//! # rust-miniscript integration test
//!
//! Read Miniscripts from file and translate into miniscripts
//! which we know how to satisfy
//!

use std::collections::BTreeMap;
use std::{error, fmt};

use actual_rand as rand;
use bitcoin::blockdata::witness::Witness;
use bitcoin::hashes::{sha256d, Hash};
use bitcoin::key::TapTweak as _;
use bitcoin::psbt::Psbt;
use bitcoin::sighash::SighashCache;
use bitcoin::taproot::{LeafVersion, TapLeafHash};
use bitcoin::{
    absolute, psbt, secp256k1, sighash, transaction, Amount, OutPoint, Sequence, Transaction, TxIn,
    TxOut, Txid,
};
use bitcoind::{AddressType, Client};
use miniscript::bitcoin::{self, ecdsa, taproot, ScriptBuf};
use miniscript::psbt::{PsbtExt, PsbtInputExt};
use miniscript::{Descriptor, Miniscript, ScriptContext, ToPublicKey};
mod setup;

use rand::RngCore;
use setup::test_util::{self, TestData};
/// Quickly create a BTC amount.
fn btc<F: Into<f64>>(btc: F) -> Amount { Amount::from_btc(btc.into()).unwrap() }

// Find the Outpoint by spk
fn get_vout(cl: &Client, txid: Txid, value: Amount, spk: ScriptBuf) -> (OutPoint, TxOut) {
    let model = cl
        .get_transaction(txid)
        .expect("rpc call failed")
        .into_model()
        .expect("conversion to model type failed");
    let tx = model.tx;

    for (i, txout) in tx.output.into_iter().enumerate() {
        if txout.value == value && spk == txout.script_pubkey {
            return (OutPoint::new(txid, i as u32), txout);
        }
    }
    unreachable!("Only call get vout on functions which have the expected outpoint");
}

#[derive(Debug, PartialEq)]
pub enum DescError {
    /// PSBT was not able to finalize
    PsbtFinalizeError,
    /// Problem with address computation
    AddressComputationError,
    /// Error while parsing the descriptor
    DescParseError,
}

impl fmt::Display for DescError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            DescError::PsbtFinalizeError => f.write_str("PSBT was not able to finalize"),
            DescError::AddressComputationError => f.write_str("Problem with address computation"),
            DescError::DescParseError => f.write_str("Not able to parse the descriptor"),
        }
    }
}

impl error::Error for DescError {}

pub fn test_desc_satisfy(
    cl: &Client,
    testdata: &TestData,
    descriptor: &str,
) -> Result<Witness, DescError> {
    let secp = secp256k1::Secp256k1::new();
    let sks = &testdata.secretdata.sks;
    let xonly_keypairs = &testdata.secretdata.x_only_keypairs;
    let pks = &testdata.pubdata.pks;
    let x_only_pks = &testdata.pubdata.x_only_pks;
    // Generate some blocks
    let blocks = cl
        .generate_to_address(1, &cl.new_address().unwrap())
        .unwrap();
    assert_eq!(blocks.0.len(), 1);

    let definite_desc = test_util::parse_test_desc(descriptor, &testdata.pubdata)
        .map_err(|_| DescError::DescParseError)?
        .at_derivation_index(0)
        .unwrap();

    let derived_desc = definite_desc.derived_descriptor(&secp);
    let desc_address = derived_desc.address(bitcoin::Network::Regtest);
    let desc_address = desc_address.map_err(|_x| DescError::AddressComputationError)?;

    // Next send some btc to each address corresponding to the miniscript
    let txid = cl
        .send_to_address(&desc_address, btc(1))
        .expect("rpc call failed")
        .txid()
        .expect("conversion to model failed");
    // Wait for the funds to mature.
    let blocks = cl
        .generate_to_address(2, &cl.new_address().unwrap())
        .unwrap();
    assert_eq!(blocks.0.len(), 2);
    // Create a PSBT for each transaction.
    // Spend one input and spend one output for simplicity.
    let mut psbt = Psbt {
        unsigned_tx: Transaction {
            version: transaction::Version::TWO,
            lock_time: absolute::LockTime::from_time(1_603_866_330).expect("valid timestamp"), // 10/28/2020 @ 6:25am (UTC)
            input: vec![],
            output: vec![],
        },
        unknown: BTreeMap::new(),
        proprietary: BTreeMap::new(),
        xpub: BTreeMap::new(),
        version: 0,
        inputs: vec![],
        outputs: vec![],
    };
    // figure out the outpoint from the txid
    let (outpoint, witness_utxo) = get_vout(cl, txid, btc(1.0), derived_desc.script_pubkey());
    let txin = TxIn {
        previous_output: outpoint,
        // set the sequence to a non-final number for the locktime transactions to be
        // processed correctly.
        // We waited 2 blocks, keep 1 for safety
        sequence: Sequence::from_height(1),
        ..Default::default()
    };
    psbt.unsigned_tx.input.push(txin);
    // Get a new script pubkey from the node so that
    // the node wallet tracks the receiving transaction
    // and we can check it by gettransaction RPC.
    let addr = cl.new_address_with_type(AddressType::Bech32).unwrap();
    // Had to decrease 'value', so that fees can be increased
    // (Was getting insufficient fees error, for deep script trees)
    psbt.unsigned_tx
        .output
        .push(TxOut { value: Amount::from_sat(99_997_000), script_pubkey: addr.script_pubkey() });
    let mut input = psbt::Input::default();
    input
        .update_with_descriptor_unchecked(&definite_desc)
        .unwrap();
    input.witness_utxo = Some(witness_utxo.clone());
    psbt.inputs.push(input);
    psbt.outputs.push(psbt::Output::default());

    // --------------------------------------------
    // Sign the transactions with all keys
    // AKA the signer role of psbt
    // Get all the pubkeys and the corresponding secret keys

    let mut sighash_cache = SighashCache::new(&psbt.unsigned_tx);
    match derived_desc {
        Descriptor::Tr(ref tr) => {
            // Fixme: take a parameter
            let sighash_type = sighash::TapSighashType::Default;

            let internal_key_present = x_only_pks
                .iter()
                .position(|&x| x.to_public_key() == *tr.internal_key());
            let internal_keypair = internal_key_present.map(|idx| xonly_keypairs[idx]);
            let prevouts = [witness_utxo];
            let prevouts = sighash::Prevouts::All(&prevouts);

            if let Some(internal_keypair) = internal_keypair {
                // ---------------------- Tr key spend --------------------
                let internal_keypair =
                    internal_keypair.tap_tweak(&secp, tr.spend_info().merkle_root());
                let sighash_msg = sighash_cache
                    .taproot_key_spend_signature_hash(0, &prevouts, sighash_type)
                    .unwrap();
                let msg = secp256k1::Message::from_digest(sighash_msg.to_byte_array());
                let mut aux_rand = [0u8; 32];
                rand::thread_rng().fill_bytes(&mut aux_rand);
                let schnorr_sig =
                    secp.sign_schnorr_with_aux_rand(&msg, &internal_keypair.to_inner(), &aux_rand);
                psbt.inputs[0].tap_key_sig =
                    Some(taproot::Signature { signature: schnorr_sig, sighash_type });
            } else {
                // No internal key
            }
            // ------------------ script spend -------------
            let x_only_keypairs_reqd: Vec<(secp256k1::Keypair, TapLeafHash)> = tr
                .leaves()
                .flat_map(|leaf| {
                    let leaf_hash =
                        TapLeafHash::from_script(&leaf.compute_script(), LeafVersion::TapScript);
                    leaf.miniscript().iter_pk().filter_map(move |pk| {
                        let i = x_only_pks.iter().position(|&x| x.to_public_key() == pk);
                        i.map(|idx| (xonly_keypairs[idx], leaf_hash))
                    })
                })
                .collect();
            for (keypair, leaf_hash) in x_only_keypairs_reqd {
                let sighash_msg = sighash_cache
                    .taproot_script_spend_signature_hash(0, &prevouts, leaf_hash, sighash_type)
                    .unwrap();
                let msg = secp256k1::Message::from_digest(sighash_msg.to_byte_array());
                let mut aux_rand = [0u8; 32];
                rand::thread_rng().fill_bytes(&mut aux_rand);
                let signature = secp.sign_schnorr_with_aux_rand(&msg, &keypair, &aux_rand);
                let x_only_pk =
                    x_only_pks[xonly_keypairs.iter().position(|&x| x == keypair).unwrap()];
                psbt.inputs[0]
                    .tap_script_sigs
                    .insert((x_only_pk, leaf_hash), taproot::Signature { signature, sighash_type });
            }
        }
        _ => {
            // Non-tr descriptors
            // Ecdsa sigs
            let sks_reqd = match derived_desc {
                Descriptor::Bare(bare) => find_sks_ms(bare.as_inner(), testdata),
                Descriptor::Pkh(pk) => find_sk_single_key(*pk.as_inner(), testdata),
                Descriptor::Wpkh(pk) => find_sk_single_key(*pk.as_inner(), testdata),
                Descriptor::Sh(sh) => match sh.as_inner() {
                    miniscript::descriptor::ShInner::Wsh(wsh) => match wsh.as_inner() {
                        miniscript::descriptor::WshInner::SortedMulti(ref smv) => {
                            let ms = Miniscript::multi(smv.sorted_threshold());
                            find_sks_ms(&ms, testdata)
                        }
                        miniscript::descriptor::WshInner::Ms(ref ms) => find_sks_ms(ms, testdata),
                    },
                    miniscript::descriptor::ShInner::Wpkh(pk) => {
                        find_sk_single_key(*pk.as_inner(), testdata)
                    }
                    miniscript::descriptor::ShInner::SortedMulti(smv) => {
                        let ms = Miniscript::multi(smv.sorted_threshold());
                        find_sks_ms(&ms, testdata)
                    }
                    miniscript::descriptor::ShInner::Ms(ms) => find_sks_ms(ms, testdata),
                },
                Descriptor::Wsh(wsh) => match wsh.as_inner() {
                    miniscript::descriptor::WshInner::SortedMulti(ref smv) => {
                        let ms = Miniscript::from_ast(smv.sorted_node()).unwrap();
                        find_sks_ms(&ms, testdata)
                    }
                    miniscript::descriptor::WshInner::Ms(ref ms) => find_sks_ms(ms, testdata),
                },
                Descriptor::Tr(_tr) => unreachable!("Tr checked earlier"),
            };
            let msg = psbt
                .sighash_msg(0, &mut sighash_cache, None)
                .unwrap()
                .to_secp_msg();

            // Fixme: Take a parameter
            let sighash_type = sighash::EcdsaSighashType::All;

            // Finally construct the signature and add to psbt
            for sk in sks_reqd {
                let signature = secp.sign_ecdsa(&msg, &sk);
                let pk = pks[sks.iter().position(|&x| x == sk).unwrap()];
                assert!(secp.verify_ecdsa(&msg, &signature, &pk.inner).is_ok());
                psbt.inputs[0]
                    .partial_sigs
                    .insert(pk, ecdsa::Signature { signature, sighash_type });
            }
        }
    }
    // Add the hash preimages to the psbt
    psbt.inputs[0]
        .sha256_preimages
        .insert(testdata.pubdata.sha256, testdata.secretdata.sha256_pre.to_vec());
    psbt.inputs[0].hash256_preimages.insert(
        sha256d::Hash::from_byte_array(testdata.pubdata.hash256.to_byte_array()),
        testdata.secretdata.hash256_pre.to_vec(),
    );
    psbt.inputs[0]
        .hash160_preimages
        .insert(testdata.pubdata.hash160, testdata.secretdata.hash160_pre.to_vec());
    psbt.inputs[0]
        .ripemd160_preimages
        .insert(testdata.pubdata.ripemd160, testdata.secretdata.ripemd160_pre.to_vec());
    println!("Testing descriptor: {}", definite_desc);
    // Finalize the transaction using psbt
    // Let miniscript do it's magic!
    if psbt.finalize_mut(&secp).is_err() {
        return Err(DescError::PsbtFinalizeError);
    }
    let tx = psbt.extract(&secp).expect("Extraction error");

    // Send the transactions to bitcoin node for mining.
    // Regtest mode has standardness checks
    // Check whether the node accepts the transactions
    let txid = cl
        .send_raw_transaction(&tx)
        .unwrap_or_else(|_| panic!("send tx failed for desc {}", definite_desc))
        .txid()
        .expect("conversion to model failed");

    // Finally mine the blocks and await confirmations
    let _blocks = cl
        .generate_to_address(1, &cl.new_address().unwrap())
        .unwrap();
    // Get the required transactions from the node mined in the blocks.
    // Check whether the transaction is mined in blocks
    // Assert that the confirmations are > 0.
    let num_conf = cl.get_transaction(txid).unwrap().confirmations;
    assert!(num_conf > 0);
    Ok(tx.input[0].witness.clone())
}

// Find all secret corresponding to the known public keys in ms
fn find_sks_ms<Ctx: ScriptContext>(
    ms: &Miniscript<bitcoin::PublicKey, Ctx>,
    testdata: &TestData,
) -> Vec<secp256k1::SecretKey> {
    let sks = &testdata.secretdata.sks;
    let pks = &testdata.pubdata.pks;
    let sks = ms
        .iter_pk()
        .filter_map(|pk| {
            let i = pks.iter().position(|&x| x.to_public_key() == pk);
            i.map(|idx| (sks[idx]))
        })
        .collect();
    sks
}

fn find_sk_single_key(pk: bitcoin::PublicKey, testdata: &TestData) -> Vec<secp256k1::SecretKey> {
    let sks = &testdata.secretdata.sks;
    let pks = &testdata.pubdata.pks;
    let i = pks.iter().position(|&x| x.to_public_key() == pk);
    i.map(|idx| vec![sks[idx]]).unwrap_or(Vec::new())
}

fn test_descs(cl: &Client, testdata: &TestData) {
    // K : Compressed key available
    // K!: Compressed key with corresponding secret key unknown
    // X: X-only key available
    // X!: X-only key with corresponding secret key unknown

    // Test 1: Simple spend with internal key
    let wit = test_desc_satisfy(cl, testdata, "tr(X)").unwrap();
    assert!(wit.len() == 1);

    // Test 2: Same as above, but with leaves
    let wit = test_desc_satisfy(cl, testdata, "tr(X,{pk(X1!),pk(X2!)})").unwrap();
    assert!(wit.len() == 1);

    // Test 3: Force to spend with script spend. Unknown internal key and only one known script path
    // X! -> Internal key unknown
    // Leaf 1 -> pk(X1) with X1 known
    // Leaf 2-> and_v(v:pk(X2),pk(X3!)) with partial witness only to X2 known
    let wit = test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1),and_v(v:pk(X2),pk(X3!))})").unwrap();
    assert!(wit.len() == 3); // control block, script and signature

    // Test 4: Force to spend with script spend. Unknown internal key and multiple script paths
    // Should select the one with minimum weight
    // X! -> Internal key unknown
    // Leaf 1 -> pk(X1!) with X1 unknown
    // Leaf 2-> and_v(v:pk(X2),pk(X3)) X2 and X3 known
    let wit = test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1),and_v(v:pk(X2),pk(X3))})").unwrap();
    assert!(wit.len() == 3); // control block, script and one signatures

    // Test 5: When everything is available, we should select the key spend path
    let wit = test_desc_satisfy(cl, testdata, "tr(X,{pk(X1),and_v(v:pk(X2),pk(X3!))})").unwrap();
    assert!(wit.len() == 1); // control block, script and signature

    // Test 6: Test the new multi_a opcodes
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),multi_a(1,X2,X3!,X4!,X5!)})").unwrap();
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),multi_a(2,X2,X3,X4!,X5!)})").unwrap();
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),multi_a(3,X2,X3,X4,X5!)})").unwrap();
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),multi_a(4,X2,X3,X4,X5)})").unwrap();

    // Test 7: Test script tree of depth 127 is valid, only X128 is known
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),{pk(X2!),{pk(X3!),{pk(X4!),{pk(X5!),{pk(X6!),{pk(X7!),{pk(X8!),{pk(X9!),{pk(X10!),{pk(X11!),{pk(X12!),{pk(X13!),{pk(X14!),{pk(X15!),{pk(X16!),{pk(X17!),{pk(X18!),{pk(X19!),{pk(X20!),{pk(X21!),{pk(X22!),{pk(X23!),{pk(X24!),{pk(X25!),{pk(X26!),{pk(X27!),{pk(X28!),{pk(X29!),{pk(X30!),{pk(X31!),{pk(X32!),{pk(X33!),{pk(X34!),{pk(X35!),{pk(X36!),{pk(X37!),{pk(X38!),{pk(X39!),{pk(X40!),{pk(X41!),{pk(X42!),{pk(X43!),{pk(X44!),{pk(X45!),{pk(X46!),{pk(X47!),{pk(X48!),{pk(X49!),{pk(X50!),{pk(X51!),{pk(X52!),{pk(X53!),{pk(X54!),{pk(X55!),{pk(X56!),{pk(X57!),{pk(X58!),{pk(X59!),{pk(X60!),{pk(X61!),{pk(X62!),{pk(X63!),{pk(X64!),{pk(X65!),{pk(X66!),{pk(X67!),{pk(X68!),{pk(X69!),{pk(X70!),{pk(X71!),{pk(X72!),{pk(X73!),{pk(X74!),{pk(X75!),{pk(X76!),{pk(X77!),{pk(X78!),{pk(X79!),{pk(X80!),{pk(X81!),{pk(X82!),{pk(X83!),{pk(X84!),{pk(X85!),{pk(X86!),{pk(X87!),{pk(X88!),{pk(X89!),{pk(X90!),{pk(X91!),{pk(X92!),{pk(X93!),{pk(X94!),{pk(X95!),{pk(X96!),{pk(X97!),{pk(X98!),{pk(X99!),{pk(X100!),{pk(X101!),{pk(X102!),{pk(X103!),{pk(X104!),{pk(X105!),{pk(X106!),{pk(X107!),{pk(X108!),{pk(X109!),{pk(X110!),{pk(X111!),{pk(X112!),{pk(X113!),{pk(X114!),{pk(X115!),{pk(X116!),{pk(X117!),{pk(X118!),{pk(X119!),{pk(X120!),{pk(X121!),{pk(X122!),{pk(X123!),{pk(X124!),{pk(X125!),{pk(X126!),{pk(X127!),pk(X128)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})").unwrap();

    // Test 8: Test script tree of depth 128 is valid, only X129 is known
    test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),{pk(X2!),{pk(X3!),{pk(X4!),{pk(X5!),{pk(X6!),{pk(X7!),{pk(X8!),{pk(X9!),{pk(X10!),{pk(X11!),{pk(X12!),{pk(X13!),{pk(X14!),{pk(X15!),{pk(X16!),{pk(X17!),{pk(X18!),{pk(X19!),{pk(X20!),{pk(X21!),{pk(X22!),{pk(X23!),{pk(X24!),{pk(X25!),{pk(X26!),{pk(X27!),{pk(X28!),{pk(X29!),{pk(X30!),{pk(X31!),{pk(X32!),{pk(X33!),{pk(X34!),{pk(X35!),{pk(X36!),{pk(X37!),{pk(X38!),{pk(X39!),{pk(X40!),{pk(X41!),{pk(X42!),{pk(X43!),{pk(X44!),{pk(X45!),{pk(X46!),{pk(X47!),{pk(X48!),{pk(X49!),{pk(X50!),{pk(X51!),{pk(X52!),{pk(X53!),{pk(X54!),{pk(X55!),{pk(X56!),{pk(X57!),{pk(X58!),{pk(X59!),{pk(X60!),{pk(X61!),{pk(X62!),{pk(X63!),{pk(X64!),{pk(X65!),{pk(X66!),{pk(X67!),{pk(X68!),{pk(X69!),{pk(X70!),{pk(X71!),{pk(X72!),{pk(X73!),{pk(X74!),{pk(X75!),{pk(X76!),{pk(X77!),{pk(X78!),{pk(X79!),{pk(X80!),{pk(X81!),{pk(X82!),{pk(X83!),{pk(X84!),{pk(X85!),{pk(X86!),{pk(X87!),{pk(X88!),{pk(X89!),{pk(X90!),{pk(X91!),{pk(X92!),{pk(X93!),{pk(X94!),{pk(X95!),{pk(X96!),{pk(X97!),{pk(X98!),{pk(X99!),{pk(X100!),{pk(X101!),{pk(X102!),{pk(X103!),{pk(X104!),{pk(X105!),{pk(X106!),{pk(X107!),{pk(X108!),{pk(X109!),{pk(X110!),{pk(X111!),{pk(X112!),{pk(X113!),{pk(X114!),{pk(X115!),{pk(X116!),{pk(X117!),{pk(X118!),{pk(X119!),{pk(X120!),{pk(X121!),{pk(X122!),{pk(X123!),{pk(X124!),{pk(X125!),{pk(X126!),{pk(X127!),{pk(X128!),pk(X129)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})").unwrap();

    // Test 9: Test script complete tree having 128 leaves with depth log(128), only X1 is known
    test_desc_satisfy(cl, testdata, "tr(X!,{{{{{{{pk(X1),pk(X2!)},{pk(X3!),pk(X4!)}},{{pk(X5!),pk(X6!)},{pk(X7!),pk(X8!)}}},{{{pk(X9!),pk(X10!)},{pk(X11!),pk(X12!)}},{{pk(X13!),pk(X14!)},{pk(X15!),pk(X16!)}}}},{{{{pk(X17!),pk(X18!)},{pk(X19!),pk(X20!)}},{{pk(X21!),pk(X22!)},{pk(X23!),pk(X24!)}}},{{{pk(X25!),pk(X26!)},{pk(X27!),pk(X28!)}},{{pk(X29!),pk(X30!)},{pk(X31!),pk(X32!)}}}}},{{{{{pk(X33!),pk(X34!)},{pk(X35!),pk(X36!)}},{{pk(X37!),pk(X38!)},{pk(X39!),pk(X40!)}}},{{{pk(X41!),pk(X42!)},{pk(X43!),pk(X44!)}},{{pk(X45!),pk(X46!)},{pk(X47!),pk(X48!)}}}},{{{{pk(X49!),pk(X50!)},{pk(X51!),pk(X52!)}},{{pk(X53!),pk(X54!)},{pk(X55!),pk(X56!)}}},{{{pk(X57!),pk(X58!)},{pk(X59!),pk(X60!)}},{{pk(X61!),pk(X62!)},{pk(X63!),pk(X64!)}}}}}},{{{{{{pk(X65!),pk(X66!)},{pk(X67!),pk(X68!)}},{{pk(X69!),pk(X70!)},{pk(X71!),pk(X72!)}}},{{{pk(X73!),pk(X74!)},{pk(X75!),pk(X76!)}},{{pk(X77!),pk(X78!)},{pk(X79!),pk(X80!)}}}},{{{{pk(X81!),pk(X82!)},{pk(X83!),pk(X84!)}},{{pk(X85!),pk(X86!)},{pk(X87!),pk(X88!)}}},{{{pk(X89!),pk(X90!)},{pk(X91!),pk(X92!)}},{{pk(X93!),pk(X94!)},{pk(X95!),pk(X96!)}}}}},{{{{{pk(X97!),pk(X98!)},{pk(X99!),pk(X100!)}},{{pk(X101!),pk(X102!)},{pk(X103!),pk(X104!)}}},{{{pk(X105!),pk(X106!)},{pk(X107!),pk(X108!)}},{{pk(X109!),pk(X110!)},{pk(X111!),pk(X112!)}}}},{{{{pk(X113!),pk(X114!)},{pk(X115!),pk(X116!)}},{{pk(X117!),pk(X118!)},{pk(X119!),pk(X120!)}}},{{{pk(X121!),pk(X122!)},{pk(X123!),pk(X124!)}},{{pk(X125!),pk(X126!)},{pk(X127!),pk(X128!)}}}}}}})").unwrap();

    // Test 10: Test taproot desc with ZERO known keys
    let result = test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),pk(X2!)})");
    assert_eq!(result, Err(DescError::PsbtFinalizeError));

    // Test 10: Test taproot desc with ZERO known keys
    let result = test_desc_satisfy(cl, testdata, "tr(X!,j:multi_a(3,X1!,X2,X3,X4))");
    assert_eq!(result, Err(DescError::DescParseError));

    // Test 11: Test taproot with insufficient known keys
    let result = test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),multi_a(3,X2!,X3,X4)})");
    assert_eq!(result, Err(DescError::PsbtFinalizeError));

    // Test 12: size exceeds the limit
    let result = test_desc_satisfy(cl, testdata, "wsh(thresh(1,pk(K1),a:pk(K2),a:pk(K3),a:pk(K4),a:pk(K5),a:pk(K6),a:pk(K7),a:pk(K8),a:pk(K9),a:pk(K10),a:pk(K11),a:pk(K12),a:pk(K13),a:pk(K14),a:pk(K15),a:pk(K16),a:pk(K17),a:pk(K18),a:pk(K19),a:pk(K20),a:pk(K21),a:pk(K22),a:pk(K23),a:pk(K24),a:pk(K25),a:pk(K26),a:pk(K27),a:pk(K28),a:pk(K29),a:pk(K30),a:pk(K31),a:pk(K32),a:pk(K33),a:pk(K34),a:pk(K35),a:pk(K36),a:pk(K37),a:pk(K38),a:pk(K39),a:pk(K40),a:pk(K41),a:pk(K42),a:pk(K43),a:pk(K44),a:pk(K45),a:pk(K46),a:pk(K47),a:pk(K48),a:pk(K49),a:pk(K50),a:pk(K51),a:pk(K52),a:pk(K53),a:pk(K54),a:pk(K55),a:pk(K56),a:pk(K57),a:pk(K58),a:pk(K59),a:pk(K60),a:pk(K61),a:pk(K62),a:pk(K63),a:pk(K64),a:pk(K65),a:pk(K66),a:pk(K67),a:pk(K68),a:pk(K69),a:pk(K70),a:pk(K71),a:pk(K72),a:pk(K73),a:pk(K74),a:pk(K75),a:pk(K76),a:pk(K77),a:pk(K78),a:pk(K79),a:pk(K80),a:pk(K81),a:pk(K82),a:pk(K83),a:pk(K84),a:pk(K85),a:pk(K86),a:pk(K87),a:pk(K88),a:pk(K89),a:pk(K90),a:pk(K91),a:pk(K92),a:pk(K93),a:pk(K94),a:pk(K95),a:pk(K96),a:pk(K97),a:pk(K98),a:pk(K99),a:pk(K100)))");
    assert_eq!(result, Err(DescError::DescParseError));

    // Test 13: Test script tree of depth > 128 is invalid
    let result = test_desc_satisfy(cl, testdata, "tr(X!,{pk(X1!),{pk(X2!),{pk(X3!),{pk(X4!),{pk(X5!),{pk(X6!),{pk(X7!),{pk(X8!),{pk(X9!),{pk(X10!),{pk(X11!),{pk(X12!),{pk(X13!),{pk(X14!),{pk(X15!),{pk(X16!),{pk(X17!),{pk(X18!),{pk(X19!),{pk(X20!),{pk(X21!),{pk(X22!),{pk(X23!),{pk(X24!),{pk(X25!),{pk(X26!),{pk(X27!),{pk(X28!),{pk(X29!),{pk(X30!),{pk(X31!),{pk(X32!),{pk(X33!),{pk(X34!),{pk(X35!),{pk(X36!),{pk(X37!),{pk(X38!),{pk(X39!),{pk(X40!),{pk(X41!),{pk(X42!),{pk(X43!),{pk(X44!),{pk(X45!),{pk(X46!),{pk(X47!),{pk(X48!),{pk(X49!),{pk(X50!),{pk(X51!),{pk(X52!),{pk(X53!),{pk(X54!),{pk(X55!),{pk(X56!),{pk(X57!),{pk(X58!),{pk(X59!),{pk(X60!),{pk(X61!),{pk(X62!),{pk(X63!),{pk(X64!),{pk(X65!),{pk(X66!),{pk(X67!),{pk(X68!),{pk(X69!),{pk(X70!),{pk(X71!),{pk(X72!),{pk(X73!),{pk(X74!),{pk(X75!),{pk(X76!),{pk(X77!),{pk(X78!),{pk(X79!),{pk(X80!),{pk(X81!),{pk(X82!),{pk(X83!),{pk(X84!),{pk(X85!),{pk(X86!),{pk(X87!),{pk(X88!),{pk(X89!),{pk(X90!),{pk(X91!),{pk(X92!),{pk(X93!),{pk(X94!),{pk(X95!),{pk(X96!),{pk(X97!),{pk(X98!),{pk(X99!),{pk(X100!),{pk(X101!),{pk(X102!),{pk(X103!),{pk(X104!),{pk(X105!),{pk(X106!),{pk(X107!),{pk(X108!),{pk(X109!),{pk(X110!),{pk(X111!),{pk(X112!),{pk(X113!),{pk(X114!),{pk(X115!),{pk(X116!),{pk(X117!),{pk(X118!),{pk(X119!),{pk(X120!),{pk(X121!),{pk(X122!),{pk(X123!),{pk(X124!),{pk(X125!),{pk(X126!),{pk(X127!),{pk(X128!),{pk(X129!),pk(X130)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})");
    assert_eq!(result, Err(DescError::DescParseError));

    // Misc tests for other descriptors that we support
    // Keys
    test_desc_satisfy(cl, testdata, "wpkh(K)").unwrap();
    test_desc_satisfy(cl, testdata, "pkh(K)").unwrap();
    test_desc_satisfy(cl, testdata, "sh(wpkh(K))").unwrap();

    // sorted multi
    test_desc_satisfy(cl, testdata, "sh(sortedmulti(2,K1,K2,K3))").unwrap();
    test_desc_satisfy(cl, testdata, "wsh(sortedmulti(2,K1,K2,K3))").unwrap();
    test_desc_satisfy(cl, testdata, "sh(wsh(sortedmulti(2,K1,K2,K3)))").unwrap();

    // Miniscripts
    test_desc_satisfy(cl, testdata, "sh(and_v(v:pk(K1),pk(K2)))").unwrap();
    test_desc_satisfy(cl, testdata, "wsh(and_v(v:pk(K1),pk(K2)))").unwrap();
    test_desc_satisfy(cl, testdata, "sh(wsh(and_v(v:pk(K1),pk(K2))))").unwrap();
}

#[test]
fn test_satisfy() {
    let testdata = TestData::new_fixed_data(50);
    let cl = &setup::setup().client;
    test_descs(cl, &testdata);
}
