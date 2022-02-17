// Miniscript
// Written in 2019 by
//     Sanket Kanjular and Andrew Poelstra
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

use bitcoin;
use bitcoin::blockdata::witness::Witness;
use bitcoin::hashes::{hash160, sha256, Hash};

use super::{stack, Error, Stack};
use miniscript::context::NoChecksEcdsa;
use {Miniscript, MiniscriptKey};

/// Attempts to parse a slice as a Bitcoin public key, checking compressedness
/// if asked to, but otherwise dropping it
fn pk_from_slice(slice: &[u8], require_compressed: bool) -> Result<bitcoin::PublicKey, Error> {
    if let Ok(pk) = bitcoin::PublicKey::from_slice(slice) {
        if require_compressed && !pk.compressed {
            Err(Error::UncompressedPubkey)
        } else {
            Ok(pk)
        }
    } else {
        Err(Error::PubkeyParseError)
    }
}

fn pk_from_stackelem<'a>(
    elem: &stack::Element<'a>,
    require_compressed: bool,
) -> Result<bitcoin::PublicKey, Error> {
    let slice = if let stack::Element::Push(slice) = *elem {
        slice
    } else {
        return Err(Error::PubkeyParseError);
    };
    pk_from_slice(slice, require_compressed)
}

fn script_from_stackelem<'a>(
    elem: &stack::Element<'a>,
) -> Result<Miniscript<bitcoin::PublicKey, NoChecksEcdsa>, Error> {
    match *elem {
        stack::Element::Push(sl) => {
            Miniscript::<bitcoin::PublicKey, _>::parse_insane(&bitcoin::Script::from(sl.to_owned()))
                .map_err(Error::from)
        }
        stack::Element::Satisfied => Miniscript::from_ast(::Terminal::True).map_err(Error::from),
        stack::Element::Dissatisfied => {
            Miniscript::from_ast(::Terminal::False).map_err(Error::from)
        }
    }
}

/// Helper type to indicate the origin of the bare pubkey that the interpereter uses
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PubkeyType {
    Pk,
    Pkh,
    Wpkh,
    ShWpkh,
}

/// Helper type to indicate the origin of the bare miniscript that the interpereter uses
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ScriptType {
    Bare,
    Sh,
    Wsh,
    ShWsh,
}

/// Structure representing a script under evaluation as a Miniscript
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Inner {
    /// The script being evaluated is a simple public key check (pay-to-pk,
    /// pay-to-pkhash or pay-to-witness-pkhash)
    PublicKey(bitcoin::PublicKey, PubkeyType),
    /// The script being evaluated is an actual script
    Script(Miniscript<bitcoin::PublicKey, NoChecksEcdsa>, ScriptType),
}

// The `Script` returned by this method is always generated/cloned ... when
// rust-bitcoin is updated to use a copy-on-write internal representation we
// should revisit this and return references to the actual txdata wherever
// possible
/// Parses an `Inner` and appropriate `Stack` from completed transaction data,
/// as well as the script that should be used as a scriptCode in a sighash
pub fn from_txdata<'txin>(
    spk: &bitcoin::Script,
    script_sig: &'txin bitcoin::Script,
    witness: &'txin Witness,
) -> Result<(Inner, Stack<'txin>, bitcoin::Script), Error> {
    let mut ssig_stack: Stack = script_sig
        .instructions_minimal()
        .map(stack::Element::from_instruction)
        .collect::<Result<Vec<stack::Element>, Error>>()?
        .into();
    let mut wit_stack: Stack = witness
        .iter()
        .map(stack::Element::from)
        .collect::<Vec<stack::Element>>()
        .into();

    // ** pay to pubkey **
    if spk.is_p2pk() {
        if !wit_stack.is_empty() {
            Err(Error::NonEmptyWitness)
        } else {
            Ok((
                Inner::PublicKey(
                    pk_from_slice(&spk[1..spk.len() - 1], false)?,
                    PubkeyType::Pk,
                ),
                ssig_stack,
                spk.clone(),
            ))
        }
    // ** pay to pubkeyhash **
    } else if spk.is_p2pkh() {
        if !wit_stack.is_empty() {
            Err(Error::NonEmptyWitness)
        } else {
            match ssig_stack.pop() {
                Some(elem) => {
                    let pk = pk_from_stackelem(&elem, false)?;
                    if *spk == bitcoin::Script::new_p2pkh(&pk.to_pubkeyhash().into()) {
                        Ok((
                            Inner::PublicKey(pk, PubkeyType::Pkh),
                            ssig_stack,
                            spk.clone(),
                        ))
                    } else {
                        Err(Error::IncorrectPubkeyHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to witness pubkeyhash **
    } else if spk.is_v0_p2wpkh() {
        if !ssig_stack.is_empty() {
            Err(Error::NonEmptyScriptSig)
        } else {
            match wit_stack.pop() {
                Some(elem) => {
                    let pk = pk_from_stackelem(&elem, true)?;
                    if *spk == bitcoin::Script::new_v0_p2wpkh(&pk.to_pubkeyhash().into()) {
                        Ok((
                            Inner::PublicKey(pk, PubkeyType::Wpkh),
                            wit_stack,
                            bitcoin::Script::new_p2pkh(&pk.to_pubkeyhash().into()), // bip143, why..
                        ))
                    } else {
                        Err(Error::IncorrectWPubkeyHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to witness scripthash **
    } else if spk.is_v0_p2wsh() {
        if !ssig_stack.is_empty() {
            Err(Error::NonEmptyScriptSig)
        } else {
            match wit_stack.pop() {
                Some(elem) => {
                    let miniscript = script_from_stackelem(&elem)?;
                    let script = miniscript.encode();
                    let scripthash = sha256::Hash::hash(&script[..]);
                    if *spk == bitcoin::Script::new_v0_p2wsh(&scripthash.into()) {
                        Ok((
                            Inner::Script(miniscript, ScriptType::Wsh),
                            wit_stack,
                            script,
                        ))
                    } else {
                        Err(Error::IncorrectWScriptHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to scripthash **
    } else if spk.is_p2sh() {
        match ssig_stack.pop() {
            Some(elem) => {
                if let stack::Element::Push(slice) = elem {
                    let scripthash = hash160::Hash::hash(slice);
                    if *spk != bitcoin::Script::new_p2sh(&scripthash.into()) {
                        return Err(Error::IncorrectScriptHash);
                    }
                    // ** p2sh-wrapped wpkh **
                    if slice.len() == 22 && slice[0] == 0 && slice[1] == 20 {
                        return match wit_stack.pop() {
                            Some(elem) => {
                                if !ssig_stack.is_empty() {
                                    Err(Error::NonEmptyScriptSig)
                                } else {
                                    let pk = pk_from_stackelem(&elem, true)?;
                                    if slice
                                        == &bitcoin::Script::new_v0_p2wpkh(
                                            &pk.to_pubkeyhash().into(),
                                        )[..]
                                    {
                                        Ok((
                                            Inner::PublicKey(pk, PubkeyType::ShWpkh),
                                            wit_stack,
                                            bitcoin::Script::new_p2pkh(&pk.to_pubkeyhash().into()), // bip143, why..
                                        ))
                                    } else {
                                        Err(Error::IncorrectWScriptHash)
                                    }
                                }
                            }
                            None => Err(Error::UnexpectedStackEnd),
                        };
                    // ** p2sh-wrapped wsh **
                    } else if slice.len() == 34 && slice[0] == 0 && slice[1] == 32 {
                        return match wit_stack.pop() {
                            Some(elem) => {
                                if !ssig_stack.is_empty() {
                                    Err(Error::NonEmptyScriptSig)
                                } else {
                                    let miniscript = script_from_stackelem(&elem)?;
                                    let script = miniscript.encode();
                                    let scripthash = sha256::Hash::hash(&script[..]);
                                    if slice
                                        == &bitcoin::Script::new_v0_p2wsh(&scripthash.into())[..]
                                    {
                                        Ok((
                                            Inner::Script(miniscript, ScriptType::ShWsh),
                                            wit_stack,
                                            script,
                                        ))
                                    } else {
                                        Err(Error::IncorrectWScriptHash)
                                    }
                                }
                            }
                            None => Err(Error::UnexpectedStackEnd),
                        };
                    }
                }
                // normal p2sh
                let miniscript = script_from_stackelem(&elem)?;
                let script = miniscript.encode();
                if wit_stack.is_empty() {
                    let scripthash = hash160::Hash::hash(&script[..]);
                    if *spk == bitcoin::Script::new_p2sh(&scripthash.into()) {
                        Ok((
                            Inner::Script(miniscript, ScriptType::Sh),
                            ssig_stack,
                            script,
                        ))
                    } else {
                        Err(Error::IncorrectScriptHash)
                    }
                } else {
                    Err(Error::NonEmptyWitness)
                }
            }
            None => Err(Error::UnexpectedStackEnd),
        }
    // ** bare script **
    } else {
        if wit_stack.is_empty() {
            let miniscript = Miniscript::<bitcoin::PublicKey, _>::parse_insane(spk)?;
            Ok((
                Inner::Script(miniscript, ScriptType::Bare),
                ssig_stack,
                spk.clone(),
            ))
        } else {
            Err(Error::NonEmptyWitness)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use bitcoin::blockdata::script;
    use bitcoin::hashes::hex::FromHex;
    use bitcoin::hashes::{hash160, sha256, Hash};
    use bitcoin::{self, Script};
    use std::str::FromStr;

    struct KeyTestData {
        pk_spk: bitcoin::Script,
        pk_sig: bitcoin::Script,
        pkh_spk: bitcoin::Script,
        pkh_sig: bitcoin::Script,
        pkh_sig_justkey: bitcoin::Script,
        wpkh_spk: bitcoin::Script,
        wpkh_stack: Witness,
        wpkh_stack_justkey: Witness,
        sh_wpkh_spk: bitcoin::Script,
        sh_wpkh_sig: bitcoin::Script,
        sh_wpkh_stack: Witness,
        sh_wpkh_stack_justkey: Witness,
    }

    impl KeyTestData {
        fn from_key(key: bitcoin::PublicKey) -> KeyTestData {
            // what a funny looking signature..
            let dummy_sig = Vec::from_hex(
                "\
                302e02153b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63\
                    02153b78ce563f89a0ed9414f5aa28ad0d96d6795f9c65\
            ",
            )
            .unwrap();

            let pkhash = key.to_pubkeyhash().into();
            let wpkhash = key.to_pubkeyhash().into();
            let wpkh_spk = bitcoin::Script::new_v0_p2wpkh(&wpkhash);
            let wpkh_scripthash = hash160::Hash::hash(&wpkh_spk[..]).into();

            KeyTestData {
                pk_spk: bitcoin::Script::new_p2pk(&key),
                pkh_spk: bitcoin::Script::new_p2pkh(&pkhash),
                pk_sig: script::Builder::new().push_slice(&dummy_sig).into_script(),
                pkh_sig: script::Builder::new()
                    .push_slice(&dummy_sig)
                    .push_key(&key)
                    .into_script(),
                pkh_sig_justkey: script::Builder::new().push_key(&key).into_script(),
                wpkh_spk: wpkh_spk.clone(),
                wpkh_stack: Witness::from_vec(vec![dummy_sig.clone(), key.to_bytes()]),
                wpkh_stack_justkey: Witness::from_vec(vec![key.to_bytes()]),
                sh_wpkh_spk: bitcoin::Script::new_p2sh(&wpkh_scripthash),
                sh_wpkh_sig: script::Builder::new()
                    .push_slice(&wpkh_spk[..])
                    .into_script(),
                sh_wpkh_stack: Witness::from_vec(vec![dummy_sig, key.to_bytes()]),
                sh_wpkh_stack_justkey: Witness::from_vec(vec![key.to_bytes()]),
            }
        }
    }

    struct FixedTestData {
        pk_comp: bitcoin::PublicKey,
        pk_uncomp: bitcoin::PublicKey,
    }

    fn fixed_test_data() -> FixedTestData {
        FixedTestData {
            pk_comp: bitcoin::PublicKey::from_str(
                "\
                025edd5cc23c51e87a497ca815d5dce0f8ab52554f849ed8995de64c5f34ce7143\
            ",
            )
            .unwrap(),
            pk_uncomp: bitcoin::PublicKey::from_str(
                "\
                045edd5cc23c51e87a497ca815d5dce0f8ab52554f849ed8995de64c5f34ce7143\
                  efae9c8dbc14130661e8cec030c89ad0c13c66c0d17a2905cdc706ab7399a868\
            ",
            )
            .unwrap(),
        }
    }

    #[test]
    fn pubkey_pk() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::Script::new();
        let empty_wit = Witness::default();

        // Compressed pk, empty scriptsig
        let (inner, stack, script_code) =
            from_txdata(&comp.pk_spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, comp.pk_spk);

        // Uncompressed pk, empty scriptsig
        let (inner, stack, script_code) =
            from_txdata(&uncomp.pk_spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp, PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, uncomp.pk_spk);

        // Compressed pk, correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&comp.pk_spk, &comp.pk_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![comp.pk_sig[1..].into()]));
        assert_eq!(script_code, comp.pk_spk);

        // Uncompressed pk, correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&uncomp.pk_spk, &uncomp.pk_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp, PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![uncomp.pk_sig[1..].into()]));
        assert_eq!(script_code, uncomp.pk_spk);

        // Scriptpubkey has invalid key
        let mut spk = comp.pk_spk.to_bytes();
        spk[1] = 5;
        let spk = bitcoin::Script::from(spk);
        let err = from_txdata(&spk, &bitcoin::Script::new(), &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "could not parse pubkey");

        // Scriptpubkey has invalid script
        let mut spk = comp.pk_spk.to_bytes();
        spk[0] = 100;
        let spk = bitcoin::Script::from(spk);
        let err = from_txdata(&spk, &bitcoin::Script::new(), &empty_wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // Witness is nonempty
        let wit = Witness::from_vec(vec![vec![]]);
        let err = from_txdata(&comp.pk_spk, &comp.pk_sig, &wit).unwrap_err();
        assert_eq!(err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn pubkey_pkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let empty_wit = Witness::default();

        // pkh, empty scriptsig; this time it errors out
        let err = from_txdata(&comp.pkh_spk, &bitcoin::Script::new(), &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // pkh, wrong pubkey
        let err = from_txdata(&comp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "public key did not match scriptpubkey");

        // pkh, right pubkey, no signature
        let (inner, stack, script_code) =
            from_txdata(&comp.pkh_spk, &comp.pkh_sig_justkey, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, comp.pkh_spk);

        let (inner, stack, script_code) =
            from_txdata(&uncomp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp, PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, uncomp.pkh_spk);

        // pkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.pkh_spk, &comp.pkh_sig_justkey, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, comp.pkh_spk);

        let (inner, stack, script_code) =
            from_txdata(&uncomp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp, PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, uncomp.pkh_spk);

        // Witness is nonempty
        let wit = Witness::from_vec(vec![vec![]]);
        let err = from_txdata(&comp.pkh_spk, &comp.pkh_sig, &wit).unwrap_err();
        assert_eq!(err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn pubkey_wpkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::Script::new();

        // wpkh, empty witness; this time it errors out
        let err = from_txdata(&comp.wpkh_spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // wpkh, uncompressed pubkey
        let err =
            from_txdata(&comp.wpkh_spk, &blank_script, &uncomp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(
            err.to_string(),
            "uncompressed pubkey in non-legacy descriptor"
        );

        // wpkh, wrong pubkey
        let err =
            from_txdata(&uncomp.wpkh_spk, &blank_script, &comp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(
            err.to_string(),
            "public key did not match scriptpubkey (segwit v0)"
        );

        // wpkh, right pubkey, no signature
        let (inner, stack, script_code) =
            from_txdata(&comp.wpkh_spk, &blank_script, &comp.wpkh_stack_justkey)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Wpkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, comp.pkh_spk);

        // wpkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.wpkh_spk, &blank_script, &comp.wpkh_stack).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::Wpkh));
        assert_eq!(
            stack,
            Stack::from(vec![comp.wpkh_stack.second_to_last().unwrap().into()])
        );
        assert_eq!(script_code, comp.pkh_spk);

        // Scriptsig is nonempty
        let err = from_txdata(&comp.wpkh_spk, &comp.pk_sig, &comp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(err.to_string(), "segwit spend had nonempty scriptsig");
    }

    #[test]
    fn pubkey_sh_wpkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::Script::new();

        // sh_wpkh, missing witness or scriptsig
        let err = from_txdata(&comp.sh_wpkh_spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");
        let err =
            from_txdata(&comp.sh_wpkh_spk, &comp.sh_wpkh_sig, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");
        let err = from_txdata(&comp.sh_wpkh_spk, &blank_script, &comp.sh_wpkh_stack).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // sh_wpkh, uncompressed pubkey
        let err = from_txdata(
            &uncomp.sh_wpkh_spk,
            &uncomp.sh_wpkh_sig,
            &uncomp.sh_wpkh_stack_justkey,
        )
        .unwrap_err();
        assert_eq!(
            err.to_string(),
            "uncompressed pubkey in non-legacy descriptor"
        );

        // sh_wpkh, wrong redeem script for scriptpubkey
        let err = from_txdata(
            &uncomp.sh_wpkh_spk,
            &comp.sh_wpkh_sig,
            &comp.sh_wpkh_stack_justkey,
        )
        .unwrap_err();
        assert_eq!(err.to_string(), "redeem script did not match scriptpubkey",);

        // sh_wpkh, wrong redeem script for witness script
        let err = from_txdata(
            &uncomp.sh_wpkh_spk,
            &uncomp.sh_wpkh_sig,
            &comp.sh_wpkh_stack_justkey,
        )
        .unwrap_err();
        assert_eq!(err.to_string(), "witness script did not match scriptpubkey",);

        // sh_wpkh, right pubkey, no signature
        let (inner, stack, script_code) = from_txdata(
            &comp.sh_wpkh_spk,
            &comp.sh_wpkh_sig,
            &comp.sh_wpkh_stack_justkey,
        )
        .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::ShWpkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, comp.pkh_spk);

        // sh_wpkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.sh_wpkh_spk, &comp.sh_wpkh_sig, &comp.sh_wpkh_stack)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp, PubkeyType::ShWpkh));
        assert_eq!(
            stack,
            Stack::from(vec![comp.sh_wpkh_stack.second_to_last().unwrap().into()])
        );
        assert_eq!(script_code, comp.pkh_spk);
    }

    #[test]
    fn script_bare() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let miniscript: ::Miniscript<bitcoin::PublicKey, NoChecksEcdsa> =
            ::Miniscript::from_str_insane(&format!("hash160({})", hash)).unwrap();

        let spk = miniscript.encode();
        let blank_script = bitcoin::Script::new();
        let empty_wit = Witness::default();

        // bare script has no validity requirements beyond being a sane script
        let (inner, stack, script_code) =
            from_txdata(&spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Bare));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, spk);

        let err = from_txdata(&blank_script, &blank_script, &empty_wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // nonempty witness
        let wit = Witness::from_vec(vec![vec![]]);
        let err = from_txdata(&spk, &blank_script, &wit).unwrap_err();
        assert_eq!(&err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn script_sh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let miniscript: ::Miniscript<bitcoin::PublicKey, NoChecksEcdsa> =
            ::Miniscript::from_str_insane(&format!("hash160({})", hash)).unwrap();

        let redeem_script = miniscript.encode();
        let rs_hash = hash160::Hash::hash(&redeem_script[..]).into();

        let spk = Script::new_p2sh(&rs_hash);
        let script_sig = script::Builder::new()
            .push_slice(&redeem_script[..])
            .into_script();
        let blank_script = bitcoin::Script::new();
        let empty_wit = Witness::default();

        // sh without scriptsig
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect scriptsig
        let err = from_txdata(&spk, &spk, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "expected push in script");

        // with correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&spk, &script_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Sh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, redeem_script);

        // nonempty witness
        let wit = Witness::from_vec(vec![vec![]]);
        let err = from_txdata(&spk, &script_sig, &wit).unwrap_err();
        assert_eq!(&err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn script_wsh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let miniscript: ::Miniscript<bitcoin::PublicKey, NoChecksEcdsa> =
            ::Miniscript::from_str_insane(&format!("hash160({})", hash)).unwrap();

        let witness_script = miniscript.encode();
        let wit_hash = sha256::Hash::hash(&witness_script[..]).into();
        let wit_stack = Witness::from_vec(vec![witness_script.to_bytes()]);

        let spk = Script::new_v0_p2wsh(&wit_hash);
        let blank_script = bitcoin::Script::new();

        // wsh without witness
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect witness
        let wit = Witness::from_vec(vec![spk.to_bytes()]);
        let err = from_txdata(&spk, &blank_script, &wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // with correct witness
        let (inner, stack, script_code) =
            from_txdata(&spk, &blank_script, &wit_stack).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Wsh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, witness_script);

        // nonempty script_sig
        let script_sig = script::Builder::new()
            .push_slice(&witness_script[..])
            .into_script();
        let err = from_txdata(&spk, &script_sig, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "segwit spend had nonempty scriptsig");
    }

    #[test]
    fn script_sh_wsh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let miniscript: ::Miniscript<bitcoin::PublicKey, NoChecksEcdsa> =
            ::Miniscript::from_str_insane(&format!("hash160({})", hash)).unwrap();

        let witness_script = miniscript.encode();
        let wit_hash = sha256::Hash::hash(&witness_script[..]).into();
        let wit_stack = Witness::from_vec(vec![witness_script.to_bytes()]);

        let redeem_script = Script::new_v0_p2wsh(&wit_hash);
        let script_sig = script::Builder::new()
            .push_slice(&redeem_script[..])
            .into_script();
        let blank_script = bitcoin::Script::new();

        let rs_hash = hash160::Hash::hash(&redeem_script[..]).into();
        let spk = Script::new_p2sh(&rs_hash);

        // shwsh without witness or scriptsig
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");
        let err = from_txdata(&spk, &script_sig, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");
        let err = from_txdata(&spk, &blank_script, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect witness
        let wit = Witness::from_vec(vec![spk.to_bytes()]);
        let err = from_txdata(&spk, &script_sig, &wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // with incorrect scriptsig
        let err = from_txdata(&spk, &redeem_script, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "redeem script did not match scriptpubkey");

        // with correct witness
        let (inner, stack, script_code) =
            from_txdata(&spk, &script_sig, &wit_stack).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::ShWsh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, witness_script);
    }
}
