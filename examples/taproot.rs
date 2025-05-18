// SPDX-License-Identifier: CC0-1.0

use std::collections::HashMap;
use std::str::FromStr;

use miniscript::bitcoin::key::{Keypair, XOnlyPublicKey};
use miniscript::bitcoin::secp256k1::rand;
use miniscript::bitcoin::{Network, WitnessVersion};
use miniscript::descriptor::DescriptorType;
use miniscript::policy::Concrete;
use miniscript::{translate_hash_fail, Descriptor, Miniscript, Tap, Translator};

// Refer to https://github.com/sanket1729/adv_btc_workshop/blob/master/workshop.md#creating-a-taproot-descriptor
// for a detailed explanation of the policy and it's compilation

struct StrPkTranslator {
    pk_map: HashMap<String, XOnlyPublicKey>,
}

impl Translator<String> for StrPkTranslator {
    type TargetPk = XOnlyPublicKey;
    type Error = ();

    fn pk(&mut self, pk: &String) -> Result<XOnlyPublicKey, Self::Error> {
        self.pk_map.get(pk).copied().ok_or(())
    }

    // We don't need to implement these methods as we are not using them in the policy.
    // Fail if we encounter any hash fragments. See also translate_hash_clone! macro.
    translate_hash_fail!(String, XOnlyPublicKey, Self::Error);
}

fn main() {
    let pol_str = "or(
        99@thresh(2,
            pk(hA), pk(S)
        ),1@or(
            99@pk(Ca),
            1@and(pk(In), older(9))
            )
        )"
    .replace(&[' ', '\n', '\t'][..], "");

    let _ms = Miniscript::<String, Tap>::from_str("and_v(v:ripemd160(H),pk(A))").unwrap();
    let pol = Concrete::<String>::from_str(&pol_str).unwrap();
    // In case we can't find an internal key for the given policy, we set the internal key to
    // a random pubkey as specified by BIP341 (which are *unspendable* by any party :p)
    let desc = pol.compile_tr(Some("UNSPENDABLE_KEY".to_string())).unwrap();

    let expected_desc =
        Descriptor::<String>::from_str("tr(Ca,{and_v(v:pk(In),older(9)),and_v(v:pk(hA),pk(S))})")
            .unwrap();
    assert_eq!(desc, expected_desc);

    // Descriptor type and version should match respectively for taproot
    let desc_type = desc.desc_type();
    assert_eq!(desc_type, DescriptorType::Tr);
    assert_eq!(desc_type.segwit_version().unwrap(), WitnessVersion::V1);

    if let Descriptor::Tr(ref p) = desc {
        // Check if internal key is correctly inferred as Ca
        // assert_eq!(p.internal_key(), &pubkeys[2]);
        assert_eq!(p.internal_key(), "Ca");

        // Iterate through scripts
        let mut iter = p.leaves();
        let mut next = iter.next().unwrap();
        assert_eq!(
            (next.depth(), next.miniscript().as_ref()),
            (
                1u8,
                &Miniscript::<String, Tap>::from_str("and_v(vc:pk_k(In),older(9))").unwrap()
            )
        );
        next = iter.next().unwrap();
        assert_eq!(
            (next.depth(), next.miniscript().as_ref()),
            (1u8, &Miniscript::<String, Tap>::from_str("and_v(v:pk(hA),pk(S))").unwrap())
        );
        assert_eq!(iter.next(), None);
    }

    let mut pk_map = HashMap::new();

    // We require secp for generating a random XOnlyPublicKey
    let secp = secp256k1::Secp256k1::new();
    let key_pair = Keypair::new(&secp, &mut rand::thread_rng());
    // Random unspendable XOnlyPublicKey provided for compilation to Taproot Descriptor
    let (unspendable_pubkey, _parity) = XOnlyPublicKey::from_keypair(&key_pair);

    pk_map.insert("UNSPENDABLE_KEY".to_string(), unspendable_pubkey);
    let pubkeys = hardcoded_xonlypubkeys();
    pk_map.insert("hA".to_string(), pubkeys[0]);
    pk_map.insert("S".to_string(), pubkeys[1]);
    pk_map.insert("Ca".to_string(), pubkeys[2]);
    pk_map.insert("In".to_string(), pubkeys[3]);
    let mut t = StrPkTranslator { pk_map };

    let real_desc = desc.translate_pk(&mut t).unwrap();

    // Max satisfaction weight for compilation, corresponding to the script-path spend
    // `and_v(PUBKEY_1,PUBKEY_2) at tap tree depth 1, having:
    //
    //     max_witness_size = varint(control_block_size) + control_block size +
    //                        varint(script_size) + script_size + max_satisfaction_size
    //                      = 1 + 65 + 1 + 68 + 132 = 269
    let max_sat_wt = real_desc.max_weight_to_satisfy().unwrap().to_wu();
    assert_eq!(max_sat_wt, 267);

    // Compute the bitcoin address and check if it matches
    let network = Network::Bitcoin;
    let addr = real_desc.address(network).unwrap();
    let expected_addr = bitcoin::Address::from_str(
        "bc1p4l2xzq7js40965s5w0fknd287kdlmt2dljte37zsc5a34u0h9c4q85snyd",
    )
    .unwrap()
    .assume_checked();
    assert_eq!(addr, expected_addr);
}

fn hardcoded_xonlypubkeys() -> Vec<XOnlyPublicKey> {
    let serialized_keys: [[u8; 32]; 4] = [
        [
            22, 37, 41, 4, 57, 254, 191, 38, 14, 184, 200, 133, 111, 226, 145, 183, 245, 112, 100,
            42, 69, 210, 146, 60, 179, 170, 174, 247, 231, 224, 221, 52,
        ],
        [
            194, 16, 47, 19, 231, 1, 0, 143, 203, 11, 35, 148, 101, 75, 200, 15, 14, 54, 222, 208,
            31, 205, 191, 215, 80, 69, 214, 126, 10, 124, 107, 154,
        ],
        [
            202, 56, 167, 245, 51, 10, 193, 145, 213, 151, 66, 122, 208, 43, 10, 17, 17, 153, 170,
            29, 89, 133, 223, 134, 220, 212, 166, 138, 2, 152, 122, 16,
        ],
        [
            50, 23, 194, 4, 213, 55, 42, 210, 67, 101, 23, 3, 195, 228, 31, 70, 127, 79, 21, 188,
            168, 39, 134, 58, 19, 181, 3, 63, 235, 103, 155, 213,
        ],
    ];
    let mut keys: Vec<XOnlyPublicKey> = vec![];
    for key in serialized_keys {
        keys.push(XOnlyPublicKey::from_slice(&key).unwrap());
    }
    keys
}
