// SPDX-License-Identifier: CC0-1.0
//! This is not an example and will surely panic if executed, the purpose of this is using the
//! compiled binary with tools like `cargo bloat` that cannot work with libraries.
//!
//! Ideal properties:
//!
//! * Call all the library API surface.
//! * Depend on user input so that functions are not stripped out on the base of static input.
//! * Use results so that calls are not stripped out.
//!

use std::collections::HashMap;
use std::str::FromStr;

use bitcoin::{ecdsa, XOnlyPublicKey};
use miniscript::descriptor::Wsh;
use miniscript::policy::{Concrete, Liftable};
use miniscript::psbt::PsbtExt;
use miniscript::{
    translate_hash_fail, DefiniteDescriptorKey, Descriptor, DescriptorPublicKey, MiniscriptKey,
    Translator,
};
use secp256k1::Secp256k1;
fn main() {
    let empty = "".to_string();
    let mut args = std::env::args().collect::<Vec<_>>();
    let i = args.pop().unwrap_or(empty);

    let d = Descriptor::<DescriptorPublicKey>::from_str(&i).unwrap();
    use_descriptor(d.clone());
    use_descriptor(Descriptor::<DefiniteDescriptorKey>::from_str(&i).unwrap());
    use_descriptor(Descriptor::<bitcoin::PublicKey>::from_str(&i).unwrap());
    use_descriptor(Descriptor::<String>::from_str(&i).unwrap());

    let a = d
        .at_derivation_index(0)
        .unwrap()
        .address(bitcoin::Network::Bitcoin)
        .unwrap();
    println!("{}", a);

    let secp = Secp256k1::new();
    let (d, m) = Descriptor::parse_descriptor(&secp, &i).unwrap();
    use_descriptor(d);
    println!("{:?}", m);

    let p = Concrete::<bitcoin::PublicKey>::from_str(&i).unwrap();
    let h = Wsh::new(p.compile().unwrap()).unwrap();
    println!("{}", h);
    println!("{:?}", h.lift());
    println!("{:?}", h.script_pubkey());
    println!("{:?}", h.address(bitcoin::Network::Bitcoin));

    let psbt: bitcoin::Psbt = i.parse().unwrap();
    let psbt = psbt.finalize(&secp).unwrap();
    let mut tx = psbt.extract_tx().unwrap();
    println!("{:?}", tx);

    let d = miniscript::Descriptor::<bitcoin::PublicKey>::from_str(&i).unwrap();
    let sigs = HashMap::<bitcoin::PublicKey, ecdsa::Signature>::new();
    d.satisfy(&mut tx.input[0], &sigs).unwrap();

    let pol = Concrete::<String>::from_str(&i).unwrap();
    let desc = pol.compile_tr(Some("UNSPENDABLE_KEY".to_string())).unwrap();
    println!("{}", desc);
    let pk_map = HashMap::new();
    let mut t = StrPkTranslator { pk_map };
    let real_desc = desc.translate_pk(&mut t).unwrap();
    println!("{}", real_desc);
    let addr = real_desc.address(bitcoin::Network::Bitcoin).unwrap();
    println!("{}", addr);
}

fn use_descriptor<K: MiniscriptKey>(d: Descriptor<K>) {
    println!("{}", d);
    println!("{:?}", d);
    println!("{:?}", d.desc_type());
}

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
