#![allow(unexpected_cfgs)]

use honggfuzz::fuzz;
use miniscript::bitcoin::secp256k1;
use miniscript::Descriptor;

fn do_test(data: &[u8]) {
    let data_str = String::from_utf8_lossy(data);
    let secp = &secp256k1::Secp256k1::signing_only();

    if let Ok((desc, _)) = Descriptor::parse_descriptor(secp, &data_str) {
        let _output = desc.to_string();
    }
}

fn main() {
    loop {
        fuzz!(|data| {
            do_test(data);
        });
    }
}
