//! # rust-miniscript integration test
//!
//! Read Miniscripts from file and translate into miniscripts
//! which we know how to satisfy
//!

use bitcoin;
use bitcoin::hashes::hex::ToHex;
use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d, Hash};
use bitcoin::secp256k1;
use miniscript::Miniscript;
use miniscript::MiniscriptKey;
use miniscript::Segwitv0;
use miniscript::TranslatePk;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

type MsString = Miniscript<String, Segwitv0>;
type Ms = Miniscript<bitcoin::PublicKey, Segwitv0>;

#[derive(Clone, Debug)]
pub(crate) struct PubData {
    pub(crate) pks: Vec<bitcoin::PublicKey>,
    pub(crate) sha256: sha256::Hash,
    pub(crate) hash256: sha256d::Hash,
    pub(crate) ripemd160: ripemd160::Hash,
    pub(crate) hash160: hash160::Hash,
}

#[derive(Debug, Clone)]
pub(crate) struct SecretData {
    pub(crate) sks: Vec<bitcoin::secp256k1::SecretKey>,
    pub(crate) sha256_pre: [u8; 32],
    pub(crate) hash256_pre: [u8; 32],
    pub(crate) ripemd160_pre: [u8; 32],
    pub(crate) hash160_pre: [u8; 32],
}
#[derive(Debug, Clone)]
pub(crate) struct TestData {
    pub(crate) pubdata: PubData,
    pub(crate) secretdata: SecretData,
}

// Setup (sk, pk) pairs
fn setup_keys(
    n: usize,
) -> (
    Vec<bitcoin::secp256k1::SecretKey>,
    Vec<miniscript::bitcoin::PublicKey>,
) {
    let secp_sign = secp256k1::Secp256k1::signing_only();
    let mut sk = [0; 32];
    let mut sks = vec![];
    let mut pks = vec![];
    for i in 1..n + 1 {
        sk[0] = i as u8;
        sk[1] = (i >> 8) as u8;
        sk[2] = (i >> 16) as u8;

        let sk = secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key");
        let pk = miniscript::bitcoin::PublicKey {
            inner: secp256k1::PublicKey::from_secret_key(&secp_sign, &sk),
            compressed: true,
        };
        pks.push(pk);
        sks.push(sk);
    }
    (sks, pks)
}
impl TestData {
    // generate a fixed data for n keys
    pub(crate) fn new_fixed_data(n: usize) -> Self {
        let (sks, pks) = setup_keys(n);
        let sha256_pre = [0x12 as u8; 32];
        let sha256 = sha256::Hash::hash(&sha256_pre);
        let hash256_pre = [0x34 as u8; 32];
        let hash256 = sha256d::Hash::hash(&hash256_pre);
        let hash160_pre = [0x56 as u8; 32];
        let hash160 = hash160::Hash::hash(&hash160_pre);
        let ripemd160_pre = [0x78 as u8; 32];
        let ripemd160 = ripemd160::Hash::hash(&ripemd160_pre);

        let pubdata = PubData {
            pks,
            sha256,
            hash256,
            ripemd160,
            hash160,
        };
        let secretdata = SecretData {
            sks,
            sha256_pre,
            hash256_pre,
            ripemd160_pre,
            hash160_pre,
        };
        Self {
            pubdata,
            secretdata,
        }
    }
}

// parse ~30 miniscripts from file
pub(crate) fn parse_miniscripts(pubdata: &PubData) -> Vec<Ms> {
    let pks = &pubdata.pks;
    // File must exist in current path before this produces output
    let mut ms_vec = vec![];
    if let Ok(lines) = read_lines("./random_ms.txt") {
        // Consumes the iterator, returns an (Optional) String
        for line in lines {
            if let Ok(ms) = line {
                let ms = ms.replace(
                    "sha256(H)",
                    &format!("sha256({})", &pubdata.sha256.to_hex()),
                );
                let ms = ms.replace(
                    "hash256(H)",
                    &format!("hash256({})", &pubdata.hash256.into_inner().to_hex()),
                );
                let ms = ms.replace(
                    "ripemd160(H)",
                    &format!("ripemd160({})", &pubdata.ripemd160.to_hex()),
                );
                let ms = ms.replace(
                    "hash160(H)",
                    &format!("hash160({})", &pubdata.hash160.to_hex()),
                );

                let ms = MsString::from_str_insane(&ms).expect("only parsing valid minsicripts");
                let mut i = 0;
                let mut j = pks.len();
                let ms: Result<_, ()> = ms.translate_pk(
                    &mut |_c: &'_ _| {
                        i = i + 1;
                        Ok(pks[i])
                    },
                    &mut |_pkh: &'_ _| {
                        j = j - 1;
                        Ok(pks[j].to_pubkeyhash())
                    },
                );
                ms_vec.push(ms.expect("translation cannot fail"));
            }
        }
    }
    ms_vec
}

// The output is wrapped in a Result to allow matching on errors
// Returns an Iterator to the Reader of the lines of the file.
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}
