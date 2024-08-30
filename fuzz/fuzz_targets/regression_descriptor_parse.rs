use core::str::FromStr;

use honggfuzz::fuzz;
use miniscript::{Descriptor, DescriptorPublicKey};
use old_miniscript::{Descriptor as OldDescriptor, DescriptorPublicKey as OldDescriptorPublicKey};

type Desc = Descriptor<DescriptorPublicKey>;
type OldDesc = OldDescriptor<OldDescriptorPublicKey>;

fn do_test(data: &[u8]) {
    let data_str = String::from_utf8_lossy(data);
    match (Desc::from_str(&data_str), OldDesc::from_str(&data_str)) {
        (Err(_), Err(_)) => {}
        (Ok(x), Err(e)) => panic!("new logic parses {} as {:?}, old fails with {}", data_str, x, e),
        (Err(e), Ok(x)) => panic!("old logic parses {} as {:?}, new fails with {}", data_str, x, e),
        (Ok(new), Ok(old)) => {
            assert_eq!(
                old.to_string(),
                new.to_string(),
                "input {} (left is old, right is new)",
                data_str
            )
        }
    }
}

fn main() {
    loop {
        fuzz!(|data| {
            do_test(data);
        });
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn duplicate_crash() {
        crate::do_test(
            b"tr(02dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd,{1,unun:0})",
        )
    }
}
