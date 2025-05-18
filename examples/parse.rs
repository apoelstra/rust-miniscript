// SPDX-License-Identifier: CC0-1.0

//! Example: Parsing a descriptor from a string.

use std::str::FromStr;

use miniscript::descriptor::DescriptorType;
use miniscript::Descriptor;

fn main() {
    let desc = miniscript::Descriptor::<bitcoin::PublicKey>::from_str(
        "wsh(c:pk_k(020202020202020202020202020202020202020202020202020202020202020202))",
    )
    .unwrap();

    // Compute the script pubkey. As mentioned in the documentation, script_pubkey only fails
    // for Tr descriptors that don't have some pre-computed data.
    assert_eq!(
        format!("{:x}", desc.script_pubkey()),
        "0020daef16dd7c946a3e735a6e43310cb2ce33dfd14a04f76bf8241a16654cb2f0f9"
    );

    // As another way to compute script pubkey; we can also compute the type of the descriptor.
    let desc_type = desc.desc_type();
    assert_eq!(desc_type, DescriptorType::Wsh);
    // Since we know the type of descriptor, we can get the Wsh struct from Descriptor. This allows
    // us to call infallible methods for getting script pubkey.
    if let Descriptor::Wsh(wsh) = &desc {
        assert_eq!(
            format!("{:x}", wsh.script_pubkey()),
            "0020daef16dd7c946a3e735a6e43310cb2ce33dfd14a04f76bf8241a16654cb2f0f9"
        );
    }

    // Get the inner script inside the descriptor.
    assert_eq!(
        format!(
            "{:x}",
            desc.explicit_script()
                .expect("Wsh descriptors have inner scripts")
        ),
        "21020202020202020202020202020202020202020202020202020202020202020202ac"
    );

    // In a similar fashion we can parse a wrapped segwit script.
    let desc = miniscript::Descriptor::<bitcoin::PublicKey>::from_str(
        "sh(wsh(c:pk_k(020202020202020202020202020202020202020202020202020202020202020202)))",
    )
    .unwrap();
    assert!(desc.desc_type() == DescriptorType::ShWsh);
}
