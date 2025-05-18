// Written by Thomas Eizinger <thomas@coblox.tech>
// SPDX-License-Identifier: CC0-1.0

//! Example: Create an HTLC with miniscript using the policy compiler

use std::str::FromStr;

use miniscript::bitcoin::Network;
use miniscript::descriptor::Wsh;
use miniscript::policy::{Concrete, Liftable};

fn main() {
    // HTLC policy with 10:1 odds for happy (co-operative) case compared to uncooperative case.
    let htlc_policy = Concrete::<bitcoin::PublicKey>::from_str(&format!("or(10@and(sha256({secret_hash}),pk({redeem_identity})),1@and(older({expiry}),pk({refund_identity})))",
                                                  secret_hash = "1111111111111111111111111111111111111111111111111111111111111111",
                                                  redeem_identity = "022222222222222222222222222222222222222222222222222222222222222222",
                                                  refund_identity = "020202020202020202020202020202020202020202020202020202020202020202",
                                                  expiry = "4444"
    )).unwrap();

    let htlc_descriptor = Wsh::new(
        htlc_policy
            .compile()
            .expect("Policy compilation only fails on resource limits or mixed timelocks"),
    )
    .expect("Resource limits");

    assert_eq!(
        format!("{}", htlc_descriptor),
        "wsh(andor(pk(022222222222222222222222222222222222222222222222222222222222222222),sha256(1111111111111111111111111111111111111111111111111111111111111111),and_v(v:pkh(020202020202020202020202020202020202020202020202020202020202020202),older(4444))))#lfytrjen"
    );

    // Lift the descriptor into an abstract policy.
    assert_eq!(
        format!("{}", htlc_descriptor.lift().unwrap()),
        "or(and(pk(022222222222222222222222222222222222222222222222222222222222222222),sha256(1111111111111111111111111111111111111111111111111111111111111111)),and(pk(020202020202020202020202020202020202020202020202020202020202020202),older(4444)))"
    );

    // Get the scriptPubkey for this Wsh descriptor.
    assert_eq!(
        format!("{:x}", htlc_descriptor.script_pubkey()),
        "0020d853877af928a8d2a569c9c0ed14bd16f6a80ce9cccaf8a6150fd8f7f8867ae2"
    );

    // Encode the Wsh descriptor into a Bitcoin script.
    assert_eq!(
        format!("{:x}", htlc_descriptor.inner_script()),
        "21022222222222222222222222222222222222222222222222222222222222222222ac6476a91451814f108670aced2d77c1805ddd6634bc9d473188ad025c11b26782012088a82011111111111111111111111111111111111111111111111111111111111111118768"
    );

    // Get the address for this Wsh descriptor.
    assert_eq!(
        format!("{}", htlc_descriptor.address(Network::Bitcoin)),
        "bc1qmpfcw7he9z5d9ftfe8qw699azmm2sr8fen903fs4plv007yx0t3qxfmqv5"
    );
}
