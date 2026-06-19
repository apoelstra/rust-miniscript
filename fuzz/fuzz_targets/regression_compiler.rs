use std::sync::Arc;

use honggfuzz::fuzz;
use miniscript::{policy, AbsLockTime, RelLockTime, Threshold};
use old_miniscript::policy as old_policy;

type Policy = policy::Concrete<String>;
type OldPolicy = old_policy::Concrete<String>;

fn do_test(data: &[u8]) {
    let mut stack = vec![];
    for sl in data.chunks_exact(2) {
        let byte = sl[0];
        let extra = sl[1];
        let ext32 = u32::from(extra);
        match byte & 15 {
            0 => stack.push(Policy::Unsatisfiable),
            1 => stack.push(Policy::Trivial),
            2 => stack.push(Policy::Key(format!("key_{:02x}", extra))),
            3 => stack.push(Policy::After(AbsLockTime::from_consensus(1 + ext32).unwrap())),
            4 => stack.push(Policy::Older(RelLockTime::from_consensus(1 + ext32).unwrap())),
            5 => stack.push(Policy::Sha256(format!("hash_{:02x}", extra))),
            6 => {
                let (r, l) = match (stack.pop(), stack.pop()) {
                    (Some(r), Some(l)) => (r, l),
                    _ => return,
                };
                stack.push(Policy::And(vec![l.into(), r.into()]));
            }
            7 => {
                let (r, l) = match (stack.pop(), stack.pop()) {
                    (Some(r), Some(l)) => (r, l),
                    _ => return,
                };

                let l_weight = match ext32.try_into() {
                    Ok(l_weight) => l_weight,
                    _ => return,
                };
                let r_weight = match (ext32 >> 4).try_into() {
                    Ok(r_weight) => r_weight,
                    _ => return,
                };

                stack.push(Policy::Or(vec![(l_weight, l.into()), (r_weight, r.into())]));
            }
            8 => {
                let n = 1 + (extra >> 4);
                let k = 1 + (extra % n);
                let inner = match (0..n)
                    .map(|_| stack.pop().map(Arc::new))
                    .collect::<Option<Vec<_>>>()
                {
                    Some(inner) => inner,
                    None => return,
                };
                let thresh = Threshold::new(k.into(), inner).unwrap();
                stack.push(Policy::Thresh(thresh))
            }
            _ => return,
        }
        if stack.len() > 128 {
            return;
        };
    }
    let new = match stack.pop() {
        Some(new) => new,
        None => return,
    };
    let new_str = new.to_string();
    let old = match new_str.parse::<OldPolicy>() {
        Ok(old) => old,
        Err(e) => panic!("new policy {} fails with {}", new_str, e),
    };

    assert_eq!(old.to_string(), new_str, "(left is old, right is new)",);

    let comp = new.compile::<miniscript::Legacy>();
    let old_comp = old.compile::<old_miniscript::Legacy>();

    match (comp, old_comp) {
        (Err(_), Err(_)) => {}
        (Ok(x), Err(e)) => {
            panic!("new logic compiles {} as {:?}, old fails with {}", new, x, e)
        }
        (Err(e), Ok(x)) => {
            panic!("old logic compiles {} as {:?}, new fails with {}", new, x, e)
        }
        (Ok(new), Ok(old)) => {
            assert_eq!(
                old.to_string(),
                new.to_string(),
                "compiling the policy {} (left is old, right is new)",
                new_str
            );
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
        let v = miniscript::hex::decode_to_vec("0000000000000014000000280100000000010000000000000400000010011100000000000000000000000200000000000115000000000000002d3530303933910100000f0000000000000004010035000072000011007228354077727336667472697669620806727233374903").unwrap();
        crate::do_test(&v);
    }
}
