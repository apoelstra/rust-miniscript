// SPDX-License-Identifier: CC0-1.0

//! String encoding of concrete policies.

use core::{fmt, str};

use crate::sync::Arc;

use super::{Inner, Policy2};
use crate::iter::TreeLike as _;
use crate::{FromStrKey, MiniscriptKey, ParseError};

impl<Pk: MiniscriptKey> Policy2<Pk> {
    fn conditional_fmt(&self, f: &mut fmt::Formatter, is_display: bool) -> fmt::Result {
        for item in (1.0, self).verbose_pre_order_iter() {
            let (prob, node) = item.node;

            if item.n_children_yielded == 0 {
                if let Some(ref parent) = item.parent {
                    if matches!(parent.1.inner, Inner::Or(..)) {
                        write!(f, "{}@", prob)?;
                    }
                }
                f.write_str(node.inner.fragment_name())?;
                if item.is_complete {
                    match (is_display, &node.inner) {
                        (false, Inner::Key(ref pk)) => write!(f, "({:?}", pk)?,
                        (true, Inner::Key(ref pk)) => write!(f, "({}", pk)?,
                        (_, Inner::After(n)) => write!(f, "({})", n)?,
                        (_, Inner::Older(n)) => write!(f, "({})", n)?,
                        (false, Inner::Sha256(ref h)) => write!(f, "({:?})", h)?,
                        (true, Inner::Sha256(ref h)) => write!(f, "({})", h)?,
                        (false, Inner::Hash256(ref h)) => write!(f, "({:?})", h)?,
                        (true, Inner::Hash256(ref h)) => write!(f, "({})", h)?,
                        (false, Inner::Ripemd160(ref h)) => write!(f, "({:?})", h)?,
                        (true, Inner::Ripemd160(ref h)) => write!(f, "({})", h)?,
                        (false, Inner::Hash160(ref h)) => write!(f, "({:?})", h)?,
                        (true, Inner::Hash160(ref h)) => write!(f, "({})", h)?,
                        _ => {}
                    }
                } else {
                    f.write_str("(")?;
                }
            } else if !item.is_complete {
                f.write_str(",")?;
            } else {
                f.write_str("(")?;
            }
        }
        Ok(())
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Policy2<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.conditional_fmt(f, false) }
}

impl<Pk: MiniscriptKey> fmt::Display for Policy2<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.conditional_fmt(f, true) }
}

impl<Pk: FromStrKey> str::FromStr for Policy2<Pk> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tree = crate::expression::Tree::from_str(s)?;

        // TODO you really need parent pointers in the tree here.

        let mut stack = vec![];
        for item in tree.post_order_iter() {
            if item.node.args.is_empty() {
                // Terminals
                // to be until we've seen their parents. ("0" and "1" are the only exceptions,
                // since these are nodes unto themselves.)
                match item.node.name {
                    "UNSATISFIABLE" => stack.push(Self::unsatisfiable()),
                    "TRIVIAL" => stack.push(Self::trivial()),
                    _ => {},
                }
                continue;
            }

            // From here we know we have at least one child.
            match item.node.name {
                "pk" => 
            }

        }
        Ok(())
    }
}
