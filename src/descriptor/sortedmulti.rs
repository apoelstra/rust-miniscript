// Miniscript
// Written in 2020 by rust-miniscript developers
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

//! # Sorted Multi
//!
//! Implementation of sorted multi primitive for descriptors
//!

use std::{fmt, marker::PhantomData, str::FromStr};

use bitcoin::blockdata::script;

use expression;
use miniscript::{
    self, context::ScriptContext, decode::Terminal, limits::MAX_PUBKEYS_PER_MULTISIG,
};
use policy;
use script_num_size;
use {errstr, Error, ForEach, ForEachKey, Miniscript, MiniscriptKey, Satisfier, ToPublicKey};

/// Contents of a "sortedmulti" descriptor
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortedMultiVec<Pk: MiniscriptKey, Ctx: ScriptContext> {
    /// signatures required
    pub k: usize,
    /// public keys inside sorted Multi
    pub pks: Vec<Pk>,
    /// The current ScriptContext for sortedmulti
    pub(crate) phantom: PhantomData<Ctx>,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    /// Create a new instance of `SortedMultiVec` given a list of keys and the threshold
    ///
    /// Internally checks all the applicable size limits and pubkey types limitations according to the current `Ctx`.
    pub fn new(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        // A sortedmulti() is only defined for <= 20 keys (it maps to CHECKMULTISIG)
        if pks.len() > MAX_PUBKEYS_PER_MULTISIG {
            Error::BadDescriptor("Too many public keys".to_string());
        }

        // Check the limits before creating a new SortedMultiVec
        // For example, under p2sh context the scriptlen can only be
        // upto 520 bytes.
        let term: miniscript::decode::Terminal<Pk, Ctx> = Terminal::Multi(k, pks.clone());
        let ms = Miniscript::from_ast(term)?;

        // This would check all the consensus rules for p2sh/p2wsh and
        // even tapscript in future
        Ctx::check_local_validity(&ms)?;

        Ok(Self {
            k,
            pks,
            phantom: PhantomData,
        })
    }
    /// Parse an expression tree into a SortedMultiVec
    pub fn from_tree(tree: &expression::Tree) -> Result<Self, Error>
    where
        Pk: FromStr,
        <Pk as FromStr>::Err: ToString,
    {
        if tree.args.is_empty() {
            return Err(errstr("no arguments given for sortedmulti"));
        }
        let k = expression::parse_num(tree.args[0].name)?;
        if k > (tree.args.len() - 1) as u32 {
            return Err(errstr(
                "higher threshold than there were keys in sortedmulti",
            ));
        }
        let pks: Result<Vec<Pk>, _> = tree.args[1..]
            .iter()
            .map(|sub| expression::terminal(sub, Pk::from_str))
            .collect();

        pks.map(|pks| SortedMultiVec::new(k as usize, pks))?
    }

    /// This will panic if translatefpk returns an uncompressed key when
    /// converting to a Segwit descriptor. To prevent this panic, ensure
    /// translatefpk returns an error in this case instead.
    pub fn translate_pk<FPk, Q, FuncError>(
        &self,
        translatefpk: &mut FPk,
    ) -> Result<SortedMultiVec<Q, Ctx>, FuncError>
    where
        FPk: FnMut(&Pk) -> Result<Q, FuncError>,
        Q: MiniscriptKey,
    {
        let pks: Result<Vec<Q>, _> = self.pks.iter().map(&mut *translatefpk).collect();
        Ok(SortedMultiVec {
            k: self.k,
            pks: pks?,
            phantom: PhantomData,
        })
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> ForEachKey<Pk> for SortedMultiVec<Pk, Ctx> {
    fn for_each_key<'a, F: FnMut(ForEach<'a, Pk>) -> bool>(&'a self, mut pred: F) -> bool
    where
        Pk: 'a,
        Pk::Hash: 'a,
    {
        self.pks.iter().all(|key| pred(ForEach::Key(key)))
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    /// utility function to sanity a sorted multi vec
    pub fn sanity_check(&self) -> Result<(), Error> {
        let ms: Miniscript<Pk, Ctx> =
            Miniscript::from_ast(Terminal::Multi(self.k, self.pks.clone()))
                .expect("Must typecheck");
        // '?' for doing From conversion
        ms.sanity_check()?;
        Ok(())
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    /// Create Terminal::Multi containing sorted pubkeys
    pub fn sorted_node(&self) -> Terminal<Pk, Ctx>
    where
        Pk: ToPublicKey,
    {
        let mut pks = self.pks.clone();
        // Sort pubkeys lexicographically according to BIP 67
        pks.sort_by(|a, b| {
            a.to_public_key()
                .inner
                .serialize()
                .partial_cmp(&b.to_public_key().inner.serialize())
                .unwrap()
        });
        Terminal::Multi(self.k, pks)
    }

    /// Encode as a Bitcoin script
    pub fn encode(&self) -> script::Script
    where
        Pk: ToPublicKey,
    {
        self.sorted_node()
            .encode(script::Builder::new())
            .into_script()
    }

    /// Attempt to produce a satisfying witness for the
    /// witness script represented by the parse tree
    pub fn satisfy<S>(&self, satisfier: S) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        let ms = Miniscript::from_ast(self.sorted_node()).expect("Multi node typecheck");
        ms.satisfy(satisfier)
    }

    /// Size, in bytes of the script-pubkey. If this Miniscript is used outside
    /// of segwit (e.g. in a bare or P2SH descriptor), this quantity should be
    /// multiplied by 4 to compute the weight.
    ///
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    pub fn script_size(&self) -> usize {
        script_num_size(self.k)
            + 1
            + script_num_size(self.pks.len())
            + self.pks.iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>()
    }

    /// Maximum number of witness elements used to satisfy the Miniscript
    /// fragment, including the witness script itself. Used to estimate
    /// the weight of the `VarInt` that specifies this number in a serialized
    /// transaction.
    ///
    /// This function may panic on malformed `Miniscript` objects which do
    /// not correspond to semantically sane Scripts. (Such scripts should be
    /// rejected at parse time. Any exceptions are bugs.)
    pub fn max_satisfaction_witness_elements(&self) -> usize {
        2 + self.k
    }

    /// Maximum size, in bytes, of a satisfying witness.
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    ///
    /// All signatures are assumed to be 73 bytes in size, including the
    /// length prefix (segwit) or push opcode (pre-segwit) and sighash
    /// postfix.
    pub fn max_satisfaction_size(&self) -> usize {
        1 + 73 * self.k
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> policy::Liftable<Pk> for SortedMultiVec<Pk, Ctx> {
    fn lift(&self) -> Result<policy::semantic::Policy<Pk>, Error> {
        let ret = policy::semantic::Policy::Threshold(
            self.k,
            self.pks
                .clone()
                .into_iter()
                .map(|k| policy::semantic::Policy::KeyHash(k.to_pubkeyhash()))
                .collect(),
        );
        Ok(ret)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Debug for SortedMultiVec<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Display for SortedMultiVec<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "sortedmulti({}", self.k)?;
        for k in &self.pks {
            write!(f, ",{}", k)?;
        }
        f.write_str(")")
    }
}
