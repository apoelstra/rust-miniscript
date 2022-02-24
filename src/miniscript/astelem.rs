// Miniscript
// Written in 2019 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
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

//! AST Elements
//!
//! Datatype describing a Miniscript "script fragment", which are the
//! building blocks of all Miniscripts. Each fragment has a unique
//! encoding in Bitcoin script, as well as a datatype. Full details
//! are given on the Miniscript website.

use std::str::FromStr;
use std::sync::Arc;
use std::{fmt, str};

use bitcoin::blockdata::{opcodes, script};
use bitcoin::hashes::hex::FromHex;
use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d, Hash};

use errstr;
use expression;
use miniscript::context::SigType;
use miniscript::types::{self, Property};
use miniscript::ScriptContext;
use script_num_size;

use util::MsKeyBuilder;
use {Error, ForEach, ForEachKey, Miniscript, MiniscriptKey, Terminal, ToPublicKey, TranslatePk};

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Terminal<Pk, Ctx> {
    /// Internal helper function for displaying wrapper types; returns
    /// a character to display before the `:` as well as a reference
    /// to the wrapped type to allow easy recursion
    fn wrap_char(&self) -> Option<(char, &Arc<Miniscript<Pk, Ctx>>)> {
        match *self {
            Terminal::Alt(ref sub) => Some(('a', sub)),
            Terminal::Swap(ref sub) => Some(('s', sub)),
            Terminal::Check(ref sub) => Some(('c', sub)),
            Terminal::DupIf(ref sub) => Some(('d', sub)),
            Terminal::Verify(ref sub) => Some(('v', sub)),
            Terminal::NonZero(ref sub) => Some(('j', sub)),
            Terminal::ZeroNotEqual(ref sub) => Some(('n', sub)),
            Terminal::AndV(ref sub, ref r) if r.node == Terminal::True => Some(('t', sub)),
            Terminal::OrI(ref sub, ref r) if r.node == Terminal::False => Some(('u', sub)),
            Terminal::OrI(ref l, ref sub) if l.node == Terminal::False => Some(('l', sub)),
            _ => None,
        }
    }
}

impl<Pk: MiniscriptKey, Q: MiniscriptKey, Ctx: ScriptContext> TranslatePk<Pk, Q>
    for Terminal<Pk, Ctx>
{
    type Output = Terminal<Q, Ctx>;

    /// Convert an AST element with one public key type to one of another
    /// public key type .This will panic while converting to
    /// Segwit Miniscript using uncompressed public keys
    fn translate_pk<FPk, FPkh, FuncError>(
        &self,
        mut translatefpk: FPk,
        mut translatefpkh: FPkh,
    ) -> Result<Self::Output, FuncError>
    where
        FPk: FnMut(&Pk) -> Result<Q, FuncError>,
        FPkh: FnMut(&Pk::Hash) -> Result<Q::Hash, FuncError>,
    {
        self.real_translate_pk(&mut translatefpk, &mut translatefpkh)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Terminal<Pk, Ctx> {
    pub(super) fn real_for_each_key<'a, F: FnMut(ForEach<'a, Pk>) -> bool>(
        &'a self,
        pred: &mut F,
    ) -> bool
    where
        Pk: 'a,
        Pk::Hash: 'a,
    {
        match *self {
            Terminal::PkK(ref p) => pred(ForEach::Key(p)),
            Terminal::PkH(ref p) => pred(ForEach::Hash(p)),
            Terminal::After(..)
            | Terminal::Older(..)
            | Terminal::Sha256(..)
            | Terminal::Hash256(..)
            | Terminal::Ripemd160(..)
            | Terminal::Hash160(..)
            | Terminal::True
            | Terminal::False => true,
            Terminal::Alt(ref sub)
            | Terminal::Swap(ref sub)
            | Terminal::Check(ref sub)
            | Terminal::DupIf(ref sub)
            | Terminal::Verify(ref sub)
            | Terminal::NonZero(ref sub)
            | Terminal::ZeroNotEqual(ref sub) => sub.real_for_each_key(pred),
            Terminal::AndV(ref left, ref right)
            | Terminal::AndB(ref left, ref right)
            | Terminal::OrB(ref left, ref right)
            | Terminal::OrD(ref left, ref right)
            | Terminal::OrC(ref left, ref right)
            | Terminal::OrI(ref left, ref right) => {
                left.real_for_each_key(&mut *pred) && right.real_for_each_key(pred)
            }
            Terminal::AndOr(ref a, ref b, ref c) => {
                a.real_for_each_key(&mut *pred)
                    && b.real_for_each_key(&mut *pred)
                    && c.real_for_each_key(pred)
            }
            Terminal::Thresh(_, ref subs) => subs.iter().all(|sub| sub.real_for_each_key(pred)),
            Terminal::Multi(_, ref keys) | Terminal::MultiA(_, ref keys) => {
                keys.iter().all(|key| pred(ForEach::Key(key)))
            }
        }
    }
    pub(super) fn real_translate_pk<FPk, FPkh, Q, Error, CtxQ>(
        &self,
        translatefpk: &mut FPk,
        translatefpkh: &mut FPkh,
    ) -> Result<Terminal<Q, CtxQ>, Error>
    where
        FPk: FnMut(&Pk) -> Result<Q, Error>,
        FPkh: FnMut(&Pk::Hash) -> Result<Q::Hash, Error>,
        Q: MiniscriptKey,
        CtxQ: ScriptContext,
    {
        let frag: Terminal<Q, CtxQ> = match *self {
            Terminal::PkK(ref p) => Terminal::PkK(translatefpk(p)?),
            Terminal::PkH(ref p) => Terminal::PkH(translatefpkh(p)?),
            Terminal::After(n) => Terminal::After(n),
            Terminal::Older(n) => Terminal::Older(n),
            Terminal::Sha256(x) => Terminal::Sha256(x),
            Terminal::Hash256(x) => Terminal::Hash256(x),
            Terminal::Ripemd160(x) => Terminal::Ripemd160(x),
            Terminal::Hash160(x) => Terminal::Hash160(x),
            Terminal::True => Terminal::True,
            Terminal::False => Terminal::False,
            Terminal::Alt(ref sub) => Terminal::Alt(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::Swap(ref sub) => Terminal::Swap(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::Check(ref sub) => Terminal::Check(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::DupIf(ref sub) => Terminal::DupIf(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::Verify(ref sub) => Terminal::Verify(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::NonZero(ref sub) => Terminal::NonZero(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::ZeroNotEqual(ref sub) => Terminal::ZeroNotEqual(Arc::new(
                sub.real_translate_pk(translatefpk, translatefpkh)?,
            )),
            Terminal::AndV(ref left, ref right) => Terminal::AndV(
                Arc::new(left.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::AndB(ref left, ref right) => Terminal::AndB(
                Arc::new(left.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::AndOr(ref a, ref b, ref c) => Terminal::AndOr(
                Arc::new(a.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(b.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(c.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::OrB(ref left, ref right) => Terminal::OrB(
                Arc::new(left.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::OrD(ref left, ref right) => Terminal::OrD(
                Arc::new(left.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::OrC(ref left, ref right) => Terminal::OrC(
                Arc::new(left.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)?),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::OrI(ref left, ref right) => Terminal::OrI(
                Arc::new(
                    left.real_translate_pk(&mut *&mut *translatefpk, &mut *&mut *translatefpkh)?,
                ),
                Arc::new(right.real_translate_pk(translatefpk, translatefpkh)?),
            ),
            Terminal::Thresh(k, ref subs) => {
                let subs: Result<Vec<Arc<Miniscript<Q, _>>>, _> = subs
                    .iter()
                    .map(|s| {
                        s.real_translate_pk(&mut *translatefpk, &mut *translatefpkh)
                            .and_then(|x| Ok(Arc::new(x)))
                    })
                    .collect();
                Terminal::Thresh(k, subs?)
            }
            Terminal::Multi(k, ref keys) => {
                let keys: Result<Vec<Q>, _> = keys.iter().map(&mut *translatefpk).collect();
                Terminal::Multi(k, keys?)
            }
            Terminal::MultiA(k, ref keys) => {
                let keys: Result<Vec<Q>, _> = keys.iter().map(&mut *translatefpk).collect();
                Terminal::MultiA(k, keys?)
            }
        };
        Ok(frag)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> ForEachKey<Pk> for Terminal<Pk, Ctx> {
    fn for_each_key<'a, F: FnMut(ForEach<'a, Pk>) -> bool>(&'a self, mut pred: F) -> bool
    where
        Pk: 'a,
        Pk::Hash: 'a,
    {
        self.real_for_each_key(&mut pred)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Debug for Terminal<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[")?;
        if let Ok(type_map) = types::Type::type_check(self, |_| None) {
            f.write_str(match type_map.corr.base {
                types::Base::B => "B",
                types::Base::K => "K",
                types::Base::V => "V",
                types::Base::W => "W",
            })?;
            fmt::Write::write_char(f, '/')?;
            f.write_str(match type_map.corr.input {
                types::Input::Zero => "z",
                types::Input::One => "o",
                types::Input::OneNonZero => "on",
                types::Input::Any => "",
                types::Input::AnyNonZero => "n",
            })?;
            if type_map.corr.dissatisfiable {
                fmt::Write::write_char(f, 'd')?;
            }
            if type_map.corr.unit {
                fmt::Write::write_char(f, 'u')?;
            }
            f.write_str(match type_map.mall.dissat {
                types::Dissat::None => "f",
                types::Dissat::Unique => "e",
                types::Dissat::Unknown => "",
            })?;
            if type_map.mall.safe {
                fmt::Write::write_char(f, 's')?;
            }
            if type_map.mall.non_malleable {
                fmt::Write::write_char(f, 'm')?;
            }
        } else {
            f.write_str("TYPECHECK FAILED")?;
        }
        f.write_str("]")?;
        if let Some((ch, sub)) = self.wrap_char() {
            fmt::Write::write_char(f, ch)?;
            if sub.node.wrap_char().is_none() {
                fmt::Write::write_char(f, ':')?;
            }
            write!(f, "{:?}", sub)
        } else {
            match *self {
                Terminal::PkK(ref pk) => write!(f, "pk_k({:?})", pk),
                Terminal::PkH(ref pkh) => write!(f, "pk_h({:?})", pkh),
                Terminal::After(t) => write!(f, "after({})", t),
                Terminal::Older(t) => write!(f, "older({})", t),
                Terminal::Sha256(h) => write!(f, "sha256({})", h),
                Terminal::Hash256(h) => {
                    let mut x = h.into_inner();
                    x.reverse();
                    write!(f, "hash256({})", sha256d::Hash::from_inner(x))
                }
                Terminal::Ripemd160(h) => write!(f, "ripemd160({})", h),
                Terminal::Hash160(h) => write!(f, "hash160({})", h),
                Terminal::True => f.write_str("1"),
                Terminal::False => f.write_str("0"),
                Terminal::AndV(ref l, ref r) => write!(f, "and_v({:?},{:?})", l, r),
                Terminal::AndB(ref l, ref r) => write!(f, "and_b({:?},{:?})", l, r),
                Terminal::AndOr(ref a, ref b, ref c) => {
                    if c.node == Terminal::False {
                        write!(f, "and_n({:?},{:?})", a, b)
                    } else {
                        write!(f, "andor({:?},{:?},{:?})", a, b, c)
                    }
                }
                Terminal::OrB(ref l, ref r) => write!(f, "or_b({:?},{:?})", l, r),
                Terminal::OrD(ref l, ref r) => write!(f, "or_d({:?},{:?})", l, r),
                Terminal::OrC(ref l, ref r) => write!(f, "or_c({:?},{:?})", l, r),
                Terminal::OrI(ref l, ref r) => write!(f, "or_i({:?},{:?})", l, r),
                Terminal::Thresh(k, ref subs) => {
                    write!(f, "thresh({}", k)?;
                    for s in subs {
                        write!(f, ",{:?}", s)?;
                    }
                    f.write_str(")")
                }
                Terminal::Multi(k, ref keys) => {
                    write!(f, "multi({}", k)?;
                    for k in keys {
                        write!(f, ",{:?}", k)?;
                    }
                    f.write_str(")")
                }
                Terminal::MultiA(k, ref keys) => {
                    write!(f, "multi_a({}", k)?;
                    for k in keys {
                        write!(f, ",{}", k)?;
                    }
                    f.write_str(")")
                }
                _ => unreachable!(),
            }
        }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Display for Terminal<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Terminal::PkK(ref pk) => write!(f, "pk_k({})", pk),
            Terminal::PkH(ref pkh) => write!(f, "pk_h({})", pkh),
            Terminal::After(t) => write!(f, "after({})", t),
            Terminal::Older(t) => write!(f, "older({})", t),
            Terminal::Sha256(h) => write!(f, "sha256({})", h),
            Terminal::Hash256(h) => {
                let mut x = h.into_inner();
                x.reverse();
                write!(f, "hash256({})", sha256d::Hash::from_inner(x))
            }
            Terminal::Ripemd160(h) => write!(f, "ripemd160({})", h),
            Terminal::Hash160(h) => write!(f, "hash160({})", h),
            Terminal::True => f.write_str("1"),
            Terminal::False => f.write_str("0"),
            Terminal::AndV(ref l, ref r) if r.node != Terminal::True => {
                write!(f, "and_v({},{})", l, r)
            }
            Terminal::AndB(ref l, ref r) => write!(f, "and_b({},{})", l, r),
            Terminal::AndOr(ref a, ref b, ref c) => {
                if c.node == Terminal::False {
                    write!(f, "and_n({},{})", a, b)
                } else {
                    write!(f, "andor({},{},{})", a, b, c)
                }
            }
            Terminal::OrB(ref l, ref r) => write!(f, "or_b({},{})", l, r),
            Terminal::OrD(ref l, ref r) => write!(f, "or_d({},{})", l, r),
            Terminal::OrC(ref l, ref r) => write!(f, "or_c({},{})", l, r),
            Terminal::OrI(ref l, ref r)
                if l.node != Terminal::False && r.node != Terminal::False =>
            {
                write!(f, "or_i({},{})", l, r)
            }
            Terminal::Thresh(k, ref subs) => {
                write!(f, "thresh({}", k)?;
                for s in subs {
                    write!(f, ",{}", s)?;
                }
                f.write_str(")")
            }
            Terminal::Multi(k, ref keys) => {
                write!(f, "multi({}", k)?;
                for k in keys {
                    write!(f, ",{}", k)?;
                }
                f.write_str(")")
            }
            Terminal::MultiA(k, ref keys) => {
                write!(f, "multi_a({}", k)?;
                for k in keys {
                    write!(f, ",{}", k)?;
                }
                f.write_str(")")
            }
            // wrappers
            _ => {
                if let Some((ch, sub)) = self.wrap_char() {
                    if ch == 'c' {
                        if let Terminal::PkK(ref pk) = sub.node {
                            // alias: pk(K) = c:pk_k(K)
                            return write!(f, "pk({})", pk);
                        } else if let Terminal::PkH(ref pkh) = sub.node {
                            // alias: pkh(K) = c:pk_h(K)
                            return write!(f, "pkh({})", pkh);
                        }
                    }

                    fmt::Write::write_char(f, ch)?;
                    match sub.node.wrap_char() {
                        None => {
                            fmt::Write::write_char(f, ':')?;
                        }
                        // Add a ':' wrapper if there are other wrappers apart from c:pk_k()
                        // tvc:pk_k() -> tv:pk()
                        Some(('c', ms)) => {
                            if let Terminal::PkK(ref _pk) = ms.node {
                                fmt::Write::write_char(f, ':')?;
                            } else if let Terminal::PkH(ref _pkh) = ms.node {
                                fmt::Write::write_char(f, ':')?;
                            }
                        }
                        _ => {}
                    };
                    write!(f, "{}", sub)
                } else {
                    unreachable!();
                }
            }
        }
    }
}

impl<Pk, Ctx> expression::FromTree for Arc<Terminal<Pk, Ctx>>
where
    Pk: MiniscriptKey + str::FromStr,
    Pk::Hash: str::FromStr,
    Ctx: ScriptContext,
    <Pk as str::FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as str::FromStr>::Err: ToString,
{
    fn from_tree(top: &expression::Tree) -> Result<Arc<Terminal<Pk, Ctx>>, Error> {
        Ok(Arc::new(expression::FromTree::from_tree(top)?))
    }
}

impl<Pk, Ctx> expression::FromTree for Terminal<Pk, Ctx>
where
    Pk: MiniscriptKey + str::FromStr,
    Pk::Hash: str::FromStr,
    Ctx: ScriptContext,
    <Pk as str::FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as str::FromStr>::Err: ToString,
{
    fn from_tree(top: &expression::Tree) -> Result<Terminal<Pk, Ctx>, Error> {
        let mut aliased_wrap;
        let frag_name;
        let frag_wrap;
        let mut name_split = top.name.split(':');
        match (name_split.next(), name_split.next(), name_split.next()) {
            (None, _, _) => {
                frag_name = "";
                frag_wrap = "";
            }
            (Some(name), None, _) => {
                if name == "pk" {
                    frag_name = "pk_k";
                    frag_wrap = "c";
                } else if name == "pkh" {
                    frag_name = "pk_h";
                    frag_wrap = "c";
                } else {
                    frag_name = name;
                    frag_wrap = "";
                }
            }
            (Some(wrap), Some(name), None) => {
                if wrap.is_empty() {
                    return Err(Error::Unexpected(top.name.to_owned()));
                }
                if name == "pk" {
                    frag_name = "pk_k";
                    aliased_wrap = wrap.to_owned();
                    aliased_wrap.push_str("c");
                    frag_wrap = &aliased_wrap;
                } else if name == "pkh" {
                    frag_name = "pk_h";
                    aliased_wrap = wrap.to_owned();
                    aliased_wrap.push_str("c");
                    frag_wrap = &aliased_wrap;
                } else {
                    frag_name = name;
                    frag_wrap = wrap;
                }
            }
            (Some(_), Some(_), Some(_)) => {
                return Err(Error::MultiColon(top.name.to_owned()));
            }
        }
        let mut unwrapped = match (frag_name, top.args.len()) {
            ("pk_k", 1) => {
                expression::terminal(&top.args[0], |x| Pk::from_str(x).map(Terminal::PkK))
            }
            ("pk_h", 1) => {
                expression::terminal(&top.args[0], |x| Pk::Hash::from_str(x).map(Terminal::PkH))
            }
            ("after", 1) => expression::terminal(&top.args[0], |x| {
                expression::parse_num(x).map(Terminal::After)
            }),
            ("older", 1) => expression::terminal(&top.args[0], |x| {
                expression::parse_num(x).map(Terminal::Older)
            }),
            ("sha256", 1) => expression::terminal(&top.args[0], |x| {
                sha256::Hash::from_hex(x).map(Terminal::Sha256)
            }),
            ("hash256", 1) => expression::terminal(&top.args[0], |x| {
                sha256d::Hash::from_hex(x)
                    .map(|x| x.into_inner())
                    .map(|mut x| {
                        x.reverse();
                        x
                    })
                    .map(|x| Terminal::Hash256(sha256d::Hash::from_inner(x)))
            }),
            ("ripemd160", 1) => expression::terminal(&top.args[0], |x| {
                ripemd160::Hash::from_hex(x).map(Terminal::Ripemd160)
            }),
            ("hash160", 1) => expression::terminal(&top.args[0], |x| {
                hash160::Hash::from_hex(x).map(Terminal::Hash160)
            }),
            ("1", 0) => Ok(Terminal::True),
            ("0", 0) => Ok(Terminal::False),
            ("and_v", 2) => expression::binary(top, Terminal::AndV),
            ("and_b", 2) => expression::binary(top, Terminal::AndB),
            ("and_n", 2) => Ok(Terminal::AndOr(
                expression::FromTree::from_tree(&top.args[0])?,
                expression::FromTree::from_tree(&top.args[1])?,
                Arc::new(Miniscript::from_ast(Terminal::False)?),
            )),
            ("andor", 3) => Ok(Terminal::AndOr(
                expression::FromTree::from_tree(&top.args[0])?,
                expression::FromTree::from_tree(&top.args[1])?,
                expression::FromTree::from_tree(&top.args[2])?,
            )),
            ("or_b", 2) => expression::binary(top, Terminal::OrB),
            ("or_d", 2) => expression::binary(top, Terminal::OrD),
            ("or_c", 2) => expression::binary(top, Terminal::OrC),
            ("or_i", 2) => expression::binary(top, Terminal::OrI),
            ("thresh", n) => {
                if n == 0 {
                    return Err(errstr("no arguments given"));
                }
                let k = expression::terminal(&top.args[0], expression::parse_num)? as usize;
                if k > n - 1 {
                    return Err(errstr("higher threshold than there are subexpressions"));
                }
                if n == 1 {
                    return Err(errstr("empty thresholds not allowed in descriptors"));
                }

                let subs: Result<Vec<Arc<Miniscript<Pk, Ctx>>>, _> = top.args[1..]
                    .iter()
                    .map(|sub| expression::FromTree::from_tree(sub))
                    .collect();

                Ok(Terminal::Thresh(k, subs?))
            }
            ("multi", n) | ("multi_a", n) => {
                if n == 0 {
                    return Err(errstr("no arguments given"));
                }
                let k = expression::terminal(&top.args[0], expression::parse_num)? as usize;
                if k > n - 1 {
                    return Err(errstr("higher threshold than there were keys in multi"));
                }

                let pks: Result<Vec<Pk>, _> = top.args[1..]
                    .iter()
                    .map(|sub| expression::terminal(sub, Pk::from_str))
                    .collect();

                if frag_name == "multi" {
                    pks.map(|pks| Terminal::Multi(k, pks))
                } else {
                    // must be multi_a
                    pks.map(|pks| Terminal::MultiA(k, pks))
                }
            }
            _ => Err(Error::Unexpected(format!(
                "{}({} args) while parsing Miniscript",
                top.name,
                top.args.len(),
            ))),
        }?;
        for ch in frag_wrap.chars().rev() {
            // Check whether the wrapper is valid under the current context
            let ms = Miniscript::from_ast(unwrapped)?;
            Ctx::check_global_validity(&ms)?;
            match ch {
                'a' => unwrapped = Terminal::Alt(Arc::new(ms)),
                's' => unwrapped = Terminal::Swap(Arc::new(ms)),
                'c' => unwrapped = Terminal::Check(Arc::new(ms)),
                'd' => unwrapped = Terminal::DupIf(Arc::new(ms)),
                'v' => unwrapped = Terminal::Verify(Arc::new(ms)),
                'j' => unwrapped = Terminal::NonZero(Arc::new(ms)),
                'n' => unwrapped = Terminal::ZeroNotEqual(Arc::new(ms)),
                't' => {
                    unwrapped = Terminal::AndV(
                        Arc::new(ms),
                        Arc::new(Miniscript::from_ast(Terminal::True)?),
                    )
                }
                'u' => {
                    unwrapped = Terminal::OrI(
                        Arc::new(ms),
                        Arc::new(Miniscript::from_ast(Terminal::False)?),
                    )
                }
                'l' => {
                    if ms.node == Terminal::False {
                        return Err(Error::LikelyFalse);
                    }
                    unwrapped = Terminal::OrI(
                        Arc::new(Miniscript::from_ast(Terminal::False)?),
                        Arc::new(ms),
                    )
                }
                x => return Err(Error::UnknownWrapper(x)),
            }
        }
        // Check whether the unwrapped miniscript is valid under the current context
        let ms = Miniscript::from_ast(unwrapped)?;
        Ctx::check_global_validity(&ms)?;
        Ok(ms.node)
    }
}

/// Helper trait to add a `push_astelem` method to `script::Builder`
trait PushAstElem<Pk: MiniscriptKey, Ctx: ScriptContext> {
    fn push_astelem(self, ast: &Miniscript<Pk, Ctx>) -> Self
    where
        Pk: ToPublicKey;
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> PushAstElem<Pk, Ctx> for script::Builder {
    fn push_astelem(self, ast: &Miniscript<Pk, Ctx>) -> Self
    where
        Pk: ToPublicKey,
    {
        ast.node.encode(self)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Terminal<Pk, Ctx> {
    /// Encode the element as a fragment of Bitcoin Script. The inverse
    /// function, from Script to an AST element, is implemented in the
    /// `parse` module.
    pub fn encode(&self, mut builder: script::Builder) -> script::Builder
    where
        Pk: ToPublicKey,
    {
        match *self {
            Terminal::PkK(ref pk) => builder.push_ms_key::<_, Ctx>(pk),
            Terminal::PkH(ref hash) => builder
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(&Pk::hash_to_hash160(&hash)[..])
                .push_opcode(opcodes::all::OP_EQUALVERIFY),
            Terminal::After(t) => builder
                .push_int(t as i64)
                .push_opcode(opcodes::all::OP_CLTV),
            Terminal::Older(t) => builder.push_int(t as i64).push_opcode(opcodes::all::OP_CSV),
            Terminal::Sha256(h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_SHA256)
                .push_slice(&h[..])
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Hash256(h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_HASH256)
                .push_slice(&h[..])
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Ripemd160(h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_RIPEMD160)
                .push_slice(&h[..])
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Hash160(h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(&h[..])
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::True => builder.push_opcode(opcodes::OP_TRUE),
            Terminal::False => builder.push_opcode(opcodes::OP_FALSE),
            Terminal::Alt(ref sub) => builder
                .push_opcode(opcodes::all::OP_TOALTSTACK)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_FROMALTSTACK),
            Terminal::Swap(ref sub) => builder.push_opcode(opcodes::all::OP_SWAP).push_astelem(sub),
            Terminal::Check(ref sub) => builder
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_CHECKSIG),
            Terminal::DupIf(ref sub) => builder
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::Verify(ref sub) => builder.push_astelem(sub).push_verify(),
            Terminal::NonZero(ref sub) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_opcode(opcodes::all::OP_0NOTEQUAL)
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::ZeroNotEqual(ref sub) => builder
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_0NOTEQUAL),
            Terminal::AndV(ref left, ref right) => builder.push_astelem(left).push_astelem(right),
            Terminal::AndB(ref left, ref right) => builder
                .push_astelem(left)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_BOOLAND),
            Terminal::AndOr(ref a, ref b, ref c) => builder
                .push_astelem(a)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(c)
                .push_opcode(opcodes::all::OP_ELSE)
                .push_astelem(b)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrB(ref left, ref right) => builder
                .push_astelem(left)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_BOOLOR),
            Terminal::OrD(ref left, ref right) => builder
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_IFDUP)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrC(ref left, ref right) => builder
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrI(ref left, ref right) => builder
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_ELSE)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::Thresh(k, ref subs) => {
                builder = builder.push_astelem(&subs[0]);
                for sub in &subs[1..] {
                    builder = builder.push_astelem(sub).push_opcode(opcodes::all::OP_ADD);
                }
                builder
                    .push_int(k as i64)
                    .push_opcode(opcodes::all::OP_EQUAL)
            }
            Terminal::Multi(k, ref keys) => {
                debug_assert!(Ctx::sig_type() == SigType::Ecdsa);
                builder = builder.push_int(k as i64);
                for pk in keys {
                    builder = builder.push_key(&pk.to_public_key());
                }
                builder
                    .push_int(keys.len() as i64)
                    .push_opcode(opcodes::all::OP_CHECKMULTISIG)
            }
            Terminal::MultiA(k, ref keys) => {
                debug_assert!(Ctx::sig_type() == SigType::Schnorr);
                // keys must be atleast len 1 here, guaranteed by typing rules
                builder = builder.push_ms_key::<_, Ctx>(&keys[0]);
                builder = builder.push_opcode(opcodes::all::OP_CHECKSIG);
                for pk in keys.iter().skip(1) {
                    builder = builder.push_ms_key::<_, Ctx>(pk);
                    builder = builder.push_opcode(opcodes::all::OP_CHECKSIGADD);
                }
                builder
                    .push_int(k as i64)
                    .push_opcode(opcodes::all::OP_NUMEQUAL)
            }
        }
    }

    /// Size, in bytes of the script-pubkey. If this Miniscript is used outside
    /// of segwit (e.g. in a bare or P2SH descriptor), this quantity should be
    /// multiplied by 4 to compute the weight.
    ///
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    pub fn script_size(&self) -> usize {
        match *self {
            Terminal::PkK(ref pk) => Ctx::pk_len(pk),
            Terminal::PkH(..) => 24,
            Terminal::After(n) => script_num_size(n as usize) + 1,
            Terminal::Older(n) => script_num_size(n as usize) + 1,
            Terminal::Sha256(..) => 33 + 6,
            Terminal::Hash256(..) => 33 + 6,
            Terminal::Ripemd160(..) => 21 + 6,
            Terminal::Hash160(..) => 21 + 6,
            Terminal::True => 1,
            Terminal::False => 1,
            Terminal::Alt(ref sub) => sub.node.script_size() + 2,
            Terminal::Swap(ref sub) => sub.node.script_size() + 1,
            Terminal::Check(ref sub) => sub.node.script_size() + 1,
            Terminal::DupIf(ref sub) => sub.node.script_size() + 3,
            Terminal::Verify(ref sub) => {
                sub.node.script_size() + if sub.ext.has_free_verify { 0 } else { 1 }
            }
            Terminal::NonZero(ref sub) => sub.node.script_size() + 4,
            Terminal::ZeroNotEqual(ref sub) => sub.node.script_size() + 1,
            Terminal::AndV(ref l, ref r) => l.node.script_size() + r.node.script_size(),
            Terminal::AndB(ref l, ref r) => l.node.script_size() + r.node.script_size() + 1,
            Terminal::AndOr(ref a, ref b, ref c) => {
                a.node.script_size() + b.node.script_size() + c.node.script_size() + 3
            }
            Terminal::OrB(ref l, ref r) => l.node.script_size() + r.node.script_size() + 1,
            Terminal::OrD(ref l, ref r) => l.node.script_size() + r.node.script_size() + 3,
            Terminal::OrC(ref l, ref r) => l.node.script_size() + r.node.script_size() + 2,
            Terminal::OrI(ref l, ref r) => l.node.script_size() + r.node.script_size() + 3,
            Terminal::Thresh(k, ref subs) => {
                assert!(!subs.is_empty(), "threshold must be nonempty");
                script_num_size(k) // k
                    + 1 // EQUAL
                    + subs.iter().map(|s| s.node.script_size()).sum::<usize>()
                    + subs.len() // ADD
                    - 1 // no ADD on first element
            }
            Terminal::Multi(k, ref pks) => {
                script_num_size(k)
                    + 1
                    + script_num_size(pks.len())
                    + pks.iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>()
            }
            Terminal::MultiA(k, ref pks) => {
                script_num_size(k)
                    + 1 // NUMEQUAL
                    + pks.iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>() // n keys
                    + pks.len() // n times CHECKSIGADD
            }
        }
    }
}
