#![verus::trusted]
//! Wrapper around Rust HashMap, with a Map view
//!
//! This is a HashMap<u64, Vec<u8>>. We need the key to be hashable, and the
//! view uses the view of the values.
// At the time this was written, Verus generics had some
// limitations; those limitations may already resolved now.
//
// TODO: we will also need some hashmaps with Vec<u8> as their keys.

// This map is trusted because the corresponding Dafny code uses Dafny's built-in
// map types. At the time this was written, Verus' map library had limitations
// that prevented us from exporting all the verification promises we needed,
// so we hack those promises in here.
// (That, and some of the operations require assuming the inputs are immutable,
// which the values are not, so we need a clone-up-to-view sort of promise.)

use crate::host_protocol_t::*;
use crate::keys_t::*;
use std::collections;
use vstd::map::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    /// The abstract contents of the CKeyHashMap.
    pub closed spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

    #[verifier(external_body)]
    pub fn new() -> (out: CKeyHashMap)
        ensures
            out@ == Map::<AbstractKey, Seq<u8>>::empty(),
    {
        CKeyHashMap { m: collections::HashMap::new() }
    }

    #[verifier::external_body]
    pub fn len(&self) -> (l: usize)
        ensures
            l as int == self@.len(),
    {
        self.m.len()
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: CKey, value: Vec<u8>)
        ensures
            self@ == old(self)@.insert(key, value@),
    {
        //TODO: Soundness issue needs careful examination: What properties must we demand of Key
        //for this ensures to be correct? If Key has a nondeterministic hash, for example, this
        //ensures will be false.
        self.m.insert(key, value);
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &CKey)
        ensures
            self@ == old(self)@.remove(*key),
    {
        panic!()
    }

    #[verifier(external_body)]
    pub fn get(&self, key: &CKey) -> (value: Option<&Vec<u8>>)
        ensures
            (match value {
                Some(v) => self@.dom().contains(*key) && self@[*key] == v@,
                None => !self@.dom().contains(*key),
            }),
    {
        //TODO(parno): think carefully of properties we must demand of Key for this ensures to be correct.
        // (If Key has a nondeterministic hash, this ensures will be a lie.)
        match self.m.get(&key) {
            std::option::Option::Some(v) => Some(v),
            std::option::Option::None => None,
        }
    }

    #[verifier(external_body)]
    pub fn bulk_update(&mut self, kr: &KeyRange::<CKey>, other: &Self)
        ensures
            self@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey|
                    (old(self)@.dom().contains(k) || other@.dom().contains(k)) && (kr.contains(k)
                        ==> other@.dom().contains(k)),
                |k: AbstractKey|
                    if other@.dom().contains(k) {
                        other@[k]
                    } else {
                        old(self)@[k]
                    },
            ),
    {
        panic!()
    }

    #[verifier(external_body)]
    pub fn bulk_remove(&mut self, kr: &KeyRange::<CKey>)
        ensures
            self@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey| old(self)@.dom().contains(k) && !kr.contains(k),
                |k: AbstractKey| old(self)@[k],
            ),
    {
        panic!()
    }

    pub closed spec fn spec_to_vec(&self) -> Vec<CKeyKV>;

    pub closed spec fn spec_from_vec(v: Vec<CKeyKV>) -> Self;

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>)
        ensures
            res == self.spec_to_vec(),
    {
        let mut v: std::vec::Vec<(u64, std::vec::Vec<u8>)> = self.m.iter().map(
            |(k, v)| (k.ukey, v.clone()),
        ).collect();
        v.sort();
        v.into_iter().map(|(k, v)| CKeyKV { k: CKey { ukey: k }, v }).collect()
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_from_vec))]
    pub fn from_vec(v: Vec<CKeyKV>) -> (res: Self)
        ensures
            res == Self::spec_from_vec(v),
    {
        let mut res = CKeyHashMap::new();
        for CKeyKV { k, v } in v {
            res.insert(k, v);
        }
        res
    }

    #[verifier(external_body)]
    pub broadcast proof fn lemma_to_vec(self)
        ensures
            #[trigger(self.spec_to_vec())]
            Self::spec_from_vec(self.spec_to_vec()) == self,
            self.spec_to_vec().len() == self@.dom().len(),
            spec_sorted_keys(self.spec_to_vec()),
            (forall|i: int|
                #![trigger(self.spec_to_vec()[i])]
                0 <= i < self.spec_to_vec().len() ==> {
                    let (k, v) = self.spec_to_vec()[i]@;
                    self@.contains_pair(k, v)
                }),
    ;

    #[verifier(external_body)]
    pub proof fn lemma_to_vec_view(self, other: Self)
        ensures
            (self@ == other@ <==> self.spec_to_vec()@ == other.spec_to_vec()@) && (self@ == other@
                <==> (self.spec_to_vec().len() == other.spec_to_vec().len() && forall|i: int|
                #![auto]
                0 <= i < self.spec_to_vec().len() ==> self.spec_to_vec()[i]@
                    == other.spec_to_vec()[i]@)),
    ;

    #[verifier(external_body)]
    pub broadcast proof fn lemma_from_vec(v: Vec<CKeyKV>)
        ensures
            #[trigger(Self::spec_from_vec(v))]
            spec_sorted_keys(v) ==> Self::spec_from_vec(v).spec_to_vec() == v,
    ;

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (out: Self)
        ensures
            out@ == self@,
    {
        Self::from_vec(self.to_vec())
    }

    #[verifier(external_body)]
    pub fn valid(&self) -> (b: bool)
        ensures
            b == valid_hashtable(self@),
    {
        panic!()
    }

    pub open spec fn filter_spec(self, fs: spec_fn(CKey) -> bool) -> Map<AbstractKey, Seq<u8>> {
        Map::<AbstractKey, Seq<u8>>::new(
            |k: AbstractKey| self@.dom().contains(k) && fs(k),
            |k: AbstractKey| self@[k],
        )
    }

    // TODO: Move this concept into a Verus standard library
    pub open spec fn predicate_models<T, EF: Fn(T) -> bool>(
        exec_fn: EF,
        spec_fn: spec_fn(T) -> bool,
    ) -> bool {
        &&& forall|t| #![auto] exec_fn.requires((t,))
        &&& forall|t, b| exec_fn.ensures((t,), b) ==> spec_fn(t) == b
    }

    #[verifier(external_body)]  // iter was not supported at the time this was written
    pub fn filter<F: Fn(CKey) -> bool>(&self, f: F, fs: Ghost<spec_fn(CKey) -> bool>) -> (res: Self)
        requires
            Self::predicate_models(f, fs@),
        ensures
            res@ == self.filter_spec(fs@),
    {
        let mut res = CKeyHashMap::new();
        let mut iter = self.m.iter();
        let cur: Option<(&CKey, &Vec<u8>)> = iter.next();
        while cur.is_some() {
            let Some((key, val)) = cur else {
                panic!()  /* covered by while condition */

            };
            res.insert(key.clone(), val.clone());
        }
        res
    }
}

// pub struct KeyIterator
// {
//     view: Set<CKey>,
//     iter: Keys<CKey, Vec<u8>>,
// }
pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

impl CKeyKV {
    pub open spec fn view(self) -> (AbstractKey, Seq<u8>) {
        (self.k, self.v@)
    }
}

pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    // ckeykvlt ensures that this forall does not create a trigger loop on
    // v@[i].k.ukey, v@[i+1].k.ukey, ...
    //
    // we weren't able to fix this by making the whole < the trigger
    forall|i: int, j: int|
        0 <= i && i + 1 < v.len() && j == i + 1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}

} // verus!
