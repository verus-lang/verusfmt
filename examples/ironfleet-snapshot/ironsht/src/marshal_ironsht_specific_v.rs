//! All the marshalable types specific to IronSHT are stored in this file. All the types themselves
//! are defined in different modules, but the marshaling implementations (using functionality
//! provided by `marshal_v`) are written in this module.
// TODO FIXME Probably need a better name for this
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::function::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::slice::*;

use vstd::*;

use crate::args_t::clone_vec_u8;
use crate::hashmap_t::ckeykvlt;

use crate::marshal_v::*;
use crate::verus_extra::seq_lib_v::*;

verus! {

use crate::keys_t::{SHTKey, CKey, KeyRange, KeyIterator};
use crate::io_t::EndPoint;
use crate::hashmap_t::{CKeyHashMap, CKeyKV};
use crate::cmessage_v::CMessage;

/* $line_count$Proof$ */

marshalable_by_bijection! {
    /* $line_count$Proof$ */     [SHTKey] <-> [u64];
    /* $line_count$Proof$ */     forward(self) self.ukey;
    /* $line_count$Proof$ */     backward(x) SHTKey { ukey: x };
    /* $line_count$Proof$ */ }

impl SHTKey {
    /// Document that view_equal is definitionally to ==, with no explicit proof required.
    pub proof fn view_equal_spec()
        ensures
            forall|x: &SHTKey, y: &SHTKey| #[trigger] x.view_equal(y) <==> x == y,
    {
    }
}

/* $line_count$Proof$}$ */

marshalable_by_bijection! {
    /* $line_count$Proof$}$ */    [EndPoint] <-> [Vec::<u8>];
    /* $line_count$Proof$}$ */    forward(self) self.id;
    /* $line_count$Proof$}$ */    backward(x) EndPoint { id: x };
    /* $line_count$Proof$}$ */ }

impl EndPoint {
    /// Document that view_equal is definitially x@ == y@, with no explicit proof required.
    pub proof fn view_equal_spec()
        ensures
            forall|x: &EndPoint, y: &EndPoint| #[trigger] x.view_equal(y) <==> x@ == y@,
    {
    }
}

/* $line_count$Proof$ */

marshalable_by_bijection! {
    /* $line_count$Proof$ */     [KeyRange::<CKey>] <-> [(Option::<u64>, Option::<u64>)];
    /* $line_count$Proof$ */     forward(self) {
    /* $line_count$Proof$ */         (
    /* $line_count$Proof$ */             match &self.lo.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             match &self.hi.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         )
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */     backward(x) {
    /* $line_count$Proof$ */         KeyRange {
    /* $line_count$Proof$ */             lo: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.0 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             hi: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.1 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         }
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */ }/* $line_count$Proof$ */


derive_marshalable_for_struct! {
    /* $line_count$Proof$ */     pub struct CKeyKV {
    /* $line_count$Proof$ */         pub k: CKey,
    /* $line_count$Proof$ */         pub v: Vec::<u8>,
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */ }

pub exec fn sorted_keys(v: &Vec<CKeyKV>) -> (res: bool)
    ensures
        res == crate::hashmap_t::spec_sorted_keys(*v),
{
    if v.len() <= 1 {
        true
    } else {
        let mut idx = 1;
        while idx < v.len()
            invariant
                (0 < idx <= v.len()),
                (forall|i: int, j: int|
                    0 <= i && i + 1 < idx && j == i + 1 ==> #[trigger] ckeykvlt(v@[i], v@[j])),
        {
            if v[idx - 1].k.ukey >= v[idx].k.ukey {
                assert(!ckeykvlt(v@[idx as int - 1], v@[idx as int]));
                return false;
            } else {
                idx = idx + 1;
            }
        }
        assert forall|i: int| 0 <= i && i + 1 < v.len() implies #[trigger] v@[i].k.ukey < v@[i
            + 1].k.ukey by {
            assert(ckeykvlt(v@[i], v@[i + 1]));  // OBSERVE
        }
        true
    }
}

// To be able to prove marshalability, we need an arbitrary upper limit on the serialized size.
// This relates to `valid_value`; perhaps it could be used to obviate this limit?
#[verifier::opaque]
pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
    0x100000
}

pub fn ckeyhashmap_max_serialized_size_exec() -> (r: usize)
    ensures
        r == ckeyhashmap_max_serialized_size(),
{
    reveal(ckeyhashmap_max_serialized_size);
    0x100000
}

impl Marshalable for CKeyHashMap {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    proof fn lemma_view_equal_symmetric(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
    }

    open spec fn is_marshalable(&self) -> bool {
        self.to_vec().is_marshalable() && crate::hashmap_t::spec_sorted_keys(self.to_vec())
            && self.to_vec().ghost_serialize().len() <= (ckeyhashmap_max_serialized_size() as int)
    }

    exec fn _is_marshalable(&self) -> (res: bool)
    // req, ens from trait
    {
        let v = self.to_vec();
        let a = sorted_keys(&self.to_vec());
        v._is_marshalable() && a && self.to_vec().serialized_size()
            <= ckeyhashmap_max_serialized_size_exec()
    }

    open spec fn ghost_serialize(&self) -> Seq<u8>
    // req, ens from trait
    {
        self.to_vec().ghost_serialize()
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        self.to_vec().serialized_size()
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        self.to_vec().serialize(data)
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        match <Vec<CKeyKV>>::deserialize(data, start) {
            None => { None },
            Some((x, end)) => {
                if !sorted_keys(&x) {
                    None
                } else {
                    let res = CKeyHashMap::from_vec(x);
                    if end - start > ckeyhashmap_max_serialized_size_exec() {
                        None
                    } else {
                        proof {
                            CKeyHashMap::lemma_from_vec(x);
                        }
                        Some((res, end))
                    }
                }
            },
        }
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        self.lemma_to_vec_view(*other);
        assert(self.to_vec()@ != other.to_vec()@);
        if self.to_vec().len() != other.to_vec().len() {
            self.to_vec().lemma_serialization_is_not_a_prefix_of(&other.to_vec());
        } else {
            assert(exists|i: int|
                #![auto]
                0 <= i < self.spec_to_vec().len() && self.spec_to_vec()[i]@
                    != other.spec_to_vec()[i]@);
            let i = choose|i: int|
                #![auto]
                0 <= i < self.spec_to_vec().len() && self.spec_to_vec()[i]@
                    != other.spec_to_vec()[i]@;
            assert(self.to_vec()[i]@ != other.to_vec()[i]@);
            assert(!self.to_vec()[i].view_equal(&other.to_vec()[i]));
            assert(!self.to_vec().view_equal(&other.to_vec()));
            self.to_vec().lemma_serialization_is_not_a_prefix_of(&other.to_vec());
        }
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        self.lemma_to_vec_view(*other);
        self.to_vec().lemma_same_views_serialize_the_same(&other.to_vec());
    }

    proof fn lemma_serialize_injective(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());  // OBSERVE
        }
    }
}

#[allow(non_snake_case)]
pub proof fn lemma_is_marshalable_CKeyHashMap(h: CKeyHashMap)
    requires
        crate::host_protocol_t::valid_hashtable(h@),
    ensures
        h.is_marshalable(),
{
    lemma_auto_spec_u64_to_from_le_bytes();

    assert(h@.dom().len() < 62);
    h.lemma_to_vec();

    let vec = h.spec_to_vec();

    assert(vec.len() < 62);

    let max_len: int = 10_000;

    assert forall|i: int| 0 <= i < vec.len() implies (#[trigger] vec[i].is_marshalable()
        && vec[i].ghost_serialize().len() < max_len) by {
        let (k, v) = vec[i]@;
        assert(h@.contains_pair(k, v));
        assert(h@.dom().contains(k));
        assert(crate::app_interface_t::valid_key(k));
        assert(crate::app_interface_t::valid_value(h@[k]));
        assert(vec[i].is_marshalable());
        assert(vec[i].ghost_serialize().len() < max_len);
    }
    reveal(crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size);

    assert((vec@.len() as usize).ghost_serialize().len() + vec@.fold_left(
        0,
        |acc: int, x: CKeyKV| acc + x.ghost_serialize().len(),
    ) <= 0x100000) by {
        let f = |x: CKeyKV| x.ghost_serialize().len() as int;
        let ag = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len();
        let af = |acc: int, x: CKeyKV| acc + f(x);
        assert forall|i: int| 0 <= i < vec@.len() implies f(vec@[i]) <= max_len by {
            let (k, v) = vec[i]@;
            assert(h@.contains_pair(k, v));
            assert(h@.dom().contains(k));
            assert(crate::app_interface_t::valid_key(k));
            assert(crate::app_interface_t::valid_value(h@[k]));
            assert(vec[i].is_marshalable());
            assert(vec[i].ghost_serialize().len() < max_len);
        }
        lemma_seq_fold_left_sum_le(vec@, 0, max_len, f);
        fun_ext_2(ag, af);
    }
    assert((vec@.len() as usize).ghost_serialize().len() + vec@.fold_left(
        Seq::<u8>::empty(),
        |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize(),
    ).len() <= 0x100000) by {
        let emp = Seq::<u8>::empty();
        let s = |x: CKeyKV| x.ghost_serialize();
        let agl = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len() as int;
        let asl = |acc: int, x: CKeyKV| acc + s(x).len() as int;
        let sg = |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize();
        let sa = |acc: Seq<u8>, x: CKeyKV| acc + s(x);
        lemma_seq_fold_left_append_len_int(vec@, emp, s);
        assert(vec@.fold_left(emp, sa).len() as int == vec@.fold_left(0, asl));
        fun_ext_2(sa, sg);
        assert(vec@.fold_left(emp, sg).len() as int == vec@.fold_left(0, asl));
        fun_ext_2(agl, asl);
        assert(vec@.fold_left(emp, sg).len() == vec@.fold_left(0, agl));
    }
    assert(vec.is_marshalable()) by {
        assert(vec@.len() <= usize::MAX);
        assert(forall|x: CKeyKV| vec@.contains(x) ==> #[trigger] x.is_marshalable());
    }
    assert(crate::hashmap_t::spec_sorted_keys(vec));

    assert(h.is_marshalable());
}

/* $line_count$Proof$ */

derive_marshalable_for_enum! {
    /* $line_count$Proof$ */     pub enum CMessage {
    /* $line_count$Proof$ */         #[tag = 0]
    /* $line_count$Proof$ */         GetRequest{ #[o=o0] k: CKey},
    /* $line_count$Proof$ */         #[tag = 1]
    /* $line_count$Proof$ */         SetRequest{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec<u8>>},
    /* $line_count$Proof$ */         #[tag = 2]
    /* $line_count$Proof$ */         Reply{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec::<u8>> },
    /* $line_count$Proof$ */         #[tag = 3]
    /* $line_count$Proof$ */         Redirect{ #[o=o0] k: CKey, #[o=o1] id: EndPoint },
    /* $line_count$Proof$ */         #[tag = 4]
    /* $line_count$Proof$ */         Shard{ #[o=o0] kr: KeyRange::<CKey>, #[o=o1] recipient: EndPoint },
    /* $line_count$Proof$ */         #[tag = 5]
    /* $line_count$Proof$ */         Delegate{ #[o=o0] range: KeyRange::<CKey>, #[o=o1] h: CKeyHashMap},
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */     [rlimit attr = verifier::rlimit(20)]
    /* $line_count$Proof$ */ }

} // verus!
