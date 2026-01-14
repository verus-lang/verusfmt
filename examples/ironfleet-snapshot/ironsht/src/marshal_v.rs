//! Translates file Distributed/Impl/Common/GenericMarshalling.i.dfy
//!
//! Not really a translation so much as a re-implementation
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::function::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::slice::*;

use crate::verus_extra::choose_v::*;
use crate::verus_extra::clone_v::VerusClone;
use crate::verus_extra::seq_lib_v;
use crate::verus_extra::seq_lib_v::*;

// TODO: possible improvements.
//
// + [2023-02-10] `&[u8]` doesn't have a usable `.len()` in pervasive, so we end up using
//   `Vec<u8>` instead, which may cause an unnecessary runtime overhead.
//
// + [2023-02-10] Verus doesn't have a higher performance Vec constructor; need to do repeated
//   pushes right now.
//
// + [2023-03-31] There is no convenient support for overflow/underflow checking (for example,
//   `checked_add`), would be nice to have them in the standard library.

verus! {

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    exec fn _is_marshalable(&self) -> (res: bool)
        ensures
            res == self.is_marshalable(),
    ;

    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    ;

    exec fn serialized_size(&self) -> (res: usize)
        requires
            self.is_marshalable(),
        ensures
            res as int == self.ghost_serialize().len(),
    ;

    exec fn serialize(&self, data: &mut Vec<u8>)
        requires
            self.is_marshalable(),
        ensures
            data@.len() >= old(data).len(),
            data@.subrange(0, old(data)@.len() as int) == old(data)@,
            data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize(),
    ;

    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
        ensures
            match res {
                Some((x, end)) => {
                    &&& x.is_marshalable()
                    &&& start <= end <= data.len()
                    &&& data@.subrange(start as int, end as int) == x.ghost_serialize()
                },
                None => true,
            },
    ;

    // NB the use of a concrete `view_equal` inside the trait. At the time this module was designed,
    // Verus View behavior wasn't governed by a trait, and using a our own view-like trait wasn't
    // feasible because Verus didn't yet have trait generic bounds.
    spec fn view_equal(&self, other: &Self) -> bool;

    proof fn lemma_view_equal_symmetric(&self, other: &Self)
        ensures
            self.view_equal(other) == other.view_equal(self),
    ;

    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
        requires
            !self.view_equal(other),
            self.ghost_serialize().len() <= other.ghost_serialize().len(),
        ensures
            self.ghost_serialize() != other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ),
    ;

    proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
        requires
            self.view_equal(other),
        ensures
            self.is_marshalable() == other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
    ;

    proof fn lemma_serialize_injective(&self, other: &Self)
        requires
            self.is_marshalable(),
            other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
        ensures
            self.view_equal(other),
    ;
}

#[allow(unused)]
macro_rules! ext_equalities_aux {
  ($s:expr $(,)?) => {};
  ($s1:expr, $s2:expr, $($rest:expr,)* $(,)?) => {verus_proof_expr!{{
    assert($s1 =~= $s2);
    ext_equalities_aux!($s2, $($rest,)*);
  }}};
}

#[allow(unused)]
macro_rules! ext_equalities {
  ($($tt:tt)*) => {
    verus_proof_macro_exprs!(ext_equalities_aux!($($tt)*))
  };
}

impl Marshalable for u64 {
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
        true
    }

    exec fn _is_marshalable(&self) -> (res: bool)
    // req, ens from trait
    {
        true
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        8
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        let s = u64_to_le_bytes(*self);
        let mut i: usize = 0;

        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.ghost_serialize().subrange(0, i as int));
            lemma_auto_spec_u64_to_from_le_bytes();
        }

        while i < 8
            invariant
                0 <= i <= 8,
                s.len() == 8,
                s@ == self.ghost_serialize(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i as int),
                data@.len() == old(data)@.len() + i as int,
        {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) == data@.subrange(
                old(data)@.len() as int,
                old(data)@.len() + i as int,
            ));

            let x: u8 = s[i];
            data.push(x);
            i = i + 1;

            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i as int)) by {
                    assert(self.ghost_serialize().subrange(0, (i - 1) as int).push(x)
                        =~= self.ghost_serialize().subrange(0, i as int));
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize().subrange(0, (i - 1) as int).push(x));
                }
            }
        }
        proof {
            assert(self.ghost_serialize().subrange(0, i as int) =~= self.ghost_serialize());
        }
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }

        if data.len() < 8 {
            return None;
        }
        if start > data.len() - 8 {
            return None;
        }
        let end = start + 8;

        let v = u64_from_le_bytes(slice_subrange(data.as_slice(), start, end));

        Some((v, end))
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
            =~= other.ghost_serialize());
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
    }

    proof fn lemma_serialize_injective(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
    }
}

impl Marshalable for usize {
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
        &&& *self as int <= u64::MAX
    }

    exec fn _is_marshalable(&self) -> (res: bool)
    // req, ens from trait
    {
        *self as u64 <= u64::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        assert((*self as u64).is_marshalable());
        (*self as u64).serialized_size()
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        (*self as u64).serialize(data)
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        let (r, end) = match u64::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        if r <= usize::MAX as u64 {
            let res = r as usize;
            // assert(res.0 as int <= u64::MAX);
            // assert(r.0 as int <= u64::MAX);
            // assert(res.0 as int <= usize::MAX);
            // assert(r.0 as int <= usize::MAX);
            // assert(res.0 as int == r.0 as int);
            Some((res, end))
        } else {
            None
        }
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        (*self as u64).lemma_serialization_is_not_a_prefix_of(&(*other as u64));
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        (*self as u64).lemma_same_views_serialize_the_same(&(*other as u64));
    }

    proof fn lemma_serialize_injective(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        (*self as u64).lemma_serialize_injective(&(*other as u64));
    }
}

impl Marshalable for Vec<u8> {
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
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    exec fn _is_marshalable(&self) -> (res: bool)
    // req, ens from trait
    {
        let len = self.len();
        proof {
            if len <= usize::MAX {
                assert(len.is_marshalable());
            }
        }
        len <= usize::MAX && len.serialized_size() <= usize::MAX - len
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        assert(self.len().is_marshalable());
        self.len().serialized_size() + self.len()
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        let self_len = self.len();
        self_len.serialize(data);
        let init: Ghost<int> = Ghost(self_len.ghost_serialize().len() as int);

        let mut i: usize = 0;

        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.ghost_serialize().subrange(0, i + init@));
        }

        while i < self.len()
            invariant
                0 <= i <= self.len(),
                self.is_marshalable(),
                self.ghost_serialize().len() == init@ + self.len(),
                0 <= i + init@ <= self.ghost_serialize().len(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i + init@),
                data@.len() == old(data)@.len() + i + init@,
        {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) == data@.subrange(
                old(data)@.len() as int,
                old(data)@.len() + i + init@,
            ));

            let x: u8 = self[i];
            data.push(x);
            i = i + 1;

            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i + init@)) by {
                    assert(self.ghost_serialize().subrange(0, (i + init@ - 1) as int).push(x)
                        =~= self.ghost_serialize().subrange(0, i + init@));
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize().subrange(0, (i + init@ - 1) as int).push(x));
                }
            }
        }
        proof {
            assert(self.ghost_serialize().subrange(0, i + init@) =~= self.ghost_serialize());
        }
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        let (len, mid) = match usize::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let len = len as usize;

        // assert(mid <= data.len());
        // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());

        let end = if usize::MAX - mid >= len {
            mid + len
        } else {
            return None;
        };
        if end > data.len() {
            return None;
        }
        // assert(0 <= mid);
        // assert(len >= 0);
        // assert(mid <= end);
        // assert(end <= data.len());

        let res_slice = slice_subrange(data.as_slice(), mid, end);
        let res = slice_to_vec(res_slice);

        // assert(res_slice@ == data@.subrange(mid as int, end as int));
        // assert(res@ == res_slice@);

        // assert(res.ghost_serialize() == usize(len).ghost_serialize() + res@);
        // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());
        // assert(data@.subrange(mid as int, end as int) == res@);

        // assert(0 <= start);
        // assert(start <= mid);
        // assert(mid <= end);
        // assert(end <= data.len());

        proof {
            // We split this part of the proof out into a lemma due to verifier performance issues;
            // with the lemma inlined, the proof failed.
            // This is surprising verifier behavior because the lemma only calls the `assert_seqs_equal!`
            // macro which itself only uses `assert by` which should preclude verifier performance
            // misbehavior.
            seq_lib_v::lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
        }

        Some((res, end))
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self.ghost_serialize().subrange(0, 8) =~= (self@.len() as usize).ghost_serialize());
        assert(other.ghost_serialize().subrange(0, 8) =~= (
        other@.len() as usize).ghost_serialize());
        if self.ghost_serialize().len() == other.ghost_serialize().len() {
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());
            assert(self.ghost_serialize().subrange(8, self.ghost_serialize().len() as int)
                =~= self@);
            assert(other.ghost_serialize().subrange(8, self.ghost_serialize().len() as int)
                =~= other@);
        } else {
            assert(other.len() > self.len());  // OBSERVE
            assert(other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
        }
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
    }

    proof fn lemma_serialize_injective(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self@ =~= self.ghost_serialize().subrange(
            (self@.len() as usize).ghost_serialize().len() as int,
            self.ghost_serialize().len() as int,
        ));
        assert(other@ =~= other.ghost_serialize().subrange(
            (other@.len() as usize).ghost_serialize().len() as int,
            other.ghost_serialize().len() as int,
        ));
    }
}

impl<T: Marshalable> Marshalable for Option<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(s), Some(o)) => s.view_equal(o),
            _ => false,
        }
    }

    proof fn lemma_view_equal_symmetric(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        match (self, other) {
            (None, None) => (),
            (Some(s), Some(o)) => s.lemma_view_equal_symmetric(o),
            _ => (),
        }
    }

    open spec fn is_marshalable(&self) -> bool {
        match self {
            None => true,
            Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
        }
    }

    exec fn _is_marshalable(&self) -> (res: bool)
    // req, ens from trait
    {
        match self {
            None => true,
            Some(x) => x._is_marshalable() && x.serialized_size() <= usize::MAX - 1,
        }
    }

    open spec fn ghost_serialize(&self) -> Seq<u8>
    // req, ens from trait
    {
        match self {
            None => seq![0],
            Some(x) => seq![1] + x.ghost_serialize(),
        }
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        match self {
            None => 1,
            Some(x) => 1 + x.serialized_size(),
        }
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        match self {
            None => {
                data.push(0);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize());
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
            },
            Some(x) => {
                data.push(1);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![1]);
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
                x.serialize(data);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize());
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
            },
        }
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        if data.len() == 0 || start > data.len() - 1 {
            return None;
        }
        let tag = data[start];
        let (x, end) = if tag == 0 {
            let mid = start + 1;
            (None, mid)
        } else if tag == 1 {
            let mid = start + 1;
            let (x, mid) = match T::deserialize(data, mid) {
                None => {
                    return None;
                },
                Some(x) => x,
            };
            (Some(x), mid)
        } else {
            return None;
        };
        proof {
            assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());
        }
        Some((x, end))
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        match (self, other) {
            (None, None) => {},
            (Some(_), None) | (None, Some(_)) => {
                assert(self.ghost_serialize()[0] != other.ghost_serialize()[0]);  // OBSERVE
            },
            (Some(s), Some(o)) => {
                s.lemma_serialization_is_not_a_prefix_of(o);
                assert(s.ghost_serialize() =~= self.ghost_serialize().subrange(
                    1,
                    self.ghost_serialize().len() as int,
                ));
                assert(o.ghost_serialize().subrange(0, s.ghost_serialize().len() as int)
                    =~= other.ghost_serialize().subrange(
                    0,
                    self.ghost_serialize().len() as int,
                ).subrange(1, self.ghost_serialize().len() as int));
            },
        }
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        match (self, other) {
            (Some(s), Some(o)) => s.lemma_same_views_serialize_the_same(o),
            _ => (),
        }
    }

    proof fn lemma_serialize_injective(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        match (self, other) {
            (Some(s), Some(o)) => {
                assert(s.ghost_serialize() =~= self.ghost_serialize().subrange(
                    1,
                    self.ghost_serialize().len() as int,
                ));
                assert(o.ghost_serialize() =~= other.ghost_serialize().subrange(
                    1,
                    other.ghost_serialize().len() as int,
                ));
                s.lemma_serialize_injective(o);
            },
            (None, None) => {},
            (Some(s), None) => {
                assert(other.ghost_serialize()[0] == 0);  // OBSERVE
            },
            (None, Some(o)) => {
                assert(self.ghost_serialize()[0] == 0);  // OBSERVE
            },
        }
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        let s = self@;
        let o = other@;
        s.len() == o.len() && (forall|i: int|
            0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
    }

    proof fn lemma_view_equal_symmetric(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        let s = self@;
        let o = other@;
        if self.view_equal(other) {
            assert forall|i: int| 0 <= i < o.len() implies #[trigger] o[i].view_equal(&s[i]) by {
                s[i].lemma_view_equal_symmetric(&o[i]);
            }
        } else {
            if s.len() != o.len() {
                // trivial
            } else {
                let i = choose|i: int| 0 <= i < s.len() && !#[trigger] s[i].view_equal(&o[i]);
                s[i].lemma_view_equal_symmetric(&o[i]);
            }
        }
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& self@.len() <= usize::MAX
        &&& (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
        &&& (self@.len() as usize).ghost_serialize().len() + self@.fold_left(
            0,
            |acc: int, x: T| acc + x.ghost_serialize().len(),
        ) <= usize::MAX
    }

    exec fn _is_marshalable(&self) -> bool {
        let mut res = true;
        let mut i = 0;
        let mut total_len = self.len().serialized_size();

        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }

        while res && i < self.len()
            invariant
                0 <= i <= self.len(),
                res ==> total_len as int == (self@.len() as usize).ghost_serialize().len()
                    + self@.subrange(0, i as int).fold_left(
                    0,
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                ),
                res ==> (forall|x: T|
                    self@.subrange(0, i as int).contains(x) ==> #[trigger] x.is_marshalable()),
                res ==> total_len as int <= usize::MAX,
                !res ==> !self.is_marshalable(),
        {
            assert(res);
            res =
            res && self[i]._is_marshalable() && (usize::MAX - total_len
                >= self[i].serialized_size());
            if res {
                let old_total_len = total_len;
                total_len = total_len + self[i].serialized_size();
                i = i + 1;
                proof {
                    assert forall|x: T| #[trigger]
                        self@.subrange(0, i as int).contains(x) implies x.is_marshalable() by {
                        if (exists|j: int|
                            0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(
                                0,
                                i as int,
                            )[j] == x) {
                            let j = choose|j: int|
                                0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(
                                    0,
                                    i as int,
                                )[j] == x;
                            assert(self@.subrange(0, i as int - 1)[j] == x);  // OBSERVE
                        }
                    };
                    let sl = |x: T| x.ghost_serialize().len() as int;
                    fun_ext_2::<int, T, int>(
                        |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                        |acc: int, x: T| acc + sl(x),
                    );
                    let s = self@.subrange(0 as int, i as int);
                    seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                    assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i - 1 as int));
                }
            } else {
                proof {
                    if usize::MAX < total_len + self@[i as int].ghost_serialize().len() {
                        assert(((self@.len() as usize).ghost_serialize().len() + self@.fold_left(
                            0,
                            |acc: int, x: T| acc + x.ghost_serialize().len(),
                        )) >= (total_len + self@[i as int].ghost_serialize().len())) by {
                            let f = |x: T| x.ghost_serialize();
                            let sl = |x: T| x.ghost_serialize().len() as int;
                            let s = self@.subrange(0 as int, i as int + 1);
                            fun_ext_2::<int, T, int>(
                                |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                                |acc: int, x: T| acc + sl(x),
                            );
                            seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                            assert(s.subrange(0, s.len() - 1) =~= self@.subrange(
                                0 as int,
                                i as int,
                            ));
                            seq_lib_v::lemma_seq_fold_left_append_len_int_le(
                                self@,
                                i as int + 1,
                                0,
                                f,
                            );
                            fun_ext_2(
                                |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                                |acc: int, x: T| acc + f(x).len(),
                            );
                        };
                    } else {
                        assert(!self@[i as int].is_marshalable());
                    }
                }
            }
        }
        res
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@.fold_left(
            Seq::<u8>::empty(),
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        )
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        let mut res = self.len().serialized_size();
        let mut i = 0;

        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }

        while i < self.len()
            invariant
                0 <= i <= self.len(),
                (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable()),
                (self@.len() as usize).ghost_serialize().len() + self@.subrange(
                    0 as int,
                    self@.len() as int,
                ).fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) <= usize::MAX,
                res == (self@.len() as usize).ghost_serialize().len() + self@.subrange(
                    0 as int,
                    i as int,
                ).fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()),
        {
            proof {
                let f = |x: T| x.ghost_serialize();
                fun_ext_2::<int, T, int>(
                    |acc: int, x: T| acc + f(x).len(),
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                );
                seq_lib_v::lemma_seq_fold_left_append_len_int_le::<T, u8>(
                    self@,
                    i + 1 as int,
                    0,
                    f,
                );
                let sl = |x: T| x.ghost_serialize().len() as int;
                let accl = |acc: int, x: T| acc + x.ghost_serialize().len() as int;
                fun_ext_2::<int, T, int>(accl, |acc: int, x: T| acc + sl(x));
                let s = self@.subrange(0 as int, i + 1 as int);
                seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                assert(s.subrange(0, s.len() - 1 as int) =~= self@.subrange(0 as int, i as int));
                assert(self@.subrange(0 as int, self@.len() as int) =~= self@);
            }
            let old_res: Ghost<usize> = Ghost(res);
            res = res + self[i].serialized_size();
            i = i + 1;
            proof {
                let sl = |x: T| x.ghost_serialize().len() as int;
                fun_ext_2::<int, T, int>(
                    |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                    |acc: int, x: T| acc + sl(x),
                );
                let s = self@.subrange(0 as int, i as int);
                seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i - 1 as int));
            }
        }
        proof {
            let f = |x: T| x.ghost_serialize();
            seq_lib_v::lemma_seq_fold_left_append_len_int::<T, u8>(self@, Seq::<u8>::empty(), f);
            fun_ext_2::<Seq<u8>, T, Seq<u8>>(
                |acc: Seq<u8>, x: T| acc + f(x),
                |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
            );
            fun_ext_2::<int, T, int>(
                |acc: int, x: T| acc + f(x).len(),
                |acc: int, x: T| acc + x.ghost_serialize().len(),
            );
            assert(self@.subrange(0 as int, i as int) =~= self@);
        }

        res
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        let self_len = self.len();
        self_len.serialize(data);
        let init: Ghost<int> = Ghost(self_len.ghost_serialize().len() as int);

        let mut i: usize = 0;

        proof {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                Seq::<u8>::empty(),
                |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
            ));
        }

        while i < self.len()
            invariant
                i <= self.len(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                    Seq::<u8>::empty(),
                    |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
                ),
                forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable(),
                data@.len() >= old(data)@.len(),
        {
            self[i].serialize(data);
            i = i + 1;

            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                    Seq::<u8>::empty(),
                    |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
                )) by {
                    let s = self@;
                    let emp = Seq::<u8>::empty();
                    let accf = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
                    let f = |x: T| x.ghost_serialize();
                    let t = s.subrange(0, i as int);

                    fun_ext_2(accf, |acc: Seq<u8>, x: T| acc + f(x));
                    assert(t.subrange(0, t.len() - 1) =~= s.subrange(0, i - 1));
                    seq_lib_v::lemma_seq_fold_left_append_right(t, emp, f);
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.len().ghost_serialize() + s.subrange(0, (i - 1) as int).fold_left(
                        emp,
                        accf,
                    ) + s.index((i - 1) as int).ghost_serialize());
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.len().ghost_serialize() + t.fold_left(emp, accf));
                }
            }
        }
        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        let (len, mid) = match usize::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let len = len as usize;

        let mut res: Vec<T> = Vec::with_capacity(len);
        let mut i: usize = 0;
        let mut end = mid;

        let emp: Ghost<Seq<u8>> = Ghost(Seq::<u8>::empty());
        let accf: Ghost<spec_fn(Seq<u8>, T) -> Seq<u8>> = Ghost(
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        );

        proof {
            assert(data@.subrange(mid as int, end as int) =~= emp@);
            // assert(emp == seq_lib_v::seq_fold_left(res@, emp@, accf@));

            lemma_auto_spec_u64_to_from_le_bytes();
        }

        while i < len
            invariant
                0 <= i <= len,
                res.is_marshalable(),
                start <= mid <= end <= data@.len(),
                data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@),
                res@.len() == i,
                len.ghost_serialize().len() + res@.fold_left(
                    0,
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                ) == end - start,
                accf@ == |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        {
            let (x, end1) = match T::deserialize(data, end) {
                None => {
                    return None;
                },
                Some(x) => x,
            };

            let old_end: Ghost<int> = Ghost(end as int);
            let old_res: Ghost<Seq<T>> = Ghost(res@);

            res.push(x);
            end = end1;
            i = i + 1;

            assert(data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@)) by {
                let f = |x: T| x.ghost_serialize();
                // assert(data@.subrange(mid as int, old_end@) == seq_lib_v::seq_fold_left(old_res@, emp@, accf@));
                seq_lib_v::lemma_seq_add_subrange::<u8>(data@, mid as int, old_end@, end as int);
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + data@.subrange(old_end@, end as int));
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + x.ghost_serialize());
                // assert(f(x) == x.ghost_serialize());
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + f(x));
                seq_lib_v::lemma_seq_fold_left_append_right(res@, emp@, f);
                assert(accf@ == (|acc: Seq<u8>, x: T| acc + f(x))) by {
                    fun_ext_2(accf@, |acc: Seq<u8>, x: T| acc + f(x));
                }
                assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
                // assert(data@.subrange(mid as int, end as int) == seq_lib_v::seq_fold_left(res@, emp@, accf@));
            }
            assert(len.ghost_serialize().len() + res@.fold_left(
                0,
                |acc: int, x: T| acc + x.ghost_serialize().len(),
            ) == end - start) by {
                let l = |x: T| x.ghost_serialize().len() as int;
                let suml = |acc: int, x: T| acc + l(x);
                seq_lib_v::lemma_seq_fold_left_sum_right(res@, 0, l);
                fun_ext_2(|acc: int, x: T| acc + x.ghost_serialize().len(), suml);
                assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
            }
            assert(len.ghost_serialize().len() == (res@.len() as usize).ghost_serialize().len())
                by {
                lemma_auto_spec_u64_to_from_le_bytes();
            }
        }
        assert(data@.subrange(start as int, end as int) == res.ghost_serialize()) by {
            seq_lib_v::lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
        }
        Some((res, end))
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        if self.len() != other.len() {
            assert(other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
            assert(self.ghost_serialize().subrange(0, 8) =~= (
            self.len() as usize).ghost_serialize());
            assert(other.ghost_serialize().subrange(0, 8) =~= (
            other.len() as usize).ghost_serialize());
        } else {
            let not_view_equal_at_idx = |i: int| !self@[i].view_equal(&other@[i]);
            let idx = {
                let temp = choose|i: int|
                    0 <= i < self@.len() && !#[trigger] self@[i].view_equal(&other@[i]);
                assert(not_view_equal_at_idx(temp));  // OBSERVE
                choose_smallest(0, self@.len() as int, not_view_equal_at_idx)
            };
            let emp = Seq::<u8>::empty();
            let g = |x: T| x.ghost_serialize();
            let accg = |acc: Seq<u8>, x: T| acc + g(x);
            let accgs = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
            let gs = |s: Seq<T>, start: int, end: int| s.subrange(start, end).fold_left(emp, accg);
            fun_ext_2(accg, accgs);
            assert(self.ghost_serialize() =~= ((self@.len() as usize).ghost_serialize() + gs(
                self@,
                0,
                idx,
            )) + g(self@[idx]) + gs(self@, idx + 1, self.len() as int)) by {
                assert(gs(self@, 0, self.len() as int) == gs(self@, 0, idx) + gs(
                    self@,
                    idx,
                    self.len() as int,
                )) by {
                    let s1 = self@.subrange(0, idx);
                    let s2 = self@.subrange(idx, self.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(self@.subrange(0, self.len() as int) =~= s1 + s2);
                }
                assert(gs(self@, idx, self.len() as int) == g(self@[idx]) + gs(
                    self@,
                    idx + 1,
                    self.len() as int,
                )) by {
                    let s1 = self@.subrange(idx, idx + 1);
                    let s2 = self@.subrange(idx + 1, self.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(self@.subrange(idx, self.len() as int) =~= s1 + s2);
                    assert(self@.subrange(idx, idx + 1) =~= seq![self@[idx]]);
                    reveal_with_fuel(Seq::fold_left, 2);
                    assert(emp + g(self@[idx]) =~= g(self@[idx]));
                }
                assert((self@.len() as usize).ghost_serialize() + gs(self@, 0, self.len() as int)
                    == self.ghost_serialize()) by {
                    assert(self@.subrange(0, self.len() as int) =~= self@);
                }
            }
            assert(other.ghost_serialize() =~= ((other@.len() as usize).ghost_serialize() + gs(
                other@,
                0,
                idx,
            )) + g(other@[idx]) + gs(other@, idx + 1, other.len() as int)) by {
                assert(gs(other@, 0, other.len() as int) == gs(other@, 0, idx) + gs(
                    other@,
                    idx,
                    other.len() as int,
                )) by {
                    let s1 = other@.subrange(0, idx);
                    let s2 = other@.subrange(idx, other.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(other@.subrange(0, other.len() as int) =~= s1 + s2);
                }
                assert(gs(other@, idx, other.len() as int) == g(other@[idx]) + gs(
                    other@,
                    idx + 1,
                    other.len() as int,
                )) by {
                    let s1 = other@.subrange(idx, idx + 1);
                    let s2 = other@.subrange(idx + 1, other.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(other@.subrange(idx, other.len() as int) =~= s1 + s2);
                    assert(other@.subrange(idx, idx + 1) =~= seq![other@[idx]]);
                    reveal_with_fuel(Seq::fold_left, 2);
                    assert(emp + g(other@[idx]) =~= g(other@[idx]));
                }
                assert((other@.len() as usize).ghost_serialize() + gs(other@, 0, other.len() as int)
                    == other.ghost_serialize()) by {
                    assert(other@.subrange(0, other.len() as int) =~= other@);
                }
            }
            assert((self@.len() as usize).ghost_serialize() == (
            other@.len() as usize).ghost_serialize());
            assert(gs(self@, 0, idx) == gs(other@, 0, idx)) by {
                assert forall|i: int| 0 <= i < idx implies g(self@.subrange(0, idx)[i]) == g(
                    other@.subrange(0, idx)[i],
                ) by {
                    assert(self@.subrange(0, idx)[i] == self@[i] && other@.subrange(0, idx)[i]
                        == other@[i]);
                    assert(!not_view_equal_at_idx(i));
                    self@[i].lemma_same_views_serialize_the_same(&other@[i]);
                }
                lemma_fold_left_on_equiv_seqs(
                    self@.subrange(0, idx),
                    other@.subrange(0, idx),
                    |x: T, y: T| g(x) == g(y),
                    emp,
                    accg,
                );
            }
            assert(((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)) == ((
            other@.len() as usize).ghost_serialize() + gs(other@, 0, idx)));
            let prefix_len = ((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)).len();
            let i = if g(self@[idx]).len() <= g(other@[idx]).len() {
                self@[idx].lemma_serialization_is_not_a_prefix_of(&other@[idx]);
                some_differing_index_for_unequal_seqs(
                    g(self@[idx]),
                    g(other@[idx]).subrange(0, g(self@[idx]).len() as int),
                )
            } else {
                self@[idx].lemma_view_equal_symmetric(&other@[idx]);
                other@[idx].lemma_serialization_is_not_a_prefix_of(&self@[idx]);
                some_differing_index_for_unequal_seqs(
                    g(other@[idx]),
                    g(self@[idx]).subrange(0, g(other@[idx]).len() as int),
                )
            };
            assert(g(self@[idx])[i] != g(other@[idx])[i]);
            assert(self.ghost_serialize()[prefix_len + i] != other.ghost_serialize()[prefix_len
                + i]);
            assert(self.ghost_serialize() != other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ));
        }
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self@.len() == other@.len());
        assert forall|i: int| 0 <= i < self@.len() implies #[trigger] self@[i].is_marshalable()
            == other@[i].is_marshalable() && #[trigger] self@[i].ghost_serialize()
            == other@[i].ghost_serialize() by {
            self@[i].lemma_same_views_serialize_the_same(&other@[i]);
        }
        let veq = |x: T, y: T| x.view_equal(&y);
        assert(self.is_marshalable() == other.is_marshalable()) by {
            assert((self@.len() <= usize::MAX) == (other@.len() <= usize::MAX));
            if (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable()) {
                assert forall|y: T| other@.contains(y) implies #[trigger] y.is_marshalable() by {
                    let i = choose|i: int| 0 <= i < other@.len() && other@[i] == y;
                    self@[i].lemma_same_views_serialize_the_same(&other@[i]);
                }
            } else {
                let i = choose|i: int|
                    0 <= i < self@.len() && !(#[trigger] self@[i].is_marshalable());
                self@[i].lemma_same_views_serialize_the_same(&other@[i]);
            }
            assert((self@.len() as usize).ghost_serialize().len() == (
            other@.len() as usize).ghost_serialize().len());
            let f = |acc: int, x: T| acc + x.ghost_serialize().len();
            assert forall|b: int, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger] f(b, a1)
                == f(b, a2) by {
                a1.lemma_same_views_serialize_the_same(&a2);
            }
            seq_lib_v::lemma_fold_left_on_equiv_seqs(self@, other@, veq, 0, f);
            assert(self@.fold_left(0, f) == other@.fold_left(0, f));
        };
        assert(self.ghost_serialize() == other.ghost_serialize()) by {
            let f = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
            assert forall|b: Seq<u8>, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger] f(
                b,
                a1,
            ) == f(b, a2) by {
                a1.lemma_same_views_serialize_the_same(&a2);
            }
            seq_lib_v::lemma_fold_left_on_equiv_seqs(self@, other@, veq, Seq::<u8>::empty(), f);
        }
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

// NOTE: This can be replaced with a `define_struct_and_derive_marshalable` invocation
impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self.0.view_equal(&other.0) && self.1.view_equal(&other.1)
    }

    proof fn lemma_view_equal_symmetric(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        self.0.lemma_view_equal_symmetric(&other.0);
        self.1.lemma_view_equal_symmetric(&other.1);
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& self.0.is_marshalable()
        &&& self.1.is_marshalable()
        &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
    }

    exec fn _is_marshalable(&self) -> bool
    // req, ens from trait
    {
        self.0._is_marshalable() && self.1._is_marshalable() && self.0.serialized_size()
            <= usize::MAX - self.1.serialized_size()
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        self.0.ghost_serialize() + self.1.ghost_serialize()
    }

    exec fn serialized_size(&self) -> (res: usize)
    // req, ens from trait
    {
        self.0.serialized_size() + self.1.serialized_size()
    }

    exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
    {
        self.0.serialize(data);
        // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);

        let mid_data_len: Ghost<int> = Ghost(data@.len() as int);

        self.1.serialize(data);

        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= data@.subrange(
                0,
                mid_data_len@,
            ).subrange(0, old(data)@.len() as int));
            // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);
            assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= data@.subrange(
                0,
                mid_data_len@,
            ).subrange(old(data)@.len() as int, mid_data_len@));
            // assert(data@.subrange(old(data)@.len() as int, mid_data_len@) == self.0.ghost_serialize());
            // assert(data@.subrange(mid_data_len@, data@.len() as int) == self.1.ghost_serialize());
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.0.ghost_serialize() + self.1.ghost_serialize());
        }
    }

    exec fn deserialize(
        data: &Vec<u8>,
        start: usize,
    ) -> (res: Option<(Self, usize)>)
    // req, ens from trait
    {
        let (t, mid) = match T::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let (u, end) = match U::deserialize(data, mid) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let p = (t, u);
        proof {
            assert(data@.subrange(start as int, end as int) =~= p.ghost_serialize());
        }
        Some((p, end))
    }

    proof fn lemma_serialization_is_not_a_prefix_of(
        &self,
        other: &Self,
    )
    // req, ens from trait
    {
        let si = self.ghost_serialize();
        let so = other.ghost_serialize();
        let mid: int = 0;
        if !self.0.view_equal(&other.0) {
            let (x0, x1) = (self.0, other.0);
            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
            x0.lemma_view_equal_symmetric(&x1);
            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
            } else {
                (x1, x0, s1, s0)
            };
            x0.lemma_serialization_is_not_a_prefix_of(&x1);
            assert(!(s0 =~= s1.subrange(0, s0.len() as int)));  // OBSERVE
            let idx = choose|i: int| 0 <= i < s0.len() as int && s0[i] != s1[i];
            if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]);  // OBSERVE
            }
            return ;
        } else {
            self.0.lemma_same_views_serialize_the_same(&other.0);
        }
        let mid = mid + self.0.ghost_serialize().len();
        if !self.1.view_equal(&other.1) {
            let (x0, x1) = (self.1, other.1);
            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
            x0.lemma_view_equal_symmetric(&x1);
            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
            } else {
                (x1, x0, s1, s0)
            };
            x0.lemma_serialization_is_not_a_prefix_of(&x1);
            assert(!(s0 =~= s1.subrange(0, s0.len() as int)));  // OBSERVE
            let idx = choose|i: int| 0 <= i < s0.len() as int && s0[i] != s1[i];
            if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]);  // OBSERVE
            }
            return ;
        } else {
            self.1.lemma_same_views_serialize_the_same(&other.1);
        }
    }

    proof fn lemma_same_views_serialize_the_same(
        self: &Self,
        other: &Self,
    )
    // req, ens from trait
    {
        self.0.lemma_same_views_serialize_the_same(&other.0);
        self.1.lemma_same_views_serialize_the_same(&other.1);
    }

    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());  // OBSERVE
        }
    }
}

/// A convenience macro to produce the triangle necessary to confirm that there are no overflows
/// that occur when adding up a bunch of different expressions together.
#[allow(unused_macros)]
macro_rules! no_usize_overflows {
  ($e:expr,) => {
    true
  };
  ($($e:expr),*) => {
    no_usize_overflows!(@@internal 0, $($e),*)
  };
  (@@internal $total:expr,) => {
    true
  };
  (@@internal $total:expr, $a:expr) => {
    usize::MAX - $total >= $a
  };
  (@@internal $total:expr, $a:expr, $($rest:expr),*) => {
    usize::MAX - $total >= $a
      &&
    no_usize_overflows!(@@internal ($total + $a), $($rest),*)
  };
}

pub(crate) use no_usize_overflows;

/// `derive_marshalable_for_struct` is a macro that implements [`Marshalable`] for a struct. You
/// probably want to use [`define_struct_and_derive_marshalable`] wherever possible instead, since
/// it prevents code duplication. However, if you are (for some reason) unable to define at the
/// struct definition site, then this macro lets you derive the macro by simply (textually)
/// copy-pasting the struct.
#[allow(unused_macros)]
macro_rules! derive_marshalable_for_struct {
  {
    $( #[$attr:meta] )*
    $pub:vis
    struct $newstruct:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        $fieldvis:vis $field:ident : $fieldty:ty
      ),+
      $(,)?
    }
  } => {
    ::builtin_macros::verus! {
      impl $(< $($poly: Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? {
        open spec fn view_equal(&self, other: &Self) -> bool {
          $(
            &&& self.$field.view_equal(&other.$field)
          )*
        }
        proof fn lemma_view_equal_symmetric(&self, other: &Self)
        // req, ens from trait
        {
          $(
            self.$field.lemma_view_equal_symmetric(&other.$field);
          )*
        }
        open spec fn is_marshalable(&self) -> bool {
          $(
            &&& self.$field.is_marshalable()
          )*
          &&& 0 $(+ self.$field.ghost_serialize().len())* <= usize::MAX
        }
        exec fn _is_marshalable(&self) -> bool
          // req, ens from trait
        {
          $(
            &&& self.$field._is_marshalable()
          )*
          &&& no_usize_overflows!($((self.$field.serialized_size())),*)
        }
        open spec fn ghost_serialize(&self) -> Seq<u8> {
          Seq::empty() $(+ self.$field.ghost_serialize())*
        }
        exec fn serialized_size(&self) -> (res: usize)
          // req, ens from trait
        {
          0 $(+ self.$field.serialized_size())*
        }
        exec fn serialize(&self, data: &mut Vec<u8>)
          // req, ens from trait
        {
          $(self.$field.serialize(data);)*
          proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());
          }
        }
        exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
          // req, ens from trait
        {
          let mid = start;
          $(
            let ($field, mid) = match $fieldty::deserialize(data, mid) { None => {
              return None;
            }, Some(x) => x, };
          )*
          let end = mid;
          let res = $newstruct {
            $($field),+
          };
          proof {
            assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());
          }
          Some((res, end))
        }
        proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
        // req, ens from trait
        {
          let si = self.ghost_serialize();
          let so = other.ghost_serialize();
          let mid: int = 0;
          $(
            if !self.$field.view_equal(&other.$field) {
              let (x0, x1) = (self.$field, other.$field);
              let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
              x0.lemma_view_equal_symmetric(&x1);
              let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
              } else {
                (x1, x0, s1, s0)
              };
              x0.lemma_serialization_is_not_a_prefix_of(&x1);
              assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE
              let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];
              if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]); // OBSERVE
              }
              return;
            } else {
              self.$field.lemma_same_views_serialize_the_same(&other.$field);
            }
            let mid = mid + self.$field.ghost_serialize().len();
          )*
        }
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
        // req, ens from trait
        {
          $(
            self.$field.lemma_same_views_serialize_the_same(&other.$field);
          )*
        }
        proof fn lemma_serialize_injective(self: &Self, other: &Self) {
          if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                   =~= other.ghost_serialize()); // OBSERVE
          }
        }
      }
    }
  };
}

pub(crate) use derive_marshalable_for_struct;

/// `define_struct_and_derive_marshalable` is a macro that, well, defines an struct, and implements
/// [`Marshalable`] on it. This is intended to make it easier to produce serializers and
/// deserializers for arbitrary types (including polymorphic ones).
///
/// See also [`define_enum_and_derive_marshalable`] for the equivalent enum-based macro.
///
/// Example usage:
///
/// ```
/// define_struct_and_derive_marshalable! {
///   struct Example<T: Marshalable, U: Marshalable> {
///     t: T,
///     u: U,
///     v: Vec::<u8>,
///   }
/// }
/// ```
#[allow(unused_macros)]
macro_rules! define_struct_and_derive_marshalable {
  {
    $( #[$attr:meta] )*
    $pub:vis
    struct $newstruct:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        $fieldvis:vis $field:ident : $fieldty:ty
      ),+
      $(,)?
    }
  } => {

    // We first re-generate the struct definition itself, so that the struct exists
    ::builtin_macros::verus! {
    $( #[$attr] )*
    $pub
    struct $newstruct $(< $($poly : Marshalable),+ >)? {
      $($fieldvis $field : $fieldty),+
    }
    }

    // ..and then implement `Marshalable` on it.
    derive_marshalable_for_struct! {
      $( #[$attr] )*
      $pub
      struct $newstruct $(< $($poly : Marshalable),+ >)? {
        $($fieldvis $field : $fieldty),+
      }
    }

  };
}

pub(crate) use define_struct_and_derive_marshalable;

/// `derive_marshalable_for_enum` is a macro that implements [`Marshalable`] for a enum. You
/// probably want to use [`define_enum_and_derive_marshalable`] wherever possible instead, since it
/// prevents code duplication. However, if you are (for some reason) unable to define at the enum
/// definition site, then this macro lets you derive the macro by simply (textually) copy-pasting
/// the enum.
macro_rules! derive_marshalable_for_enum {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
    $( [rlimit attr = $rlimitattr:meta] )?
  } => {
    ::builtin_macros::verus! {
      impl $(< $($poly : Marshalable),+ >)? Marshalable for $newenum $(< $($poly),+ >)? {
        open spec fn view_equal(&self, other: &Self) -> bool {
          &&& match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $(&&& $member.view_equal($memother))* )?
                &&& true
              }
            ),+
            _ => false,
          }
        }
        proof fn lemma_view_equal_symmetric(&self, other: &Self)
        // req, ens from trait
        {
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $($member.lemma_view_equal_symmetric($memother);)* )?
              }
            ),+
            _ => (),
          }
        }
        open spec fn is_marshalable(&self) -> bool {
          &&& match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                $( $(&&& $member.is_marshalable())* )?
                &&& 1 $( $(+ $member.ghost_serialize().len())* )? <= usize::MAX
              }
            ),+
          }
        }
        exec fn _is_marshalable(&self) -> bool {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                &&& true
                $( $(&&& $member._is_marshalable())* )?
                $( &&& no_usize_overflows!(1, $($member.serialized_size()),*) )?
              }
            ),+
          }
        }
        open spec fn ghost_serialize(&self) -> Seq<u8> {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                seq![$tag] $( $(+ $member.ghost_serialize())* )?
              }
            ),*
          }
        }
        exec fn serialized_size(&self) -> (res: usize)
          // req, ens from trait
        {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                1 $( $(+ $member.serialized_size())* )?
              }
            ),*
          }
        }
        $( #[$rlimitattr] )?
        exec fn serialize(&self, data: &mut Vec<u8>)
          // req, ens from trait
        {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                data.push($tag);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                $( $(
                  proof {
                    assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![$tag]);
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                  }
                  $member.serialize(data);
                )* )?
                proof {
                  assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());
                  assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
              }
            ),*
          }
        }
        $( #[$rlimitattr] )?
        exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
          // req, ens from trait
        {
          if data.len() == 0 || start >= data.len() - 1 {
            return None;
          }
          let tag = data[start];
          let (x, end) = $(
            if tag == $tag {
              let mid = start + 1;
              $( $(
                let ($member, mid) = match $memberty::deserialize(data, mid) { None => {
                  return None;
                }, Some(x) => x, };
              )* )?
              ($newenum::$variant $( { $($member),* } )?, mid)
            } else
          )* {
            return None;
          };
          proof {
            assert(data@.subrange(start as int, end as int) == x.ghost_serialize()) by {
                assert(data@.subrange(start as int, end as int).len() == x.ghost_serialize().len());
                assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());
            }
          }
          Some((x, end))
        }
        proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
        // req, ens from trait
        {
          let si = self.ghost_serialize();
          let so = other.ghost_serialize();
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                let mid: int = 1;
                $($(
                  if !$member.view_equal(&$memother) {
                    let (x0, x1) = ($member, $memother);
                    let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
                    x0.lemma_view_equal_symmetric(&x1);
                    let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                      (x0, x1, s0, s1)
                    } else {
                      (x1, x0, s1, s0)
                    };
                    x0.lemma_serialization_is_not_a_prefix_of(&x1);
                    assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE
                    let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];
                    if si == so.subrange(0, si.len() as int) {
                      assert(si[mid + idx] == so[mid + idx]); // OBSERVE
                    }
                    return;
                  } else {
                    $member.lemma_same_views_serialize_the_same(&$memother);
                  }
                  let mid = mid + $member.ghost_serialize().len();
                )*)?
              }
            ),+
            _ => {
              if si == so.subrange(0, si.len() as int) {
                assert(si[0] == so[0]); // OBSERVE
              }
            },
          }
        }
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
        // req, ens from trait
        {
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $($member.lemma_same_views_serialize_the_same($memother);)* )?
              }
            ),+
            _ => (),
          }
        }
        proof fn lemma_serialize_injective(self: &Self, other: &Self)
          // req, ens from trait
        {
          if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                   =~= other.ghost_serialize()); // OBSERVE
          }
        }
      }
    }
  };
}

pub(crate) use derive_marshalable_for_enum;

/// `define_enum_and_derive_marshalable` is a macro that, well, defines an enum, and implements
/// [`Marshalable`] on it. This is intended to make it easier to produce serializers and
/// deserializers for arbitrary types (including polymorphic ones).
///
/// It currently supports enums that have a maximum of 256 variants, since it uses a 1-byte tag to
/// pick between the variants.
///
/// See also [`define_struct_and_derive_marshalable`] for the equivalent struct-based macro.
///
/// Example usage:
///
/// ```
/// define_enum_and_derive_marshalable! {
///   enum Example<T: Marshalable, U: Marshalable> {
///     #[tag = 0]
///     U { u: u64, v: u64, x: Vec::<u8>, z: T },
///     #[tag = 1]
///     V { zz: U },
///   }
/// }
/// ```
///
/// Note: Currently due to https://github.com/verus-lang/verus/issues/444, passingly only a
/// single-variant enum will cause Verus to panic. But if you wanted just one variant, why are you
/// wasting a byte in the serialized output? Just use [`define_struct_and_derive_marshalable`]
/// instead!
#[allow(unused_macros)]
macro_rules! define_enum_and_derive_marshalable {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
    $( [rlimit attr = $rlimitattr:meta] )?
  } => {

    // We first re-generate the enum definition itself, so that the enum exists
    ::builtin_macros::verus! {
    $( #[$attr] )*
    $pub
    enum $newenum $(< $($poly : Marshalable),+ >)? {
      $($variant $( { $($member : $memberty),* } )?),+
    }
    }

    // ..and then implement `Marshalable` on it.
    derive_marshalable_for_enum! {
      $( #[$attr] )*
      $pub
      enum $newenum $(< $($poly : Marshalable),+ >)? {
        $(
          #[tag = $tag]
          $variant $( { $(#[o=$memother] $member : $memberty),* } )?
        ),+
      }
      $( [rlimit attr = $rlimitattr] )?
    }
  };
}

pub(crate) use define_enum_and_derive_marshalable;

/// A macro that conveniently lets one produce a marshaler for a type `$type` by showing a
/// bijection to another (already known to be marshalable) type `$marshalable`.
///
/// This macro only needs to be provided with a forward and backward function (and a few new
/// identifiers, just to keep things distinct from things already known) and it'll produce
/// everything necessary to make the type marshalable.
#[allow(unused_macros)]
macro_rules! marshalable_by_bijection {
    {
        [$type:ty] <-> [$marshalable:ty];
        forward ($self:ident) $forward:expr;
        backward ($m:ident) $backward:expr;
    }
    =>
    {
        ::builtin_macros::verus! {
            impl $type {
                 pub open spec fn forward_bijection_for_view_equality_do_not_use_for_anything_else($self: Self) -> $marshalable {
                  $forward
                }
            }
            impl Marshalable for $type {
                open spec fn view_equal(&self, other: &Self) -> bool {
                    self.forward_bijection_for_view_equality_do_not_use_for_anything_else().view_equal(
                      &other.forward_bijection_for_view_equality_do_not_use_for_anything_else())
                }
                proof fn lemma_view_equal_symmetric(&self, other: &Self)
                  // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_view_equal_symmetric(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else())
                }
                open spec fn is_marshalable($self: &Self) -> bool {
                    $forward.is_marshalable()
                }
                exec fn _is_marshalable($self: &Self) -> (res: bool)
                // req, ens from trait
                {
                    $forward._is_marshalable()
                }
                open spec fn ghost_serialize($self: &Self) -> Seq<u8>
                // req, ens from trait
                {
                    $forward.ghost_serialize()
                }
                exec fn serialized_size($self: &Self) -> (res: usize)
                // req, ens from trait
                {
                    $forward.serialized_size()
                }
                exec fn serialize($self: &Self, data: &mut Vec<u8>)
                // req, ens from trait
                {
                    $forward.serialize(data)
                }
                exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
                // req, ens from trait
                {
                    match <$marshalable>::deserialize(data, start) {
                        None => None,
                        Some(($m, end)) => {
                            Some(($backward, end))
                        }
                    }
                }
                proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
                // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_serialization_is_not_a_prefix_of(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else()
                  );
                }
                proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
                // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_same_views_serialize_the_same(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else()
                  );
                }
                proof fn lemma_serialize_injective(self: &Self, other: &Self)
                // req, ens from trait
                {
                  if !self.view_equal(other) {
                    self.lemma_serialization_is_not_a_prefix_of(other);
                    assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                           =~= other.ghost_serialize()); // OBSERVE
                  }
                }
            }
        }
    };
}

pub(crate) use marshalable_by_bijection;

} // verus!
