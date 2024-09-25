//! Translates file Distributed/Impl/SHT/Delegations.i.dfy
use builtin_macros::*;

use builtin::*;

use vstd::prelude::*;
use vstd::{map::*, modes::*, seq::*, seq_lib::*, set::*, set_lib::*, *};

use crate::abstract_end_point_t::AbstractEndPoint;
use crate::delegation_map_t::*;
use crate::io_t::EndPoint;
use crate::keys_t::*;
use crate::seq_is_unique_v::*;
use crate::verus_extra::clone_v::*;

verus! {

impl Ordering {
    pub open spec fn eq(self) -> bool {
        matches!(self, Ordering::Equal)
    }

    pub open spec fn ne(self) -> bool {
        !matches!(self, Ordering::Equal)
    }

    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }

    pub open spec fn gt(self) -> bool {
        matches!(self, Ordering::Greater)
    }

    pub open spec fn le(self) -> bool {
        !matches!(self, Ordering::Greater)
    }

    pub open spec fn ge(self) -> bool {
        !matches!(self, Ordering::Less)
    }

    pub fn is_eq(self) -> (b: bool)
        ensures
            b == self.eq(),
    {
        matches!(self, Ordering::Equal)
    }

    pub fn is_ne(self) -> (b: bool)
        ensures
            b == self.ne(),
    {
        !matches!(self, Ordering::Equal)
    }

    pub const fn is_lt(self) -> (b: bool)
        ensures
            b == self.lt(),
    {
        matches!(self, Ordering::Less)
    }

    pub const fn is_gt(self) -> (b: bool)
        ensures
            b == self.gt(),
    {
        matches!(self, Ordering::Greater)
    }

    pub const fn is_le(self) -> (b: bool)
        ensures
            b == self.le(),
    {
        !matches!(self, Ordering::Greater)
    }

    pub const fn is_ge(self) -> (b: bool)
        ensures
            b == self.ge(),
    {
        !matches!(self, Ordering::Less)
    }
}

// Stores the entries from smallest to largest
struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

/*
proof fn sorted_subrange<K: KeyTrait>(s: Seq<K>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        sorted(s),
    ensures
        sorted(s.subrange(i, j)),
{
    let sub = s.subrange(i, j);
    assert forall |m, n| 0 <= m < n < sub.len() implies #[trigger](sub[m].cmp_spec(sub[n]).lt()) by {
        K::cmp_properties();
    }
}
*/

impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {
    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }

    proof fn to_set(self) -> (s: Set<K>)
        requires
            self.valid(),
        ensures
            s == self@.to_set(),
            s.finite(),
            s.len() == self@.len(),
    {
        seq_to_set_is_finite::<K>(self@);
        self@.unique_seq_to_set();
        self@.to_set()
    }

    fn new() -> (v: Self)
        ensures
            v@ == Seq::<K>::empty(),
            v.valid(),
    {
        StrictlyOrderedVec { v: Vec::new() }
    }

    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    {
        self.v.len()
    }

    // TODO(parno): returning an &K is a bit more Rusty (and faster!)
    fn index(&self, i: usize) -> (k: K)
        requires
            i < self@.len(),
        ensures
            k == self@[i as int],
    {
        (self.v[i]).clone()
    }

    fn set(&mut self, i: usize, k: K)
        requires
            old(self).valid(),
            i < old(self)@.len(),
            i > 0 ==> old(self)@[i as int - 1].cmp_spec(k).lt(),
            i < old(self)@.len() - 1 ==> k.cmp_spec(old(self)@[i as int + 1]).lt(),
        ensures
            self.valid(),
            self@ == old(self)@.update(i as int, k),
    {
        self.v.set(i, k);
        assert forall|m, n| 0 <= m < n < self@.len() implies #[trigger] (self@[m].cmp_spec(
            self@[n],
        ).lt()) by {
            K::cmp_properties();
        }
        assert forall|i, j| 0 <= i < self@.len() && 0 <= j < self@.len() && i != j implies self@[i]
            != self@[j] by {
            K::cmp_properties();
        }
    }

    fn remove(&mut self, i: usize) -> (k: K)
        requires
            old(self).valid(),
            i < old(self)@.len(),
        ensures
            self.valid(),
            k == old(self)@.index(i as int),
            self@ == old(self)@.remove(i as int),
            self@.to_set() == old(self)@.to_set().remove(k),
    {
        let k = self.v.remove(i);
        proof {
            let old_s = old(self)@.to_set().remove(k);
            let new_s = self@.to_set();
            assert forall|e| old_s.contains(e) implies new_s.contains(e) by {
                assert(old(self)@.to_set().contains(e));
                let n = choose|n: int| 0 <= n < old(self)@.len() && old(self)@[n] == e;
                if n < i {
                    assert(self@[n] == e);  // OBSERVE
                } else {
                    assert(self@[n - 1] == e);  // OBSERVE
                }
            }
            assert_sets_equal!(self@.to_set(), old(self)@.to_set().remove(k));
        }
        k
    }

    /// Remove entries in the range [start, end)
    fn erase(&mut self, start: usize, end: usize)
        requires
            old(self).valid(),
            start <= end <= old(self)@.len(),
        ensures
            self.valid(),
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(
                end as int,
                old(self)@.len() as int,
            ),
            // TODO: We might want to strengthen this further to say that the two sets on the RHS
            //       are disjoint
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(
                start as int,
                end as int,
            ).to_set(),
    {
        let mut deleted = 0;
        let ghost mut deleted_set;
        proof {
            deleted_set = Set::empty();
            assert_seqs_equal!(self@,
                               old(self)@.subrange(0, start as int) +
                               old(self)@.subrange(start as int + deleted as int,
                                                   old(self)@.len() as int));
            assert_sets_equal!(deleted_set,
                               old(self)@.subrange(start as int,
                                                   start as int + deleted as int).to_set());
            assert_sets_equal!(old(self)@.to_set(),
                               self@.to_set() + deleted_set);
        }
        while deleted < end - start
            invariant
                start <= end <= old(self)@.len(),
                self@.len() == old(self)@.len() - deleted,
                0 <= deleted <= end - start,
                old(self).valid(),
                self.valid(),
                self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(
                    start as int + deleted as int,
                    old(self)@.len() as int,
                ),
                deleted_set == old(self)@.subrange(
                    start as int,
                    start as int + deleted as int,
                ).to_set(),
                deleted_set.len() == deleted,
                old(self)@.to_set() == self@.to_set() + deleted_set,
        {
            let ghost mut old_deleted_set;
            let ghost mut old_deleted_seq;
            let ghost mut target;
            proof {
                old_deleted_set = deleted_set;
                old_deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                target = self@[start as int];
                deleted_set = deleted_set.insert(self@[start as int]);
            }
            self.remove(start);
            deleted = deleted + 1;
            proof {
                assert_seqs_equal!(self@,
                                   old(self)@.subrange(0, start as int) +
                                   old(self)@.subrange(start as int + deleted as int,
                                                       old(self)@.len() as int));
                let deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                seq_to_set_is_finite::<K>(deleted_seq);
                deleted_seq.unique_seq_to_set();

                assert forall|e| #[trigger]
                    deleted_set.contains(e) implies deleted_seq.to_set().contains(e) by {
                    if e == target {
                        assert(deleted_seq[deleted as int - 1] == e);  // OBSERVE
                    } else {
                        assert(old_deleted_set.contains(e));
                        assert(old_deleted_seq.contains(e));
                        let i = choose|i| 0 <= i < old_deleted_seq.len() && old_deleted_seq[i] == e;
                        assert(deleted_seq[i] == e);  // OBSERVE
                    }
                }
                assert forall|e| #[trigger]
                    deleted_seq.to_set().contains(e) implies deleted_set.contains(e) by {
                    if e == target {
                    } else {
                        let i = choose|i| 0 <= i < deleted_seq.len() && deleted_seq[i] == e;
                        assert(old_deleted_seq[i] == e);  // OBSERVE
                    }
                }
                assert_sets_equal!(deleted_set,
                                   deleted_seq.to_set());
                assert_sets_equal!(old(self)@.to_set(),
                                   self@.to_set() + deleted_set);
            }
        }
    }

    fn insert(&mut self, k: K) -> (i: usize)
        requires
            old(self).valid(),
            !old(self)@.contains(k),
        ensures
            self.valid(),
            self@.len() == old(self)@.len() + 1,
            0 <= i < self@.len(),
            self@ == old(self)@.insert(i as int, k),
            self@.to_set() == old(self)@.to_set().insert(k),
    {
        // Find the index where we should insert k
        let mut index: usize = 0;
        while index < self.v.len() && self.v[index].cmp(&k).is_lt()
            invariant
                0 <= index <= self@.len(),
                forall|i| 0 <= i < index ==> (#[trigger] self@.index(i).cmp_spec(k)).lt(),
        {
            index = index + 1;
        }
        self.v.insert(index, k);
        assert forall|m, n| 0 <= m < n < self@.len() implies #[trigger] (self@[m].cmp_spec(
            self@[n],
        ).lt()) by {
            K::cmp_properties();
        }
        assert(self@.to_set() == old(self)@.to_set().insert(k)) by {
            let new_s = self@.to_set();
            let old_s = old(self)@.to_set().insert(k);
            assert(self@[index as int] == k);  // OBSERVE
            assert forall|e| old_s.contains(e) implies new_s.contains(e) by {
                if e == k {
                } else {
                    let i = choose|i: int| 0 <= i < old(self)@.len() && old(self)@[i] == e;
                    if i < index {
                        assert(self@[i] == e);  // OBSERVE
                    } else {
                        assert(self@[i + 1] == e);  // OBSERVE
                    }
                }
            };
            assert_sets_equal!(new_s, old_s);
        };
        return index;
    }
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    // #[verifier(when_used_as_spec(new_spec))]
    pub fn new(k: K) -> (s: Self)
        ensures
            s.k == Some(k),
    {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }

    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures
            s.k.is_None(),
    {
        KeyIterator { k: None }
    }

    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures
            b == self.is_end_spec(),
    {
        matches!(self.k, None)
    }

    pub open spec fn get_spec(&self) -> &K
        recommends
            self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires
            !self.is_end(),
        ensures
            k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }

    //    fn cmp(&self, other: &Self) -> (o: Ordering)
    //        ensures o == self.cmp_spec(*other),
    //    {
    //        match (self.k, other.k) {
    //            (None, None) => Ordering::Equal,
    //            (None, Some(_)) => Ordering::Less,
    //            (Some(_), None) => Ordering::Greater,
    //            (Some(i), Some(j)) => { i.cmp(&j) }
    //        }
    //    }
    //
    // #[verifier(when_used_as_spec(lt_spec))]
    pub fn lt(&self, other: &Self) -> (b: bool)
        ensures
            b == self.lt_spec(*other),
    {
        (!self.is_end() && other.is_end()) || (!self.is_end() && !other.is_end()
            && self.k.as_ref().unwrap().cmp(&other.k.as_ref().unwrap()).is_lt())
    }

    spec fn leq_spec(self, other: Self) -> bool {
        self.lt_spec(other) || self == other
    }

    spec fn geq_K(self, other: K) -> bool {
        !self.lt_spec(KeyIterator::new_spec(other))
    }

    // Ivy calls this `done`
    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }

    // Is this iterator strictly above the supplied value?
    #[verifier(when_used_as_spec(above_spec))]
    fn above(&self, k: K) -> (b: bool)
        ensures
            b == self.above_spec(k),
    {
        self.is_end() || k.cmp(&self.k.as_ref().unwrap().clone()).is_lt()
    }

    // Is k in the range [lhs, rhs)
    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }
}

pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize)
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
            end as int,
            old(v)@.len() as int,
        ),
{
    let mut deleted = 0;
    proof {
        assert_seqs_equal!(v@,
                           old(v)@.subrange(0, start as int) +
                           old(v)@.subrange(start as int + deleted as int,
                                               old(v)@.len() as int));
    }
    while deleted < end - start
        invariant
            start <= end <= old(v)@.len(),
            v@.len() == old(v)@.len() - deleted,
            0 <= deleted <= end - start,
            v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
                start as int + deleted as int,
                old(v)@.len() as int,
            ),
    {
        v.remove(start);
        deleted = deleted + 1;
        proof {
            assert_seqs_equal!(v@,
                               old(v)@.subrange(0, start as int) +
                               old(v)@.subrange(start as int + deleted as int,
                                                   old(v)@.len() as int));
        }
    }
}

// TODO: Restore this to be generic over values V
#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedMap<K> {
    pub closed spec fn view(self) -> Map<K, ID> {
        self.m@
    }

    pub closed spec fn map_valid(
        self,
    ) -> bool  // recommends self.keys@.len() == self.vals.len()
    // error: public function requires cannot refer to private items
     {
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall|i|
            0 <= i < self.keys@.len() ==> #[trigger] (self.m@[self.keys@.index(i)])
                == self.vals@.index(i)
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.keys.valid()
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }

    /// We hold no keys in the range (lo, hi)
    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }

    proof fn mind_the_gap(self)
        ensures
            forall|w, x, y, z|
                self.gap(w, x) && self.gap(y, z) && #[trigger] y.lt_spec(x) ==> #[trigger] self.gap(
                    w,
                    z,
                ),
            forall|w, x, y: KeyIterator<K>, z| #[trigger]
                self.gap(w, x) && y.geq_spec(w) && x.geq_spec(z) ==> #[trigger] self.gap(y, z),
            forall|l: KeyIterator<K>, k, m| #[trigger]
                self.gap(k, m) ==> !(k.lt_spec(l) && l.lt_spec(m) && #[trigger] self@.contains_key(
                    *l.get(),
                )),
    {
        K::cmp_properties();
    }

    proof fn gap_means_empty(self, lo: KeyIterator<K>, hi: KeyIterator<K>, k: KeyIterator<K>)
        requires
            self.gap(lo, hi),
            lo.lt_spec(k) && k.lt_spec(hi),
            self@.contains_key(*k.get()),
        ensures
            false,
    {
        self.mind_the_gap();
    }

    proof fn choose_gap_violator(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> (r: KeyIterator<
        K,
    >)
        requires
            !self.gap(lo, hi),
        ensures
            lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get()),
    {
        choose|r| #![auto] lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get_spec())
    }

    fn new() -> (s: Self)
        ensures
            s.valid(),
            s@ == Map::<K, ID>::empty(),
    {
        let keys = StrictlyOrderedVec::new();
        let m = Ghost(Map::empty());
        proof {
            assert_sets_equal!(m@.dom(), keys@.to_set());
        }
        StrictlyOrderedMap { keys, vals: Vec::new(), m }
    }

    fn find_key(&self, k: &K) -> (o: Option<usize>)
        requires
            self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(i) => 0 <= i < self.keys@.len() && self.keys@[i as int] == k,
            },
    {
        let mut i = 0;
        while i < self.keys.len()
            invariant
                forall|j| 0 <= j < i ==> self.keys@[j] != k,
        {
            //println!("Loop {} of find_key", i);
            if self.keys.index(i).cmp(&k).is_eq() {
                proof {
                    K::cmp_properties();
                }
                return Some(i);
            } else {
                proof {
                    K::cmp_properties();
                }
            }
            i = i + 1;
        }
        return None;
    }

    // All values in the index range [lo, hi] are `v`
    // Second return value says that all values in the index range [lo, hi) are `v`,
    // but the value at hi is not `v`
    fn values_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret: (bool, bool))
        requires
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures
            ret.0 == forall|i| #![auto] lo <= i <= hi ==> self.vals@[i]@ == v@,
            !ret.0 ==> (ret.1 == (self.vals@[hi as int]@ != v@ && forall|i|
                #![auto]
                lo <= i < hi ==> self.vals@[i]@ == v@)),
    {
        let mut i = lo;
        while i <= hi
            invariant
                lo <= i,
                hi < self.keys@.len() as usize == self.vals@.len(),
                forall|j| #![auto] lo <= j < i ==> self.vals@[j]@ == v@,
        {
            let eq = do_end_points_match(&self.vals[i], v);
            if !eq {
                if i == hi {
                    return (false, true);
                } else {
                    return (false, false);
                }
            } else {
                proof {
                    //K::cmp_properties();
                }
            }
            i = i + 1;
        }
        (true, true)
    }

    // All keys in the range [keys[lo .. hi]] are `v`
    // Second return value says that all keys in the index range [keys[lo, hi)] are `v`,
    // but the value at hi is not `v`
    fn keys_in_index_range_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret: (bool, bool))
        requires
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures
            ret.0 == forall|i| #![auto] lo <= i <= hi ==> self@[self.keys@[i]]@ == v@,
            !ret.0 ==> (ret.1 == (self@[self.keys@[hi as int]]@ != v@ && (forall|i|
                #![auto]
                lo <= i < hi ==> self@[self.keys@[i]]@ == v@))),
    {
        let (agree, almost) = self.values_agree(lo, hi, v);
        proof {
            if agree {
            } else {
                assert(!forall|i| #![auto] lo <= i <= hi ==> self.vals@[i]@ == v@);
                let i = choose|i| #![auto] !(lo <= i <= hi ==> self.vals@.index(i)@ == v@);
                assert(self.vals@.index(i)@ != v@);
                assert(self@[self.keys@[i]]@ == self.vals@.index(i)@);
                if almost {
                } else {
                    assert(!(self.vals@[hi as int]@ != v@ && forall|i|
                        #![auto]
                        lo <= i < hi ==> self.vals@[i]@ == v@));
                    if self.vals@[hi as int]@ == v@ {
                    } else {
                        let j = choose|j| #![auto] lo <= j < hi && self.vals@[j]@ != v@;
                        assert(self@[self.keys@[j]]@ != v@);
                    }
                }
            }
        }
        (agree, almost)
    }

    //    // All keys present in the range [lo .. hi] map `v`
    //    fn keys_agree(&self, ghost(lo): Ghost<&K>, lo_index: usize, ghost(hi): Ghost<&K>, hi_index: usize, v: &ID) -> (b: bool)
    //        requires
    //            self.valid(),
    //            0 <= lo_index <= hi_index < self.keys@.len(),
    //            lo == self.keys@[lo_index as int],
    //            hi == self.keys@[hi_index as int],
    //        ensures b == forall |k| #![auto]
    //                        lo.cmp_spec(k).le()
    //                     && k.cmp_spec(*hi).le()
    //                     && self@.contains_key(k)
    //                     ==> self@[k]@ == v@,
    //    {
    //        let ret = self.keys_in_index_range_agree(lo_index, hi_index, v);
    //        proof {
    //            if ret {
    //                assert forall |k| #![auto]
    //                        lo.cmp_spec(k).le()
    //                     && k.cmp_spec(*hi).le()
    //                     && self@.contains_key(k)
    //                     implies self@[k]@ == v@ by {
    //                    assert(exists |i| 0 <= i < self.keys@.len() && self.keys@[i] == k);
    //                    let i = choose |i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
    //                    assert(lo_index <= i <= hi_index) by {
    //                        K::cmp_properties();
    //                    }
    //                }
    //            } else {
    //                let i = choose |i| #![auto] !(lo_index <= i <= hi_index ==> self@[self.keys@[i]]@ == v@);
    //                let k = self.keys@[i];
    //                assert(lo.cmp_spec(k).le() && k.cmp_spec(*hi).le()) by {
    //                    K::cmp_properties();
    //                }
    //                assert(self@.contains_key(k));
    //                assert(self@[k]@ != v@);
    //            }
    //        }
    //        ret
    //    }
    fn get<'a>(&'a self, k: &K) -> (o: Option<&'a ID>)
        requires
            self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(v) => self@[*k] == v,
            },
    {
        match self.find_key(k) {
            None => None,
            Some(i) => Some(&self.vals[i]),
        }
    }

    fn set(&mut self, k: K, v: ID)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@.insert(k, v),
            forall|lo, hi|
                self.gap(lo, hi) <==> old(self).gap(lo, hi) && !(lo.lt_spec(
                    KeyIterator::new_spec(k),
                ) && KeyIterator::new_spec(k).lt_spec(hi)),
    {
        match self.find_key(&k) {
            Some(i) => {
                self.vals.set(i, v);
                self.m = Ghost(self.m@.insert(k, v));
                proof {
                    assert_sets_equal!(self.m@.dom() == self.keys@.to_set());
                }
            },
            None => {
                let index = self.keys.insert(k.clone());
                self.vals.insert(index, v);
                self.m = Ghost(self.m@.insert(k, v));
            },
        }
        assert forall|lo, hi|
            self.gap(lo, hi) <==> old(self).gap(lo, hi) && !(lo.lt_spec(KeyIterator::new_spec(k))
                && KeyIterator::new_spec(k).lt_spec(hi)) by {
            self.mind_the_gap();
            old(self).mind_the_gap();
            if old(self).gap(lo, hi) && !(lo.lt_spec(KeyIterator::new_spec(k))
                && KeyIterator::new_spec(k).lt_spec(hi)) {
                assert forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(
                #[trigger] self@.contains_key(*ki.get())) by {
                    // TODO: This was the previous (flaky) proof:
                    // K::cmp_properties();
                    //
                    assert_by_contradiction!(!old(self)@.contains_key(*ki.get()), {
                        old(self).gap_means_empty(lo, hi, ki);
                    });
                };
                assert(self.gap(lo, hi));
            }
            if self.gap(lo, hi) {
                assert forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger] old(
                    self,
                )@.contains_key(*ki.get())) by {
                    assert_by_contradiction!(!(old(self)@.contains_key(*ki.get())), {
                        assert(self@.contains_key(*ki.get()));
                        K::cmp_properties();
                    });
                };
                assert(old(self).gap(lo, hi));
                assert_by_contradiction!(!(lo.lt_spec(KeyIterator::new_spec(k)) && KeyIterator::new_spec(k).lt_spec(hi)), {
                    assert(self@.contains_key(k));
                    self.gap_means_empty(lo, hi, KeyIterator::new_spec(k));
                });
            }
        };
    }

    spec fn greatest_lower_bound_spec(self, iter: KeyIterator<K>, glb: KeyIterator<K>) -> bool {
        (glb == iter || glb.lt_spec(iter)) && (forall|k|
            KeyIterator::new_spec(k) != glb && #[trigger] self@.contains_key(k) && iter.above(k)
                ==> glb.above(k)) && (!iter.is_end_spec() ==> glb.k.is_Some() && self@.contains_key(
            glb.k.get_Some_0(),
        )
            &&
        // There are no keys in the interval (glb, hi), and iter falls into that gap
        (exists|hi| #[trigger] self.gap(glb, hi) && #[trigger] KeyIterator::between(glb, iter, hi)))
    }

    // Finds the index of the largest iterator <= iter
    fn greatest_lower_bound_index(&self, iter: &KeyIterator<K>) -> (index: usize)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            0 <= index < self.keys@.len(),
            self.greatest_lower_bound_spec(*iter, KeyIterator::new_spec(self.keys@[index as int])),
    {
        let mut bound = 0;
        let mut i = 1;

        // Prove the initial starting condition
        assert forall|j: nat| j < i implies iter.geq_K(#[trigger] self.keys@.index(j as int)) by {
            let z = K::zero_spec();
            assert(self.keys@.contains(z));
            let n = choose|n: int| 0 <= n < self.keys@.len() && self.keys@[n] == z;
            K::zero_properties();
            assert_by_contradiction!(n == 0, {
                assert(self.keys@[0].cmp_spec(self.keys@[n]).lt());
                K::cmp_properties();
            });
            assert(self.keys@[0] == z);
            K::cmp_properties();
        }
        // Find the glb's index (bound)

        while i < self.keys.len()
            invariant
                1 <= i <= self.keys@.len(),
                bound == i - 1,
                forall|j: nat| j < i ==> iter.geq_K(#[trigger] self.keys@.index(j as int)),
            ensures
                bound == i - 1,
                (i == self.keys@.len() && forall|j: nat|
                    j < i ==> iter.geq_K(#[trigger] self.keys@.index(j as int))) || (i
                    < self.keys@.len() && !iter.geq_K(self.keys@.index(i as int)) && forall|j: nat|
                    j < i ==> iter.geq_K(#[trigger] self.keys@.index(j as int))),
        {
            if iter.lt(&KeyIterator::new(self.keys.index(i))) {
                // Reached a key that's too large
                break ;
            }
            bound = i;
            i = i + 1;
        }
        let glb = KeyIterator::new(self.keys.index(bound));

        assert forall|k|
            KeyIterator::new_spec(k) != glb && #[trigger] self@.contains_key(k) && iter.above(
                k,
            ) implies glb.above(k) by {
            K::cmp_properties();
        }
        proof {
            if !iter.is_end_spec() {
                if i == self.keys@.len() {
                    let hi = KeyIterator::end();
                    // Prove self.gap(glb, hi)
                    assert forall|ki| glb.lt_spec(ki) && ki.lt_spec(hi) implies !(
                    #[trigger] self@.contains_key(*ki.get())) by {
                        K::cmp_properties();
                    }
                    assert(self.gap(glb, hi));
                    assert(KeyIterator::between(glb, *iter, hi)) by {
                        K::cmp_properties();
                    }
                } else {
                    let hi = KeyIterator::new_spec(self.keys@[i as int]);
                    // Prove self.gap(glb, hi)
                    assert forall|ki| glb.lt_spec(ki) && ki.lt_spec(hi) implies !(
                    #[trigger] self@.contains_key(*ki.get())) by {
                        K::cmp_properties();
                    }
                    assert(self.gap(glb, hi));
                    assert(KeyIterator::between(glb, *iter, hi)) by {
                        assert(iter.lt_spec(hi));
                        K::cmp_properties();
                    }
                }
            }
        }

        assert(glb == iter || glb.lt_spec(*iter)) by {
            K::cmp_properties();
        }
        return bound;
    }

    // Finds the largest iterator <= iter
    fn greatest_lower_bound(&self, iter: &KeyIterator<K>) -> (glb: KeyIterator<K>)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            self.greatest_lower_bound_spec(*iter, glb),
    {
        let index = self.greatest_lower_bound_index(iter);
        let glb = KeyIterator::new(self.keys.index(index));
        glb
    }

    // Remove all keys in the range [lo, hi)
    fn erase(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            forall|k|
                {
                    let ki = KeyIterator::new_spec(k);
                    (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                        !(#[trigger] self@.contains_key(k))
                    } else {
                        (old(self)@.contains_key(k) ==> self@.contains_key(k) && self@[k] == old(
                            self,
                        )@[k]) && (self@.contains_key(k) ==> old(self)@.contains_key(k))
                    })
                },
            forall|x, y|
                self.gap(x, y) <==> ({
                    ||| old(self).gap(x, y)
                    ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                        || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                }),
    {
        // Find the point where keys are >= lo
        let mut start = 0;
        while start < self.keys.len() && lo.above(self.keys.index(start))
            invariant
                self.valid(),
                0 <= start <= self.keys@.len(),
                forall|j| #![auto] 0 <= j < start ==> lo.above(self.keys@.index(j)),
        {
            start = start + 1;
        }
        // Find the first point where keys are >= hi

        let mut end = start;
        while end < self.keys.len() && hi.above(self.keys.index(end))
            invariant
                self.valid(),
                start <= end <= self.keys@.len(),
                forall|j| #![auto] start <= j < end ==> hi.above(self.keys@[j]),
        {
            end = end + 1;
        }
        //assert(forall |i| #![auto] 0 <= i < start ==> lo.above(self.keys@.index(i)));

        assert forall|i| start <= i < end implies !lo.above(#[trigger] self.keys@[i]) && hi.above(
            self.keys@[i],
        ) by {
            K::cmp_properties();
        }
        self.keys.erase(start, end);
        vec_erase(&mut self.vals, start, end);
        self.m = Ghost(
            Map::new(
                |k| self.keys@.to_set().contains(k),
                |k|
                    {
                        let i = choose|i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
                        self.vals@[i]
                    },
            ),
        );
        proof {
            let ks = self.keys.to_set();
            assert(self.keys@.to_set() == ks);
            assert_sets_equal!(self.m@.dom(), ks);
        }

        assert forall|k|
            {
                let ki = KeyIterator::new_spec(k);
                (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                    !(#[trigger] self@.contains_key(k))
                } else {
                    old(self)@.contains_key(k) ==> self@.contains_key(k) && self@[k] == old(
                        self,
                    )@[k]
                })
            } by {
            let ki = KeyIterator::new_spec(k);
            if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                assert_by_contradiction!(!self@.contains_key(k), {
                    K::cmp_properties();
                });
            }
        }
        assert forall|x, y| self.gap(x, y) implies ({
            ||| old(self).gap(x, y)
            ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                || hi.is_end_spec() || !self@.contains_key(*hi.get())))
        }) by {
            assert_by_contradiction!(
                             old(self).gap(x, y)
                         || (old(self).gap(x, *lo) &&
                             old(self).gap(*hi, y) &&
                             (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get()))), {
                //assert(exists |ki| x.lt_spec(ki) && ki.lt_spec(y) && old(self)@.contains_key(*ki.get()));
                let ki = old(self).choose_gap_violator(x, y);
                if !old(self).gap(x, *lo) {
                    let kk = old(self).choose_gap_violator(x, *lo);
                    assert(self@.contains_key(*kk.get())); // contradicts self.gap(x, y)
                    K::cmp_properties();
                } else if !old(self).gap(*hi, y) {
                    let kk = old(self).choose_gap_violator(*hi, y);
                    assert(self@.contains_key(*kk.get())) by {   // contradicts self.gap(x, y)
                        K::cmp_properties();
                    };
                    K::cmp_properties();
                } else {
                    assert(!(hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())));
                    assert(hi.lt_spec(y));
                    if x.lt_spec(*hi) {
                        self.gap_means_empty(x, y, *hi);
                    } else if x == hi {
                        self.gap_means_empty(*hi, ki, y);
                    } else {
                        assert(hi.lt_spec(x)) by { K::cmp_properties(); };
                        assert(self@.contains_key(*ki.get())) by { K::cmp_properties(); };
                    }
                }
                assert(self@.contains_key(*ki.get()));
            });
        }
        assert forall|x, y|
            ({
                ||| old(self).gap(x, y)
                ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                    || hi.is_end_spec() || !self@.contains_key(*hi.get())))
            }) implies #[trigger] self.gap(x, y) by {
            if old(self).gap(x, y) {
                assert_by_contradiction!(self.gap(x, y), {
                    //let ki = self.choose_gap_violator(x, y);      // Flaky proof -- sometimes needs this line
                });
            }
            if old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y) || hi.is_end_spec()
                || !self@.contains_key(*hi.get())) {
                assert forall|ki| x.lt_spec(ki) && ki.lt_spec(y) implies !(
                #[trigger] self@.contains_key(*ki.get())) by {
                    assert(KeyIterator::between(x, ki, y)) by {
                        K::cmp_properties();
                    };
                    K::cmp_properties();  // Flaky
                    if ki.lt_spec(*lo) {
                        // flaky without assert_by_contradiction (and maybe still flaky)
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if hi.lt_spec(ki) {
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if ki == lo {
                        assert(!(self@.contains_key(*ki.get())));
                    } else if ki == hi {
                        assert(!(self@.contains_key(*ki.get())));
                    } else {
                        assert(KeyIterator::between(*lo, ki, *hi));
                    }
                    //old(self).mind_the_gap();

                };
            }
        }
    }
}

type ID = EndPoint;

// this code was trying to be too generic, but we need to know how to clone IDs. So we specialize.
#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    pub closed spec fn view(self) -> Map<K, AbstractEndPoint> {
        self.m@
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.lows.valid()
        &&& self.lows@.contains_key(K::zero_spec())
        &&& self@.dom().is_full()
        &&& (forall|k| #[trigger] self@[k].valid_physical_address())
        &&& (forall|k, i, j|
            self.lows@.contains_key(i) && self.lows.gap(KeyIterator::new_spec(i), j)
                && #[trigger] KeyIterator::between(
                KeyIterator::new_spec(i),
                KeyIterator::new_spec(k),
                j,
            ) ==> self@[k] == self.lows@[i]@)
    }

    pub fn new(k_zero: K, id_zero: ID) -> (s: Self)
        requires
            k_zero == K::zero_spec(),
            id_zero@.valid_physical_address(),
        ensures
            s.valid(),
            s@ == Map::total(|k: K| id_zero@),
    {
        let mut lows = StrictlyOrderedMap::new();
        lows.set(k_zero, id_zero);
        let m = Ghost(Map::total(|k| id_zero@));
        let s = DelegationMap { lows, m };
        s
    }

    pub proof fn valid_implies_complete(&self)
        requires
            self.valid(),
        ensures
            self@.dom().is_full(),
    {
    }

    // Returns the greatest_lower_bound as evidence for the proof of correctness for set
    fn get_internal(&self, k: &K) -> (res: (ID, Ghost<KeyIterator<K>>))
        requires
            self.valid(),
        ensures
            ({
                let (id, glb) = res;
                &&& id@ == self@[*k]
                &&& self.lows.greatest_lower_bound_spec(KeyIterator::new_spec(*k), glb@)
                &&& id@.valid_physical_address()
            }),
    {
        let ki = KeyIterator::new(k.clone());
        let glb = self.lows.greatest_lower_bound(&ki);
        proof {
            let glb_k = *glb.get();
            assert(self.lows@.contains_key(glb_k));  // OBSERVE
            let hi = choose|hi|
                self.lows.gap(glb, hi) && #[trigger] KeyIterator::between(glb, ki, hi);  // OBSERVE
            assert(KeyIterator::between(KeyIterator::new_spec(glb_k), ki, hi));
            // OBSERVE The following is required; unclear why the line above isn't sufficient
            assert(self.lows@.contains_key(glb_k) && self.lows.gap(KeyIterator::new_spec(glb_k), hi)
                && KeyIterator::between(
                KeyIterator::new_spec(glb_k),
                KeyIterator::new_spec(*k),
                hi,
            ));
        }
        let id = (*self.lows.get(glb.get()).unwrap()).clone_up_to_view();
        (id, Ghost(glb))
    }

    pub fn get(&self, k: &K) -> (id: ID)
        requires
            self.valid(),
        ensures
            id@ == self@[*k],
            id@.valid_physical_address(),
    {
        let (id, glb_ret) = self.get_internal(k);
        id
    }

    // Maps keys from [lo, hi) to dst
    pub fn set(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID)
        requires
            old(self).valid(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            forall|ki: KeyIterator<K>| #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> self@[*ki.get()] == dst@,
            forall|ki: KeyIterator<K>|
                !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi))
                    ==> self@[*ki.get()] == old(self)@[*ki.get()],
    {
        if lo.lt(&hi) {
            let ghost mut glb;
            if !hi.is_end() {
                // Get the current value of hi
                let (id, glb_ret) = self.get_internal(hi.get());
                proof {
                    glb = glb_ret@;
                }
                // Set it explicitly
                self.lows.set(hi.get().clone(), id);
            }
            let ghost mut pre_erase;
            proof {
                pre_erase = self.lows@;
            }
            let ghost mut pre_erase_vec;
            proof {
                pre_erase_vec = self.lows;
            }
            self.lows.erase(&lo, &hi);
            let ghost mut erased;
            proof {
                erased = self.lows@;
            }
            let ghost mut erased_vec;
            proof {
                erased_vec = self.lows;
            }
            self.lows.set(lo.get().clone(), clone_end_point(dst));
            self.m = Ghost(
                self.m@.union_prefer_right(
                    Map::new(
                        |k| KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi),
                        |k| dst@,
                    ),
                ),
            );
            assert(self@.dom().is_full()) by {
                assert_sets_equal!(self@.dom(), Set::full());
            }
            assert(self.lows@.contains_key(K::zero_spec())) by {
                let ki = KeyIterator::new_spec(K::zero_spec());
                assert_by_contradiction!(!lo.lt_spec(ki), {
                    K::zero_properties();
                    K::cmp_properties();
                });
                if lo == ki {
                } else {
                    assert(ki.lt_spec(*lo)) by {
                        K::zero_properties();
                    }
                }
            };
            assert forall|k, i, j|
                self.lows@.contains_key(i) && self.lows.gap(KeyIterator::new_spec(i), j)
                    && #[trigger] KeyIterator::between(
                    KeyIterator::new_spec(i),
                    KeyIterator::new_spec(k),
                    j,
                ) implies self@[k] == self.lows@[i]@ by {
                let ii = KeyIterator::new_spec(i);
                let ki = KeyIterator::new_spec(k);
                if KeyIterator::between(*lo, ki, *hi) {
                    assert(self@[k] == dst@);
                    assert_by_contradiction!(ii == lo, {
                        if lo.lt_spec(ii) {
                            K::cmp_properties();
                        } else {
                            K::cmp_properties();
                            assert(ii.lt_spec(*lo));
                            // We have ii < lo < hi && ii <= k < j, and nothing in (ii, j)
                            // and lo <= k < hi
                            // ==> ii < lo <= k < j
                            assert(lo.lt_spec(j));
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        }
                    });
                    assert(self.lows@[i]@ == dst@);
                } else if ki.lt_spec(*lo) {
                    assert(self@[k] == old(self)@[k]);
                    assert(!(ki.geq_spec(*lo) && ki.lt_spec(*hi)));
                    assert(erased.contains_key(i));
                    assert(ii != hi) by {
                        K::cmp_properties();
                    };
                    assert(old(self).lows@.contains_key(i));
                    assert(self.lows@[i] == old(self).lows@[i]);
                    assert(old(self).lows.gap(ii, j)) by {
                        assert_by_contradiction!(!lo.lt_spec(j), {
                            K::cmp_properties();
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        });
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall|m| KeyIterator::new_spec(m).lt_spec(*lo) implies (old(
                            self,
                        ).lows@.contains_key(m) == #[trigger] self.lows@.contains_key(m)) by {
                            K::cmp_properties();
                        };
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall|mi| ii.lt_spec(mi) && mi.lt_spec(j) implies !(#[trigger] old(
                            self,
                        ).lows@.contains_key(*mi.get())) by {
                            K::cmp_properties();
                        }
                    };
                    assert(old(self)@[k] == old(self).lows@[i]@);
                } else {
                    // We have:
                    //   self.lows@.contains i
                    //   nothing in (i, j)
                    //   i < k < j
                    //   lo < hi <= k < j
                    assert(ki.geq_spec(*hi));
                    assert(self@[k] == old(self)@[k]);
                    assert(!hi.is_end());

                    assert((ii != hi && old(self)@[k] == old(self).lows@[i]@) || self@[k]
                        == self.lows@[i]@) by {
                        assert((ii != hi && old(self).lows@.contains_key(i)) || ii == hi) by {
                            assert_by_contradiction!(!ii.lt_spec(*lo), {
                                // Flaky proof here
                                K::cmp_properties();
                            });

                            assert_by_contradiction!(ii != lo, {
                                // We need the following to prove hi is in self.lows@
                                assert(!hi.lt_spec(*hi)) by { K::cmp_properties(); };
                                assert(pre_erase.contains_key(*hi.get()));
                                assert(erased.contains_key(*hi.get()));
                                assert(self.lows@.contains_key(*hi.get()));

                                // But we have i < hi < j
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };

                                // which violates lows.gap(i, j)
                                //assert(false);
                            });

                            assert(lo.lt_spec(ii)) by {
                                K::cmp_properties();
                            };
                            // lo < i ==>
                            // lo < i <= k < j
                            // lo < hi <= k < j
                            assert_by_contradiction!(!ii.lt_spec(*hi), {
                                // If this were true, we would have i < hi < j,
                                // which violates gap(i, j)
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };
                                //assert(false);
                            });
                            // Therefore hi <= i
                            if ii == hi {
                            } else {
                                // hi < i   ==> keys from i to j in lows didn't change
                                assert(erased.contains_key(i));
                                assert(pre_erase.contains_key(i));
                                assert(old(self).lows@.contains_key(i));
                                //                                assert forall |m| ii.lt_spec(m) && m.lt_spec(j)
                                //                                        implies !(#[trigger] old(self)@.contains_key(*m.get())) by {
                                //                                    K::cmp_properties();
                                ////                                    assert_by_contradiction!(!old(self)@.contains_key(*m.get()), {
                                ////                                        K::cmp_properties();
                                ////                                        assert(self@.contains_key(*m.get()));
                                ////                                        assert(KeyIterator::between(ii, m, j));
                                ////                                        self.lows.gap_means_empty(ii, j, m);
                                ////                                    });
                                //                                };
                                K::cmp_properties();  // Flaky
                                assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                            }
                        };

                        //assert(erased.gap(i, j));

                        if ii == hi {
                            //   lo < (hi == i) < k < j
                            assert(pre_erase[*hi.get()]@ == old(self)@[*hi.get()]);
                            assert(erased[*hi.get()] == pre_erase[*hi.get()]) by {
                                K::cmp_properties();
                            };
                            assert(self@[*hi.get()] == erased[*hi.get()]@);
                            // Above establishes self@[*hi.get()] == old(self)@[*hi.get()]
                            assert(erased_vec.gap(ii, j));
                            assert(pre_erase_vec.gap(ii, j));
                            assert(old(self).lows.gap(ii, j));
                            if old(self).lows@.contains_key(i) {
                                assert(old(self)@[k] == old(self).lows@[i]@);
                            } else {
                                // old(self) did not contain hi; instead we added it inside the `if !hi.is_end()` clause
                                // But we know that glb was the closest bound to hi and glb is in old(self).lows@
                                assert(old(self).lows@.contains_key(*glb.get()));
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert_by_contradiction!(!ii.lt_spec(glb), {
                                    K::cmp_properties();
                                });
                                assert(ii.geq_spec(glb));
                                // Establish the preconditions to use @old(self).valid() to relate
                                // old(self)@[k] to old(self).lows@[glb]
                                let hi_hi = choose|h| #[trigger]
                                    old(self).lows.gap(glb, h) && KeyIterator::between(glb, *hi, h);
                                assert(old(self).lows.gap(glb, j)) by {
                                    old(self).lows.mind_the_gap();
                                }
                                assert(KeyIterator::between(glb, ki, j)) by {
                                    K::cmp_properties();
                                };
                                assert(old(self)@[k] == old(self).lows@[*glb.get()]@);

                                // Directly prove that  self@[k] == self.lows@[i]
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert(old(self).lows@[*glb.get()]@ == self@[*hi.get()]);
                                assert(old(self)@[k] == self@[*hi.get()]);
                                assert(self@[k] == self@[*hi.get()]);
                                assert(*lo.get() != i) by {
                                    K::cmp_properties();
                                };
                                assert(self.lows@[i] == erased[i]);
                                assert(self@[*hi.get()] == self.lows@[i]@);
                                assert(self@[k] == self.lows@[i]@);
                            }
                        } else {
                            assert(old(self).lows@.contains_key(i));
                            assert(erased_vec.gap(KeyIterator::new_spec(i), j));
                            // Prove that we can't be in the second clause of erase's gap
                            // postcondition
                            assert_by_contradiction!(!(hi.geq_spec(j) ||
                                                       hi.is_end_spec() ||
                                                       !erased_vec@.contains_key(*hi.get())), {
                                K::cmp_properties();
                            });
                            // Therefore we must be in the first clause, and hence:
                            assert(pre_erase_vec.gap(KeyIterator::new_spec(i), j));
                            assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                        }
                    };

                    if ii != hi {
                        assert(erased.contains_key(i)) by {
                            K::cmp_properties();
                        };
                        assert(self.lows@[i] == erased[i]) by {
                            K::cmp_properties();
                        };
                        assert(pre_erase.contains_key(i)) by {
                            K::cmp_properties();
                        };
                        assert(erased[i] == pre_erase[i]);
                        assert(old(self).lows@.contains_key(i));
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(self.lows@[i] == old(self).lows@[i]);
                    }
                }
            }
        }
        assert forall|ki: KeyIterator<K>| #[trigger]
            KeyIterator::between(*lo, ki, *hi) implies self@[*ki.get()] == dst@ by {
            K::cmp_properties();
        };
        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
        assert forall|ki: KeyIterator<K>|
            !ki.is_end_spec() && !(#[trigger] KeyIterator::between(
                *lo,
                ki,
                *hi,
            )) implies self@[*ki.get()] == old(self)@[*ki.get()] by {
            K::cmp_properties();
        };
    }

    pub open spec fn range_consistent(
        self,
        lo: &KeyIterator<K>,
        hi: &KeyIterator<K>,
        dst: &ID,
    ) -> bool {
        forall|k|
            KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) ==> (#[trigger] self@[k])
                == dst@
    }

    proof fn not_range_consistent(
        self,
        lo: &KeyIterator<K>,
        hi: &KeyIterator<K>,
        dst: &ID,
        bad: &KeyIterator<K>,
    )
        requires
            KeyIterator::between(*lo, *bad, *hi),
            self@.contains_key(*bad.get()),
            self@[*bad.get()] != dst@,
        ensures
            !self.range_consistent(lo, hi, dst),
    {
    }

    proof fn extend_range_consistent(
        self,
        x: &KeyIterator<K>,
        y: &KeyIterator<K>,
        z: &KeyIterator<K>,
        dst: &ID,
    )
        requires
            self.range_consistent(x, y, dst),
            self.range_consistent(y, z, dst),
        ensures
            self.range_consistent(x, z, dst),
    {
    }

    proof fn range_consistent_subset(
        self,
        x: &KeyIterator<K>,
        y: &KeyIterator<K>,
        x_inner: &KeyIterator<K>,
        y_inner: &KeyIterator<K>,
        dst: &ID,
    )
        requires
            self.range_consistent(x, y, dst),
            x_inner.geq_spec(*x),
            !y.lt_spec(*y_inner),
        ensures
            self.range_consistent(x_inner, y_inner, dst),
    {
        K::cmp_properties();
    }

    proof fn empty_key_range_is_consistent(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, id: &ID)
        requires
            lo.geq_spec(*hi),
        ensures
            self.range_consistent(lo, hi, id),
    {
        K::cmp_properties();
    }

    proof fn all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall|i| #![auto] lo <= i <= hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(
                &KeyIterator::new_spec(self.lows.keys@[lo as int]),
                &KeyIterator::new_spec(self.lows.keys@[hi as int]),
                id,
            ),
        decreases hi - lo,
    {
        self.almost_all_keys_agree(lo, hi, id);
    }

    proof fn almost_all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall|i| #![auto] lo <= i < hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(
                &KeyIterator::new_spec(self.lows.keys@[lo as int]),
                &KeyIterator::new_spec(self.lows.keys@[hi as int]),
                id,
            ),
        decreases hi - lo,
    {
        let lo_k = self.lows.keys@[lo as int];
        let hi_k = self.lows.keys@[hi as int];
        let lo_ki = KeyIterator::new_spec(lo_k);
        let hi_ki = KeyIterator::new_spec(hi_k);
        if lo_ki.geq_spec(hi_ki) {
            self.empty_key_range_is_consistent(&lo_ki, &hi_ki, id);
        } else {
            assert(lo_ki.lt_spec(hi_ki) && lo < hi) by {
                K::cmp_properties();
            }
            let lo_next = (lo + 1) as usize;
            let lo_next_k = self.lows.keys@[lo_next as int];
            let lo_next_ki = KeyIterator::new_spec(lo_next_k);
            assert(self.lows.gap(lo_ki, lo_next_ki)) by {
                K::cmp_properties();
            }
            assert(self.range_consistent(&lo_ki, &lo_next_ki, id));
            self.almost_all_keys_agree(lo_next, hi, id);
            self.extend_range_consistent(&lo_ki, &lo_next_ki, &hi_ki, id);
        }
    }

    pub fn range_consistent_impl(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID) -> (b:
        bool)
        requires
            self.valid(),
        ensures
            b == self.range_consistent(lo, hi, dst),
    {
        if lo.lt(hi) {
            let lo_glb_index = self.lows.greatest_lower_bound_index(lo);
            let hi_glb_index = self.lows.greatest_lower_bound_index(hi);
            assert(lo_glb_index <= hi_glb_index) by {
                K::cmp_properties();
            };
            let ghost lo_glb = self.lows.keys@[lo_glb_index as int];
            let hi_glb = self.lows.keys.index(hi_glb_index);
            let ghost lo_glb_ki = KeyIterator::new_spec(lo_glb);
            let ghost hi_glb_ki = KeyIterator::new_spec(hi_glb);

            //let ret = self.lows.keys_agree(Ghost(&lo_glb), lo_glb_index, Ghost(&hi_glb), hi_glb_index, dst);
            let (agree, almost) = self.lows.keys_in_index_range_agree(
                lo_glb_index,
                hi_glb_index,
                dst,
            );
            let ret = if agree {
                // Simple case where everything agrees
                true
            } else if !agree && almost && !hi.is_end() && hi_glb.cmp(hi.get()).is_eq() {
                // Corner case where almost everything agrees; the one disagreement
                // is exactly at the hi key, which isn't included in range_consistent
                true
            } else {
                // Simpler case where disagreement occurs before hi
                false
            };
            proof {
                let end_ki = KeyIterator::end_spec();
                if ret {
                    if agree {
                        self.all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        if hi_glb_index == self.lows.keys@.len() - 1 {
                            assert forall|k|
                                KeyIterator::between(
                                    hi_glb_ki,
                                    KeyIterator::new_spec(k),
                                    end_ki,
                                ) implies (#[trigger] self@[k]) == dst@ by {
                                K::cmp_properties();
                            }
                            assert(self.range_consistent(&hi_glb_ki, &end_ki, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &end_ki, dst);
                            self.range_consistent_subset(&lo_glb_ki, &end_ki, lo, hi, dst);
                        } else {
                            let hi_next_index = hi_glb_index + 1;
                            let hi_next = self.lows.keys@[hi_next_index];
                            let hi_next_ki = KeyIterator::new_spec(hi_next);
                            assert(self.lows.gap(hi_glb_ki, hi_next_ki)) by {
                                K::cmp_properties();
                            }
                            assert_by_contradiction!(!hi.above(hi_next), {
                                K::cmp_properties();
                                assert(self.lows@.contains_key(hi_next));   // Trigger conclusion of glb_spec
                            });
                            assert(!hi.is_end_spec()) by {
                                K::cmp_properties();
                            }
                            let upper = choose|u| #[trigger]
                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                    hi_glb_ki,
                                    *hi,
                                    u,
                                );
                            assert(self.range_consistent(&hi_glb_ki, &upper, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &upper, dst);
                            assert(!upper.lt_spec(*hi)) by {
                                K::cmp_properties();
                            }
                            self.range_consistent_subset(&lo_glb_ki, &upper, lo, hi, dst);
                        }
                    } else {
                        assert(!agree && almost && !hi.is_end() && hi_glb.cmp_spec(
                            *hi.get_spec(),
                        ).eq());
                        self.almost_all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        self.range_consistent(
                            &KeyIterator::new_spec(self.lows.keys@[lo_glb_index as int]),
                            &KeyIterator::new_spec(self.lows.keys@[hi_glb_index as int]),
                            dst,
                        );
                        assert(lo.geq_spec(lo_glb_ki));
                        self.range_consistent_subset(&lo_glb_ki, &hi_glb_ki, lo, hi, dst);
                    }
                } else {
                    assert(!agree);
                    let bad_index = choose|bad_index|
                        #![auto]
                        lo_glb_index <= bad_index <= hi_glb_index
                            && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                    let bad = self.lows.keys@[bad_index];
                    let bad_ki = KeyIterator::new_spec(bad);

                    if bad_index == lo_glb_index {
                        let lo_k = *lo.get();
                        let upper = choose|u| #[trigger]
                            self.lows.gap(lo_glb_ki, u) && KeyIterator::between(
                                lo_glb_ki,
                                KeyIterator::new_spec(lo_k),
                                u,
                            );
                        assert(self.lows@.contains_key(lo_glb));
                        assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                        assert(KeyIterator::between(
                            KeyIterator::new_spec(lo_glb),
                            KeyIterator::new_spec(lo_k),
                            upper,
                        ));
                        assert(self@[lo_k] == self.lows@[lo_glb]@);
                        assert(self.lows@[lo_glb]@ == self.lows@[self.lows.keys@[bad_index]]@);
                        assert(self@[lo_k] != dst@);
                        assert(KeyIterator::between(*lo, *lo, *hi)) by {
                            K::cmp_properties();
                        }
                        self.not_range_consistent(lo, hi, dst, lo);
                    } else {
                        assert(hi.is_end_spec() ==> hi_glb_ki != hi);
                        assert(hi_glb_ki.cmp_spec(*hi).eq() == (hi_glb_ki == hi)) by {
                            K::cmp_properties();
                        };

                        assert(bad_index > lo_glb_index && !bad_ki.lt_spec(*lo)) by {
                            K::cmp_properties();
                            assert(self.lows@.contains_key(bad));  // Trigger conclusion of glb_spec
                        };

                        // almost == (self@[self.keys@[hi_glb_index as int]]@ != v@ &&
                        //            (forall |i| #![auto] lo_glb_index <= i < hi_glb_index ==> self@[self.keys@[i]]@ == v@)))
                        if almost {
                            assert(hi_glb_index == bad_index);
                            if !hi.is_end_spec() {
                                if hi_glb_ki == hi {
                                    assert(ret);
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));

                                    let upper = choose|u|
                                        #![auto]
                                        self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                            hi_glb_ki,
                                            *hi,
                                            u,
                                        );
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, upper)) by {
                                        K::cmp_properties();
                                    };
                                    assert(self@[bad] == self.lows@[bad]@);

                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            } else {
                                if hi_glb_ki == hi {
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));

                                    //let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(self@[bad] == self.lows@[bad]@);

                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }
                        } else {
                            assert(self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ || !(
                            forall|i|
                                #![auto]
                                lo_glb_index <= i < hi_glb_index ==> self.lows@[self.lows.keys@[i]]@
                                    == dst@));

                            if self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ {
                                if !hi.is_end_spec() {
                                    if hi_glb_ki == hi {
                                        assert(bad_index < hi_glb_index);
                                        // Proof X
                                        let bad_next = self.lows.keys@[bad_index + 1];
                                        let bad_next_ki = KeyIterator::new_spec(bad_next);
                                        assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                            K::cmp_properties();
                                        }
                                        assert(self@[bad] != dst@) by {
                                            // Trigger DelegationMap::valid
                                            assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                K::cmp_properties();
                                            };
                                            assert(KeyIterator::between(
                                                bad_ki,
                                                bad_ki,
                                                bad_next_ki,
                                            )) by {
                                                K::cmp_properties();
                                            };
                                        }
                                        self.not_range_consistent(lo, hi, dst, &bad_ki);
                                    } else {
                                        // TODO: Duplicates entire Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X
                                            assert(bad_index + 1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index + 1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                                K::cmp_properties();
                                            }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                    K::cmp_properties();
                                                };
                                                assert(KeyIterator::between(
                                                    bad_ki,
                                                    bad_ki,
                                                    bad_next_ki,
                                                )) by {
                                                    K::cmp_properties();
                                                };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose|u|
                                                #![auto]
                                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                                    hi_glb_ki,
                                                    *hi,
                                                    u,
                                                );
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper)
                                                    && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(
                                                    hi_glb_ki,
                                                    hi_glb_ki,
                                                    upper,
                                                )) by {
                                                    K::cmp_properties();
                                                };  // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }
                                    }
                                } else {
                                    if hi_glb_ki == hi {
                                        assert(false);
                                    } else {
                                        // Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X
                                            assert(bad_index + 1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index + 1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                                K::cmp_properties();
                                            }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                    K::cmp_properties();
                                                };
                                                assert(KeyIterator::between(
                                                    bad_ki,
                                                    bad_ki,
                                                    bad_next_ki,
                                                )) by {
                                                    K::cmp_properties();
                                                };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose|u|
                                                #![auto]
                                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                                    hi_glb_ki,
                                                    *hi,
                                                    u,
                                                );
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper)
                                                    && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(
                                                    hi_glb_ki,
                                                    hi_glb_ki,
                                                    upper,
                                                )) by {
                                                    K::cmp_properties();
                                                };  // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }
                                    }
                                }
                            }
                            if !(forall|i: int|
                                lo_glb_index <= i < hi_glb_index ==> #[trigger] (
                                self.lows@[self.lows.keys@[i]]@) == dst@) {
                                // Choose a badder index
                                let bad_index = choose|bad_index|
                                    #![auto]
                                    lo_glb_index <= bad_index < hi_glb_index
                                        && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                                let bad = self.lows.keys@[bad_index];
                                let bad_ki = KeyIterator::new_spec(bad);

                                if bad_index == lo_glb_index {
                                    // TODO: Duplicates proof above
                                    let lo_k = *lo.get();
                                    let upper = choose|u| #[trigger]
                                        self.lows.gap(lo_glb_ki, u) && KeyIterator::between(
                                            lo_glb_ki,
                                            KeyIterator::new_spec(lo_k),
                                            u,
                                        );
                                    assert(self.lows@.contains_key(lo_glb));
                                    assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                                    assert(KeyIterator::between(
                                        KeyIterator::new_spec(lo_glb),
                                        KeyIterator::new_spec(lo_k),
                                        upper,
                                    ));
                                    assert(self@[lo_k] == self.lows@[lo_glb]@);
                                    assert(self.lows@[lo_glb]@
                                        == self.lows@[self.lows.keys@[bad_index]]@);
                                    assert(self@[lo_k] != dst@);
                                    assert(KeyIterator::between(*lo, *lo, *hi)) by {
                                        K::cmp_properties();
                                    }
                                    self.not_range_consistent(lo, hi, dst, lo);
                                } else {
                                    // TODO: This duplicates Proof X
                                    assert(bad_index + 1 < self.lows.keys@.len());
                                    let bad_next = self.lows.keys@[bad_index + 1];
                                    let bad_next_ki = KeyIterator::new_spec(bad_next);
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                        assert(self.lows@.contains_key(bad));  // Trigger conclusion of glb_spec
                                    }
                                    assert(self@[bad] != dst@) by {
                                        // Trigger DelegationMap::valid
                                        assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                            K::cmp_properties();
                                        };
                                        assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki))
                                            by {
                                            K::cmp_properties();
                                        };
                                    }
                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }
                        }
                    }
                }
            }
            ret
        } else {
            proof {
                self.empty_key_range_is_consistent(lo, hi, dst);
            }
            true
        }
    }
}

impl DelegationMap<AbstractKey> {
    pub fn delegate_for_key_range_is_host_impl(
        &self,
        lo: &KeyIterator<AbstractKey>,
        hi: &KeyIterator<AbstractKey>,
        dst: &ID,
    ) -> (b: bool)
        requires
            self.valid(),
        ensures
            b == AbstractDelegationMap::delegate_for_key_range_is_host(
                AbstractDelegationMap(self@),
                KeyRange { lo: *lo, hi: *hi },
                dst@,
            ),
    {
        let ret = self.range_consistent_impl(lo, hi, dst);
        proof {
            let kr = KeyRange { lo: *lo, hi: *hi };
            if ret {
                assert forall|k| #[trigger] kr.contains(k) implies self@[k] == dst@ by {
                    assert(KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi));  // Trigger for range_consistent
                }
            } else {
                let k = choose|k|
                    KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) && #[trigger] self@[k]
                        != dst@;
                assert(kr.contains(k));
            }
        }
        ret
    }
}

impl DelegationMap<CKey> {
    pub proof fn lemma_set_is_update(
        pre: Self,
        post: Self,
        lo: KeyIterator<CKey>,
        hi: KeyIterator<CKey>,
        dst: &ID,
    )
        requires
            pre.valid(),
            dst@.valid_physical_address(),
            // fn set postconditions
            post.valid(),
            forall|ki: KeyIterator<CKey>| #[trigger]
                KeyIterator::between(lo, ki, hi) ==> post@[*ki.get()] == dst@,
            forall|ki: KeyIterator<CKey>|
                !ki.is_end_spec() && !(#[trigger] KeyIterator::between(lo, ki, hi))
                    ==> post@[*ki.get()] == pre@[*ki.get()],
        ensures
            AbstractDelegationMap(post@) =~= AbstractDelegationMap(pre@).update(
                KeyRange { lo, hi },
                dst@,
            ),
    {
        //         let setted = AbstractDelegationMap(post@);
        //         let updated = AbstractDelegationMap(pre@).update(KeyRange{lo, hi}, dst@);
        //         assert forall |k| setted.0.contains_key(k) <==> updated.0.contains_key(k) by {}
        //         assert forall |k| setted.0.contains_key(k) implies setted.0[k] == updated.0[k] by {}
        //AbstractDelegationMap(self@.union_prefer_right(Map::new(|k| newkr.contains(k), |k| host)))
        //         assert( AbstractDelegationMap(post@) =~= AbstractDelegationMap(pre@).update(KeyRange{lo, hi}, dst@) );
    }
}

} // verus!
// end verus!
