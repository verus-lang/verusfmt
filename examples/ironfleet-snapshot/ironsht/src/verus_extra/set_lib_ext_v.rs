use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

verus! {

/// This fold uses a fixed zero rather than accumulating results in that
/// argument. This means proofs don't need to generalize over the accumulator,
/// unlike the Set::fold currently in Verus.
pub open spec fn set_fold<A, B>(s: Set<A>, zero: B, f: spec_fn(B, A) -> B) -> B
    recommends
        s.finite(),
    decreases s.len(),
{
    if s.finite() {
        if s.len() == 0 {
            zero
        } else {
            let a = s.choose();
            f(set_fold(s.remove(a), zero, f), a)
        }
    } else {
        zero
    }
}

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    // extra parens are for rust-analyzer
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

pub proof fn flatten_sets_spec<A>(sets: Set<Set<A>>)
    ensures
        (forall|e| #[trigger]
            flatten_sets(sets).contains(e) ==> exists|s| sets.contains(s) && s.contains(e)),
        (forall|s: Set<A>| #[trigger] sets.contains(s) ==> s.subset_of(flatten_sets(sets))),
{
}

pub proof fn lemma_flatten_sets_insert<A>(sets: Set<Set<A>>, s: Set<A>)
    ensures
        flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s),
{
    assert_sets_equal!(flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s));
}

pub proof fn lemma_flatten_sets_union<A>(sets1: Set<Set<A>>, sets2: Set<Set<A>>)
    ensures
        flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
    assert_sets_equal!(flatten_sets(sets1.union(sets2)) ==
        flatten_sets(sets1).union(flatten_sets(sets2)));
}

pub proof fn lemma_flatten_sets_union_auto<A>()
    ensures
        forall|sets1: Set<Set<A>>, sets2: Set<Set<A>>| #[trigger]
            flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
    assert forall|sets1: Set<Set<A>>, sets2: Set<Set<A>>| #[trigger]
        flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)) by {
        lemma_flatten_sets_union(sets1, sets2);
    }
}

pub proof fn set_map_union<A, B>(s1: Set<A>, s2: Set<A>, f: spec_fn(A) -> B)
    ensures
        (s1 + s2).map(f) == s1.map(f) + s2.map(f),
{
    assert_sets_equal!((s1 + s2).map(f) == s1.map(f) + s2.map(f), y => {
        if s1.map(f).contains(y) {
            let x = choose |x| s1.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        } else if s2.map(f).contains(y) {
            let x = choose |x| s2.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        }
    });
}

pub proof fn set_map_union_auto<A, B>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, f: spec_fn(A) -> B| #[trigger]
            (s1 + s2).map(f) == s1.map(f) + s2.map(f),
{
    assert forall|s1: Set<A>, s2: Set<A>, f: spec_fn(A) -> B| #[trigger]
        ((s1 + s2).map(f)) == s1.map(f) + s2.map(f) by {
        set_map_union(s1, s2, f);
    }
}

pub proof fn seq_map_values_concat<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B)
    ensures
        (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f),
{
    assert_seqs_equal!((s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f), i => {
        if i < s1.len() {
            assert((s1+s2)[i] == s1[i]);
        } else {
            assert((s1+s2)[i] == s2[i - s1.len()]);
        }
    });
}

pub proof fn seq_map_values_concat_auto<A, B>()
    ensures
        forall|s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B| #[trigger]
            (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f),
{
    assert forall|s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B| #[trigger]
        ((s1 + s2).map_values(f)) == s1.map_values(f) + s2.map_values(f) by {
        seq_map_values_concat(s1, s2, f);
    }
}

pub open spec fn flatten_set_seq<A>(sets: Seq<Set<A>>) -> Set<A> {
    sets.fold_left(Set::<A>::empty(), |s1: Set<A>, s2: Set<A>| s1.union(s2))
}

pub proof fn lemma_flatten_set_seq_spec<A>(sets: Seq<Set<A>>)
    ensures
        (forall|x: A| #[trigger]
            flatten_set_seq(sets).contains(x) ==> exists|i: int|
                0 <= i < sets.len() && #[trigger] sets[i].contains(x)),
        (forall|x: A, i: int|
            0 <= i < sets.len() && #[trigger] sets[i].contains(x) ==> flatten_set_seq(
                sets,
            ).contains(x)),
    decreases sets.len(),
{
    if sets.len() == 0 {
    } else {
        lemma_flatten_set_seq_spec(sets.drop_last());
        assert forall|x: A| flatten_set_seq(sets).contains(x) implies exists|i: int|
            0 <= i < sets.len() && #[trigger] sets[i].contains(x) by {
            if sets.last().contains(x) {
            } else {
                assert(flatten_set_seq(sets.drop_last()).contains(x));
            }
        }
        assert forall|x: A, i: int|
            0 <= i < sets.len() && #[trigger] sets[i].contains(x) implies flatten_set_seq(
            sets,
        ).contains(x) by {
            if i == sets.len() - 1 {
                assert(sets.last().contains(x));
                assert(flatten_set_seq(sets) == flatten_set_seq(sets.drop_last()).union(
                    sets.last(),
                ));
            } else {
                assert(0 <= i < sets.drop_last().len() && sets.drop_last()[i].contains(x));
            }
        }
    }
}

pub proof fn lemma_seq_push_to_set<A>(s: Seq<A>, x: A)
    ensures
        s.push(x).to_set() == s.to_set().insert(x),
{
    assert_sets_equal!(s.push(x).to_set() == s.to_set().insert(x), elem => {
        if elem == x {
            assert(s.push(x)[s.len() as int] == x);
            assert(s.push(x).contains(x))
        } else {
            if s.to_set().insert(x).contains(elem) {
                assert(s.to_set().contains(elem));
                let i = choose |i: int| 0 <= i < s.len() && s[i] == elem;
                assert(s.push(x)[i] == elem);
            }
        }
    });
}

pub proof fn lemma_set_map_insert<A, B>(s: Set<A>, f: spec_fn(A) -> B, x: A)
    ensures
        s.insert(x).map(f) == s.map(f).insert(f(x)),
{
    assert_sets_equal!(s.insert(x).map(f) == s.map(f).insert(f(x)), y => {
        if y == f(x) {
            assert(s.insert(x).contains(x)); // OBSERVE
            // assert(s.map(f).insert(f(x)).contains(f(x)));
        } else {
            if s.insert(x).map(f).contains(y) {
                let x0 = choose |x0| s.contains(x0) && y == f(x0);
                assert(s.map(f).contains(y));
            } else {
                if s.map(f).insert(f(x)).contains(y) {
                    let x0 = choose |x0| s.contains(x0) && y == f(x0);
                    assert(s.map(f).contains(y));
                    assert(s.insert(x).contains(x0));
                }
            }
        }
    });
}

// TODO(verus): This consequence should somehow be broadcast from map_values/map
pub proof fn lemma_seq_map_equiv<A, B>(f: spec_fn(A) -> B, g: spec_fn(int, A) -> B)
    requires
        forall|i: int, a: A| #[trigger] g(i, a) == f(a),
    ensures
        forall|s: Seq<A>| s.map_values(f) == s.map(g),
{
    assert forall|s: Seq<A>| s.map_values(f) == s.map(g) by {
        assert_seqs_equal!(s.map_values(f), s.map(g));
    }
}

pub proof fn lemma_to_set_distributes_over_addition<A>(s: Seq<A>, t: Seq<A>)
    ensures
        (s + t).to_set() == s.to_set() + t.to_set(),
{
    let left = (s + t).to_set();
    let right = s.to_set() + t.to_set();
    assert forall|x| right.contains(x) implies left.contains(x) by {
        assert(s.to_set() + t.to_set() == s.to_set().union(t.to_set()));
        if s.to_set().contains(x) {
            let si = choose|si| 0 <= si < s.len() && s[si] == x;
            assert((s + t)[si] == x);
        } else {
            let ti = choose|ti| 0 <= ti < t.len() && t[ti] == x;
            assert((s + t)[s.len() + ti] == x);
        }
    }
    assert_sets_equal!(left, right);
}

pub proof fn lemma_to_set_union_auto<A>()
    ensures
        forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set(),
{
    assert forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set() by {
        lemma_to_set_distributes_over_addition(s, t);
    }
}

spec fn map_fold<A, B>(s: Set<A>, f: spec_fn(A) -> B) -> Set<B>
    recommends
        s.finite(),
{
    set_fold(s, Set::empty(), |s1: Set<B>, a: A| s1.insert(f(a)))
}

proof fn map_fold_ok<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires
        s.finite(),
    ensures
        map_fold(s, f) =~= s.map(f),
    decreases s.len(),
{
    if s.len() == 0 {
        return ;
    } else {
        let a = s.choose();
        map_fold_ok(s.remove(a), f);
        return ;
    }
}

proof fn map_fold_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires
        s.finite(),
    ensures
        map_fold(s, f).finite(),
    decreases s.len(),
{
    if s.len() == 0 {
        return ;
    } else {
        let a = s.choose();
        map_fold_finite(s.remove(a), f);
        return ;
    }
}

pub proof fn map_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires
        s.finite(),
    ensures
        s.map(f).finite(),
{
    map_fold_ok(s, f);
    map_fold_finite(s, f);
}

pub proof fn map_set_finite_auto<A, B>()
    ensures
        forall|s: Set<A>, f: spec_fn(A) -> B| s.finite() ==> #[trigger] (s.map(f).finite()),
{
    assert forall|s: Set<A>, f: spec_fn(A) -> B| s.finite() implies #[trigger] s.map(
        f,
    ).finite() by {
        map_finite(s, f);
    }
}

pub proof fn lemma_to_set_singleton_auto<A>()
    ensures
        forall|x: A| #[trigger] seq![x].to_set() == set![x],
{
    assert forall|x: A| #[trigger] seq![x].to_set() =~= set![x] by {
        assert(seq![x][0] == x);
    }
}

pub proof fn lemma_map_values_singleton_auto<A, B>()
    ensures
        forall|x: A, f: spec_fn(A) -> B| #[trigger] seq![x].map_values(f) =~= seq![f(x)],
{
}

pub proof fn lemma_map_set_singleton_auto<A, B>()
    ensures
        forall|x: A, f: spec_fn(A) -> B| #[trigger] set![x].map(f) == set![f(x)],
{
    assert forall|x: A, f: spec_fn(A) -> B| #[trigger] set![x].map(f) =~= set![f(x)] by {
        assert(set![x].contains(x));
    }
}

pub proof fn lemma_map_seq_singleton_auto<A, B>()
    ensures
        forall|x: A, f: spec_fn(A) -> B| #[trigger] seq![x].map_values(f) =~= seq![f(x)],
{
}

pub proof fn flatten_sets_singleton_auto<A>()
    ensures
        forall|x: Set<A>| #[trigger] flatten_sets(set![x]) =~= x,
{
}

// TODO(Tej): We strongly suspect there is a trigger loop in these auto
// lemmas somewhere, but it's not easy to see from the profiler yet.
} // verus!
