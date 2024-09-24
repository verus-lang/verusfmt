use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::set_lib::*;

use crate::abstract_end_point_t::*;
use crate::args_t::*;
use crate::io_t::*;
use builtin::*;
use builtin_macros::*;

verus! {

// Translates Impl/Common/SeqIsUniqueDef.i.dfy :: SeqIsUnique
#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
}

pub fn do_vec_u8s_match(e1: &Vec<u8>, e2: &Vec<u8>) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    if e1.len() != e2.len() {
        assert(e1@.len() != e2@.len());
        assert(e1@ != e2@);
        return false;
    }
    let mut i: usize = 0;
    while i < e1.len()
        invariant
            0 <= i,
            i <= e1.len(),
            e1.len() == e2.len(),
            forall|j: int| 0 <= j && j < i ==> e1@[j] == e2@[j],
    {
        if e1[i] != e2[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert_seqs_equal!(e1@, e2@);
    }
    return true;
}

pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    do_vec_u8s_match(&e1.id, &e2.id)
}

// Translates Impl/Common/CmdLineParser.i.dfy :: test_unique
pub fn test_unique(endpoints: &Vec<EndPoint>) -> (unique: bool)
    ensures
        unique == seq_is_unique(abstractify_end_points(*endpoints)),
{
    let mut i: usize = 0;
    while i < endpoints.len()
        invariant
            0 <= i,
            i <= endpoints.len(),
            forall|j: int, k: int|
                #![trigger endpoints@[j]@, endpoints@[k]@]
                0 <= j && j < endpoints.len() && 0 <= k && k < i && j != k ==> endpoints@[j]@
                    != endpoints@[k]@,
    {
        let mut j: usize = 0;
        while j < endpoints.len()
            invariant
                0 <= i,
                i < endpoints.len(),
                forall|j: int, k: int|
                    #![trigger endpoints@[j]@, endpoints@[k]@]
                    0 <= j && j < endpoints.len() && 0 <= k && k < i && j != k ==> endpoints@[j]@
                        != endpoints@[k]@,
                0 <= j,
                j <= endpoints.len(),
                forall|k: int|
                    #![trigger endpoints@[k]@]
                    0 <= k && k < j && k != i ==> endpoints@[i as int]@ != endpoints@[k]@,
        {
            if i != j && do_end_points_match(&endpoints[i], &endpoints[j]) {
                assert(!seq_is_unique(abstractify_end_points(*endpoints))) by {
                    reveal(seq_is_unique::<AbstractEndPoint>);
                    let aeps = abstractify_end_points(*endpoints);
                    assert(aeps[i as int] == endpoints@[i as int]@);
                    assert(aeps[j as int] == endpoints@[j as int]@);
                    assert(endpoints@[i as int]@ == endpoints@[j as int]@ && i != j);
                }
                return false;
            }
            j = j + 1;
        }
        i = i + 1;
    };
    assert(seq_is_unique(abstractify_end_points(*endpoints))) by {
        reveal(seq_is_unique::<AbstractEndPoint>);
    }
    return true;
}

pub fn endpoints_contain(endpoints: &Vec<EndPoint>, endpoint: &EndPoint) -> (present: bool)
    ensures
        present == abstractify_end_points(*endpoints).contains(endpoint@),
{
    let mut j: usize = 0;
    while j < endpoints.len()
        invariant
            0 <= j && j <= endpoints.len(),
            forall|k: int|
                #![trigger endpoints@[k]@]
                0 <= k && k < j ==> endpoint@ != endpoints@[k]@,
    {
        if do_end_points_match(endpoint, &endpoints[j]) {
            assert(abstractify_end_points(*endpoints)[j as int] == endpoint@);
            return true;
        }
        j = j + 1;
    }
    return false;
}

pub fn clone_option_vec_u8(ov: Option<&Vec<u8>>) -> (res: Option<Vec<u8>>)
    ensures
        match ov {
            Some(e1) => res.is_some() && e1@ == res.get_Some_0()@,
            None => res.is_None(),
        },
{
    match ov {
        Some(e1) => Some(clone_vec_u8(e1)),
        None => None,
    }
}

pub fn clone_end_point(ep: &EndPoint) -> (cloned_ep: EndPoint)
    ensures
        cloned_ep@ == ep@,
{
    EndPoint { id: clone_vec_u8(&ep.id) }
}

pub fn clone_option_end_point(oep: &Option<EndPoint>) -> (cloned_oep: Option<EndPoint>)
    ensures
        match oep {
            Some(ep) => cloned_oep.is_some() && ep@ == cloned_oep.get_Some_0()@,
            None => cloned_oep.is_None(),
        },
{
    match oep.as_ref() {
        Some(ep) => Some(clone_end_point(ep)),
        None => None,
    }
}

pub proof fn singleton_seq_to_set_is_singleton_set<T>(x: T)
    ensures
        seq![x].to_set() == set![x],
{
    let seq1 = seq![x];
    let set1 = seq1.to_set();
    let set2 = set![x];
    assert forall|y| set1.contains(y) <==> set2.contains(y) by {
        if y == x {
            assert(seq1[0] == y);
            assert(set1.contains(y));
        }
    }
    assert_sets_equal!(seq![x].to_set(), set![x]);
}

} // verus!
