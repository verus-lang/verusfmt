// TODO fix?
// #![feature(register_tool)]
// #![register_tool(verifier)]

#[allow(unused_imports)]
use builtin::*;
use vstd::*;
// use vstd::seq::*;
use vstd::prelude::*;
use state_machines_macros::state_machine;

mod spec{
// some types and utilities
pub mod constants{


}

pub mod types{
#[allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::Dispatch;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Some Types
////////////////////////////////////////////////////////////////////////////////////////////////////

pub use crate::{NodeId, LogIdx, ReqId, ThreadId};

/// This represents an entry in the abstract log
pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}

/// Represents an entry in the log
///
/// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
pub struct ConcreteLogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: u64,
}

} // verus!

}

pub mod utils{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::set::Set;

verus! {

pub open spec fn seq_unique<A>(seq: Seq<A>) -> bool
    // where A: PartialEq + Structural
{
    forall |i:int, j:int| (0 <= i < seq.len() && 0 <=j < seq.len() && i != j)
            ==> seq.index(i as int) !== seq.index(j as int)
}

/// whether two sequences are disjoint, i.e., they don't have common elements
pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool
{
   forall |i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j)
}


/// recursive definition of seq to set conversion
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len() when seq.len() >= 0 via seq_to_set_rec_decreases::<A>
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

#[via_fn]
proof fn seq_to_set_rec_decreases<A>(seq: Seq<A>)
{
    if seq.len() == 0 {
    } else {
        assert(seq.drop_last().len() < seq.len()); // INCOMPLETENESS weird incompleteness again
    }
}

/// shows that the recursive definition of set_to_seq produces a finite set
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures seq_to_set_rec(seq).finite()
    decreases seq.len()
{
    if seq.len() > 0{
        let sub_seq = seq.drop_last();
        assert(seq_to_set_rec(sub_seq).finite()) by {
            seq_to_set_rec_is_finite(sub_seq);
        }
    }
}

/// shows that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq =~= seq.drop_last().push(seq.last()));
        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures seq_to_set(seq) == seq_to_set_rec(seq)
{
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set(seq).contains(n));
    assert(seq_to_set(seq) =~= seq_to_set_rec(seq));
}

pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A>
{
    Set::new(|a: A| seq.contains(a))
}

pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures seq_to_set(seq).finite()
{
    assert(seq_to_set(seq).finite()) by {
        seq_to_set_equal_rec(seq);
        seq_to_set_rec_is_finite(seq);
    }
}

pub open spec fn map_new_rec<V>(dom: nat, val: V) -> Map<nat, V>
    decreases dom when dom >= 0
{
    if dom == 0 {
        map![ dom => val]
    } else {
        map_new_rec((dom - 1) as nat, val).insert(dom, val)
    }
}

pub proof fn map_new_rec_dom_finite<V>(dom: nat, val: V)
   ensures
      map_new_rec(dom, val).dom().finite(),
      forall |n: nat| 0 <= n <= dom <==> map_new_rec(dom, val).contains_key(n),
      forall |n| (#[trigger] map_new_rec(dom, val).contains_key(n)) ==> map_new_rec(dom, val)[n] == val
   decreases dom
{
    if dom == 0 {

    } else {
        let sub_dom = (dom - 1) as nat;
        let sub_map = map_new_rec(sub_dom as nat, val);
        assert(sub_map.dom().finite()) by {
            map_new_rec_dom_finite(sub_dom, val);
        }

        assert(forall |n: nat| (#[trigger] sub_map.contains_key(n)) <==> 0 <= n <= sub_dom ) by {
            map_new_rec_dom_finite(sub_dom, val);
        }

        assert(forall |n: nat| (#[trigger] sub_map.contains_key(n)) ==> sub_map[n] == val) by {
            map_new_rec_dom_finite(sub_dom, val);
        }


    }
}



pub open spec fn map_contains_value<K, V>(map: Map<K, V>, val: V) -> bool
    // where K: PartialEq + Structural
{
    exists|i: K| #[trigger] map.contains_key(i) && map.index(i) == val
}


pub open spec fn range(low: nat, mid: nat, high:nat) -> bool {
    low <= mid && mid < high
}

pub open spec fn rangeincl(low: nat, mid: nat, high:nat) -> bool {
    low <= mid && mid <= high
}


#[verifier(nonlinear)]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires 0 <= i < len, 0 < len,
    ensures  (i % len) == i

{
}

}

}


// the linearization proof
pub mod linearization{
// The Linearization Proof


#[allow(unused_imports)]
use builtin::*;
// use vstd::*;
use vstd::seq::*;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::spec::simple_log::{UpdateResp, ReadReq, SimpleLog, compute_nrstate_at_version};
use crate::{LogIdx, ReqId};
use crate::Dispatch;
#[cfg(verus_keep_ghost)]
use crate::{SimpleLogRefinesAsynchronousSingleton, AsyncLabel, AsynchronousSingletonBehavior, AsynchronousSingleton, SimpleLogBehavior,
behavior_equiv, InputOperation, OutputOperation};

verus! {
#[cfg(verus_keep_ghost)]
type SState<DT> = SimpleLog::State<DT>;
#[cfg(verus_keep_ghost)]
type AState<DT> = AsynchronousSingleton::State<DT>;

////////////////////////////////////////////////////////////////////////////////////////////////////
//                                  LINEARIZATION PROOF                                           //
////////////////////////////////////////////////////////////////////////////////////////////////////


// =================================================================================================
// Refinement Theorem
// =================================================================================================

#[cfg(verus_keep_ghost)]
pub tracked struct RefinementProof;
#[cfg(verus_keep_ghost)]
impl<DT: Dispatch> SimpleLogRefinesAsynchronousSingleton<DT> for RefinementProof {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<DT>)
        // requires a.wf(),
        // ensures b.wf() && behavior_equiv(a, b)
    {
        return exists_equiv_behavior_rec(a, Map::empty())
    }
}

/// The *actual* refinement proof using recursion over the behaviors
proof fn exists_equiv_behavior_rec<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>)
    -> (b: AsynchronousSingletonBehavior<DT>)
    requires a.wf() && future_points_ok(a.get_last(), r_points)
    ensures  b.wf() && behavior_equiv(a, b) && state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases a, 0nat, 0nat
{
    match a {
        SimpleLogBehavior::Stepped(post, aop, tail) => {
            // reveal the next transition
            reveal(SimpleLog::State::next);
            reveal(SimpleLog::State::next_by);
            reveal(AsynchronousSingleton::State::next);
            reveal(AsynchronousSingleton::State::next_by);

            let prev = tail.get_last();
            let step = choose |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(prev, post, aop, step);
            match step {
                SimpleLog::Step::readonly_start(rid, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.remove(rid));
                    let a0 = readonly_start_refines(prev, post, aop, b0.get_last(), r_points, rid, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::readonly_read_version(rid) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = readonly_read_version_refines(prev, post, aop, b0.get_last(), r_points, rid);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::readonly_finish(rid, logidx, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.insert(rid, logidx));
                    let a0 = readonly_finish_refines(prev, post, aop, b0.get_last(), r_points, rid, logidx, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_start(rid, uop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_start_refines(prev, post, aop, b0.get_last(), r_points, rid, uop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_add_op_to_log(rid) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_add_update_to_log_refines(prev, post, aop, b0.get_last(), r_points, rid);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_incr_version(logidx) => {
                    update_incr_version_refines(a, r_points, logidx)
                }
                SimpleLog::Step::update_finish(rid, resp) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_finish_refines(prev, post, aop, b0.get_last(), r_points, rid, resp);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::no_op() => {
                    exists_equiv_behavior_rec(*tail, r_points)
                }
                SimpleLog::Step::dummy_to_use_type_params(state) => {
                    assert(false);  // nothing to be done here, this is not a real transition but
                    arbitrary()     // is being generated to make Rust happy w.r.t. type parameters
                }
            }
        }
        SimpleLogBehavior::Inited(sl_state) => {
            let st = AsynchronousSingleton::State {
                state: DT::init_spec(),
                reqs: Map::empty(),
                resps: Map::empty(),
            };
            let res =  AsynchronousSingletonBehavior::Inited(st);

            reveal(SimpleLog::State::init);
            reveal(SimpleLog::State::init_by);
            reveal(AsynchronousSingleton::State::init);
            reveal(AsynchronousSingleton::State::init_by);

            assert(AsynchronousSingleton::State::init_by(st, AsynchronousSingleton::Config::initialize()));
            res
        }
    }
}


// =================================================================================================
// Validity of Requests
// =================================================================================================


/// checks whether the version of the request with the given ID is OK           (Dafny: FutureRidOk)
spec fn future_rid_ok<DT: Dispatch>(s: SState<DT>, rid: ReqId, version: LogIdx) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Init() ==> s.version <= version
    &&& s.readonly_reqs[rid].is_Req()  ==> s.readonly_reqs[rid].get_Req_version() <= version
}

/// checks whether the versions of the requests are ok                       (Dafny: FuturePointsOk)
spec fn future_points_ok<DT: Dispatch>(s:SState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    &&& r_points.dom().finite()
    &&& (forall |rid| #[trigger]r_points.contains_key(rid) ==> future_rid_ok(s, rid, r_points[rid]))
}

/// checks whether the readonly requests are valid                                    (Dafny: rel_r)
/// in the simple log, we do not distinguish between requests and responses, but the AsyncSingleton
/// does, so we need to do a case distinction here.
spec fn readonly_requests_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    &&& (forall |rid| (#[trigger]s.readonly_reqs.contains_key(rid) && #[trigger]t.reqs.contains_key(rid))
            ==> readonly_request_is_valid(s, t, r_points, rid))
    &&& (forall |rid| (#[trigger]s.readonly_reqs.contains_key(rid) && #[trigger]t.resps.contains_key(rid))
            ==> readonly_response_is_valid(s, t, r_points, rid))
}

/// checks whether the readonly request is valid                            (Dafny: readonly_is_req)
spec fn readonly_request_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& (s.readonly_reqs[rid].is_Req() ==> s.readonly_reqs[rid].get_Req_version() <= s.version)

    &&& t.reqs.contains_key(rid)
    &&& t.reqs[rid] == InputOperation::<DT>::Read(s.readonly_reqs[rid].op())

    &&& (r_points.contains_key(rid) ==> {
        &&& s.version <= r_points[rid]
        &&& (s.readonly_reqs[rid].is_Req() ==> s.version < r_points[rid])
    })
}

/// checks whether the readonly response is valid                          (Dafny: readonly_is_resp)
spec fn readonly_response_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Req()
    &&& s.readonly_reqs[rid].get_Req_version() <= s.version

    &&& t.resps.contains_key(rid)

    &&& (r_points.contains_key(rid) ==> {
        &&& s.readonly_reqs[rid].get_Req_version() <= r_points[rid] && r_points[rid] <= s.version
        &&& 0 <= r_points[rid] && r_points[rid] <= s.log.len()
        &&& t.resps[rid] == OutputOperation::<DT>::Read(DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), s.readonly_reqs[rid].op()))
    })
}

/// checks whether the update response is valid                              (Dafny: update_is_done)
spec fn update_response_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.update_resps.contains_key(rid)
    &&& s.update_resps[rid].0 < s.log.len()

    &&& t.resps.contains_key(rid)
    &&& t.resps[rid] == OutputOperation::<DT>::Write(
        DT::dispatch_mut_spec(s.nrstate_at_version(s.update_resps[rid].0), s.log[s.update_resps[rid].0 as int]).1
    )
}

/// checks whether the upate responses have versions that matche the log         (Dafny: HasVersion)
spec fn update_response_with_version(update_resps: Map<ReqId, UpdateResp>, version: LogIdx) -> bool
{
    exists |rid| #[trigger] update_resps.contains_key(rid) && update_resps[rid].0 == version
}


// =================================================================================================
// State Refinement Relation
// =================================================================================================


/// Basic State Refinement Relation                                               (Dafny: rel_basic)
/// sets the AsynchronousSingleton::State in realtion with the SimpleLog::State
spec fn state_refinement_relation_basic<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    // the version must be valid w.r.t. to the log size
    &&& (0 <= s.version && s.version <= s.log.len())
    // the state corresponds to the state computed at the given version
    &&& t.state == s.nrstate_at_version(s.version)

    // the request ids of the readonly/update requests and responses must be unique
    &&& s.readonly_reqs.dom().disjoint( s.update_reqs.dom())
    &&& s.readonly_reqs.dom().disjoint( s.update_resps.dom())
    &&& s.update_reqs.dom().disjoint( s.update_resps.dom())
    &&& t.reqs.dom().disjoint(t.resps.dom())

    // requests are complete: if a request in present in the AState then it must be present in the SState
    &&& (forall |rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) || #[trigger] s.update_reqs.contains_key(rid) || #[trigger] s.update_resps.contains_key(rid))
        <==>
        (#[trigger] t.reqs.contains_key(rid) || #[trigger] t.resps.contains_key(rid))
    )

    // requests/responses in the rightmaps
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Read()
            ==> s.readonly_reqs.contains_key(rid))
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Write()
            ==> s.update_reqs.contains_key(rid) || s.update_resps.contains_key(rid))
    &&& (forall |rid| #[trigger] t.resps.contains_key(rid)
            ==> s.readonly_reqs.contains_key(rid) || s.update_resps.contains_key(rid))

    // for all log entries > version, there must be a response with the given version
    &&& (forall |v: LogIdx|  s.version <= v && v < s.log.len() ==> update_response_with_version(s.update_resps, v))

    // for any two update responses, if the request id differs, the version in the log must also differ
    &&& (forall |rid1, rid2| #[trigger] s.update_resps.contains_key(rid1) && #[trigger] s.update_resps.contains_key(rid2) && rid1 != rid2
            ==> s.update_resps[rid1] != s.update_resps[rid2])

    // for all update responses, the version must be within the log
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid)
            ==> s.update_resps[rid].0 < s.log.len())

    // for all update requests, they must be part of the requests and the operation must match
    &&& (forall |rid| #[trigger] s.update_reqs.contains_key(rid)
            ==> t.reqs.contains_key(rid) && t.reqs[rid] == InputOperation::<DT>::Write(s.update_reqs[rid]))

    // forall update responses larger than the current version, they must be in the requests,
    // the update operation must match
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 >= s.version ==> {
        &&& t.reqs.contains_key(rid)
        &&& t.reqs[rid] == InputOperation::<DT>::Write(s.log[s.update_resps[rid].0 as int])
    })

    // for all update responses smaller than th eversion, they must be valid
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 < s.version ==>
        update_response_is_valid(s, t, r_points, rid)
    )
}

/// State Refinement Relation                                                           (Dafny: rel)
/// This relates the state of the SimpleLog and the AsyncSingleton to each other
spec fn state_refinement_relation<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool
{
    &&& state_refinement_relation_basic(s, t, r_points)
    &&& readonly_requests_valid(s, t, r_points)
}


// =================================================================================================
// State Transition Refinements: Read-Only Requests
// =================================================================================================


/// Refinement Proof of the ReadOnly_Start transition of the SimpleLog
///
/// This corresponds to the "Start" transition that introduces a new request into the system
proof fn readonly_start_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, rop: DT::ReadOperation) -> (t2: AState<DT>)
    requires
        SimpleLog::State::readonly_start(s, s2, aop, rid, rop),
        state_refinement_relation(s, t, r_points.remove(rid)), future_points_ok(s2, r_points)
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) // one.Next(Is, Is', AI.Start(rid, nrifc.ROp(rop)))
{
    // Is' := Is.(reqs := Is.reqs[rid := nrifc.ROp(rop)]);
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs.insert(rid, InputOperation::Read(rop)),
        resps: t.resps,
    };

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, aop, AsynchronousSingleton::Step::start(rid, InputOperation::Read(rop))));

    res
}

/// Refinement Proof of the Readonly_ReadVersion transition of the SimpleLog
///
/// This corresponds to an "InternalOp" transition
proof fn readonly_read_version_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::readonly_read_version(s, s2, aop, rid),
        state_refinement_relation(s, t, r_points), future_points_ok(s2, r_points)
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) // one.Next(Is, Is', AI.InternalOp)
{
    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    if r_points.contains_key(rid) && r_points[rid] == s.version {
        let op =  s.readonly_reqs[rid].get_Init_op();

        // remind verus that the request id is known!
        assert(t.reqs.contains_key(rid) || t.resps.contains_key(rid));

        let retval = DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), op);

        // Is' := Is.(reqs := Is.reqs - {rid})
        //         .(resps := Is.resps[rid := retval]);
        let res = AsynchronousSingleton::State {
            state: t.state,
            reqs: t.reqs.remove(rid),
            resps: t.resps.insert(rid, OutputOperation::Read(retval)),
        };

        assert(AsynchronousSingleton::State::next_by(t, res, aop, AsynchronousSingleton::Step::internal_next(rid, InputOperation::Read(op), OutputOperation::Read(retval))));
        res
    } else {
        // if the request id is not part of the supplied r_points then this corresponds to a no-op
        assert(AsynchronousSingleton::State::next_by(t, t, aop, AsynchronousSingleton::Step::no_op()));
        t
    }
}

/// Refinement Proof of the Readonly_Finish transition of the SimpleLog
///
/// This corresponds to a "End" transition where a response leaves the system
proof fn readonly_finish_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, version: LogIdx, ret: DT::Response) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::readonly_finish(s, s2, aop, rid, version, ret),
        state_refinement_relation(s, t, r_points.insert(rid, version)),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) // one.Next(Is, Is', AI.End(rid, return_value))
{
    // Is' := Is.(resps := Is.resps - {rid});
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs,
        resps: t.resps.remove(rid),
    };

    if t.reqs.contains_key(rid) {
        assert(false); // proof by contradiction
    } else {
        assert(t.resps.contains_key(rid));
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, aop, AsynchronousSingleton::Step::end(rid,  OutputOperation::Read(ret))));
    res
}


// =================================================================================================
// State Transition Refinements: Update Requests
// =================================================================================================


/// Refinement Proof of the Update_Start transition of the SimpleLog
///
/// This corresponds to the "Start" transition that introduces a new request into the system
proof fn update_start_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, uop: DT::WriteOperation) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_start(s, s2, aop, rid, uop),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) //  one.Next(Is, Is', AI.Start(rid, nrifc.UOp(uop)))
{
    //  Is' := Is.(reqs := Is.reqs[rid := nrifc.UOp(uop)]);
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs.insert(rid, InputOperation::Write(uop)),
        resps: t.resps,
    };

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, aop, AsynchronousSingleton::Step::start(rid,  InputOperation::Write(uop))));
    res
}


/// Refinement Proof of the Update_AddUpdateToLog transition of the SimpleLog
///
/// This corresponds to an "InternalOp transition"
proof fn update_add_update_to_log_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_add_op_to_log(s, s2, aop, rid),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) //  one.Next(Is, Is', AI.InternalOp)
{
    state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.version);

    assert forall |r| #[trigger] s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r)
        ==> readonly_response_is_valid(s2, t, r_points, r) by {
        if s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r) {
            if r_points.contains_key(r) {
                state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], r_points[r]);
            }
        }
    }

    assert forall |r| (#[trigger] s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version)
        ==> update_response_is_valid(s2, t, r_points, r) by {
        if s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version {
            state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.update_resps[r].0);
        }
    }

    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> update_response_with_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            if v < s2.log.len() - 1 {
                assert(update_response_with_version(s.update_resps, v));
                let qid = choose|qid| #[trigger]s.update_resps.contains_key(qid) && s.update_resps[qid].0 == v;
                assert(s2.update_resps.contains_key(qid) && s2.update_resps[qid].0 == v);
            } else {
                assert(s2.update_resps.contains_key(rid) && s2.update_resps[rid].0 == v);
            }
        }
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, t, aop, AsynchronousSingleton::Step::no_op()));
    t
}


/// Refinement Proof ot the Update_Finish transition of the SimpleLog
///
/// This corresponds to the "End" transition that removes a response from the system
proof fn update_finish_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, aop: AsyncLabel<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, resp: DT::Response) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_finish(s, s2, aop, rid, resp),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2, aop) //  one.Next(Is, Is', AI.End(rid, return_value))
{
    // Is' := Is.(resps := Is.resps - {rid});
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs,
        resps: t.resps.remove(rid),
    };

    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> update_response_with_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            assert(update_response_with_version(s.update_resps, v));
            let qid = choose|qid| #[trigger]s.update_resps.contains_key(qid) && s.update_resps[qid].0 == v;
            assert(s2.update_resps.contains_key(qid) && s2.update_resps[qid].0 == v);

        }
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, aop, AsynchronousSingleton::Step::end(rid, OutputOperation::Write(resp))));
    res
}


/// Refinement Proof of the Update_IncrVersion transition of the SimpleLog
///
/// This corresponds to an internal, or next transition
proof fn update_incr_version_refines<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>, new_version: LogIdx) -> (b: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(), future_points_ok(a.get_last(), r_points), a.is_Stepped(), a.get_Stepped_1().is_Internal(),
        SimpleLog::State::update_incr_version(a.get_Stepped_2().get_last(), a.get_last(), AsyncLabel::Internal, new_version),
    ensures
        b.wf(), behavior_equiv(a, b), state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases
        *a.get_Stepped_2(), 1nat, new_version
{
    if new_version == a.get_Stepped_2().get_last().version {
        exists_equiv_behavior_rec(*a.get_Stepped_2(), r_points)
    } else {
        /* var amid := a.(s := a.s.(ctail := a.s.ctail - 1)); */
        let mut new_st = a.get_Stepped_0();
        new_st.version = (new_st.version - 1) as nat;
        let amid = SimpleLogBehavior::Stepped(
            new_st,
            a.get_Stepped_1(),
            a.get_Stepped_2(),
        );

        reveal(SimpleLog::State::next);
        reveal(SimpleLog::State::next_by);
        assert(SimpleLog::State::next_by(amid.get_Stepped_2().get_last(), amid.get_last(), AsyncLabel::Internal, SimpleLog::Step::update_incr_version((new_version - 1) as nat)));

        let bmid = update_incr_version_refines(amid, r_points, (new_version - 1) as LogIdx);
        update_incr_version_1_refines(bmid, amid, a, r_points)
    }
}


proof fn update_incr_version_1_refines<DT: Dispatch>(b: AsynchronousSingletonBehavior<DT>, a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>) -> (b2: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(), future_points_ok(a2.get_last(), r_points),
        a.is_Stepped() && a2.is_Stepped(),
        a.get_Stepped_2() == a2.get_Stepped_2(), // a.tail == a'.tail
        a.get_Stepped_1().is_Internal() && a2.get_Stepped_1().is_Internal(),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
        a.get_last().version + 1 <= a.get_last().log.len(),
        b.wf(),
        behavior_equiv(a, b),
        state_refinement_relation(a.get_last(), b.get_last(), r_points)
    ensures
        b2.wf(), behavior_equiv(a2, b2), state_refinement_relation(a2.get_last(), b2.get_last(), r_points)
{
    let s = a.get_last();
    let s2 = a2.get_last();

    assert(s.version < s.log.len());
    assert(update_response_with_version(s.update_resps, s.version));

    let urid  = choose |urid| #[trigger] s.update_resps.contains_key(urid) && s.update_resps[urid].0 == s.version;

    let x = DT::dispatch_mut_spec(s.nrstate_at_version(s.update_resps[urid].0), s.log[s.update_resps[urid].0 as int]);
    let uret = x.1;

    let input = InputOperation::Write(s.log[s.update_resps[urid].0 as int]);
    let output = OutputOperation::Write(uret);

    let st = AsynchronousSingleton::State {
        state: x.0,
        reqs: b.get_last().reqs.remove(urid),
        resps: b.get_last().resps.insert(urid, output),
    };
    let b2 = AsynchronousSingletonBehavior::Stepped(st, AsyncLabel::Internal, Box::new(b));

    assert(b2.wf()) by {
        reveal(AsynchronousSingleton::State::next);
        reveal(AsynchronousSingleton::State::next_by);
        assert(AsynchronousSingleton::State::next_by(b2.get_Stepped_2().get_last(), b2.get_last(), AsyncLabel::Internal,  AsynchronousSingleton::Step::internal_next(urid, input, output)));
    }


    assert(behavior_equiv(a2, b2)) by { trick_equiv(a, a2, b2); }

    let the_reads = all_reads_for::<DT>(s.readonly_reqs, r_points, s.version + 1);
    update_incr_version_1_read_reqs(b2, a, a2, r_points, the_reads)
}

spec fn simple_log_state_equiv_inc_version<DT: Dispatch>(a: SState<DT>, a2: SState<DT>) -> bool {
    // a'.s == a.s.(ctail := a.s.ctail + 1)
    &&& a2.log == a.log
    &&& a2.version == a.version + 1
    &&& a2.readonly_reqs == a.readonly_reqs
    &&& a2.update_reqs == a.update_reqs
    &&& a2.update_resps == a.update_resps
}

spec fn recursion_invariant<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t2: AState<DT>, r_points: Map<ReqId, LogIdx>, the_reads: Set<ReqId>) -> bool {
    &&& the_reads.finite()
    &&& s.version + 1 <= s.log.len()
    &&&  state_refinement_relation_basic(s2, t2, r_points)
    &&& (forall |rid| #[trigger]the_reads.contains(rid) ==> {
        &&& r_points.contains_key(rid)
        &&& r_points[rid] == s.version + 1
        &&& s.readonly_reqs.contains_key(rid)
        &&& s.readonly_reqs[rid].is_Req()
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
        !the_reads.contains(rid) ==> readonly_request_is_valid(s2, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
        !the_reads.contains(rid) ==> readonly_response_is_valid(s2, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
        the_reads.contains(rid) ==> readonly_request_is_valid(s, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
        the_reads.contains(rid) ==> readonly_response_is_valid(s, t2, r_points, rid)
    })
}

proof fn update_incr_version_1_read_reqs<DT: Dispatch>(b2: AsynchronousSingletonBehavior<DT>, a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>, the_reads: Set<ReqId>) -> (res: AsynchronousSingletonBehavior<DT>)
    requires
        b2.wf(), behavior_equiv(a2, b2),
        recursion_invariant(a.get_last(), a2.get_last(), b2.get_last(), r_points, the_reads),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
    ensures
        res.wf(), behavior_equiv(a2, res),
        recursion_invariant(a.get_last(), a2.get_last(), res.get_last(), r_points, Set::<ReqId>::empty()),
    decreases
        the_reads.len()
{
    if the_reads.is_empty() {
        assert(the_reads =~= Set::empty());
        b2
    } else {
        let s = a.get_last();
        let s2 = a2.get_last();

        let (the_reads2, rid) = pop_rid(the_reads);

        let ret = DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), s.readonly_reqs[rid].op());
        let input = InputOperation::<DT>::Read(s.readonly_reqs[rid].op());
        let output = OutputOperation::Read(ret);

        let st = AsynchronousSingleton::State {
            state: b2.get_last().state,
            reqs: b2.get_last().reqs.remove(rid),
            resps: b2.get_last().resps.insert(rid, output),
        };
        let b2_new = AsynchronousSingletonBehavior::Stepped(st, AsyncLabel::Internal, Box::new(b2));

        assert(b2_new.wf()) by {
            reveal(AsynchronousSingleton::State::next);
            reveal(AsynchronousSingleton::State::next_by);
            assert(AsynchronousSingleton::State::internal_next(b2.get_last(), b2_new.get_last(), AsyncLabel::Internal, rid, input, output));
            assert(AsynchronousSingleton::State::next_by(b2.get_last(), b2_new.get_last(), AsyncLabel::Internal,
                AsynchronousSingleton::Step::internal_next(rid, input, output)
            ));
        }

        update_incr_version_1_read_reqs(b2_new, a, a2, r_points, the_reads2)
    }
}


// =================================================================================================
// Utility Functions
// =================================================================================================

/// Shows that adding an entry to the log doesn't change the state
proof fn state_at_version_preserves<DT: Dispatch>(a: Seq<DT::WriteOperation>, b: Seq<DT::WriteOperation>, x: DT::WriteOperation, i: LogIdx)
    requires b == a.push(x), i <= a.len(), i <= b.len()
    ensures compute_nrstate_at_version::<DT>(a, i) == compute_nrstate_at_version::<DT>(b, i)
    decreases i
{
    if i > 0 {
        state_at_version_preserves::<DT>(a, b, x, (i-1) as LogIdx);
    }
}

/// Removes an element from the set, returning it, maintaining finitenes property
/// XXX: something like this shoudl go intot he stdlib...
proof fn pop_rid(t: Set<ReqId>) -> (res: (Set<ReqId>, ReqId))
    requires !t.is_empty(), t.finite()
    ensures res.0.len() < t.len(), t.contains(res.1), res.0 =~= t.remove(res.1), res.0.finite()
{
    let r = t.choose();
    (t.remove(r), r)
}

/// Shows the behavior equivalency under specific condition
proof fn trick_equiv<DT: Dispatch>(a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, b: AsynchronousSingletonBehavior<DT>)
    requires
        behavior_equiv(a, b), a.is_Stepped(), a2.is_Stepped(), a.get_Stepped_2() == a2.get_Stepped_2(),
        a.get_Stepped_1().is_Internal(), a2.get_Stepped_1().is_Internal()
    ensures
        behavior_equiv(a2, b)
    decreases b
{
    if !b.is_Inited() &&  behavior_equiv(a, *b.get_Stepped_2()) {
        trick_equiv(a, a2, *b.get_Stepped_2());
    }
}


/// Constructs a set of Requests IDs that corresponds to ReadOnly requests and that are currently
/// in the r_points set and have a version that matches the input
spec fn all_reads_for<DT: Dispatch>(readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>, r_points: Map<ReqId, LogIdx>, version: LogIdx) -> Set<ReqId>
    recommends r_points.dom().finite()
{
    r_points.dom().filter(|rid| r_points[rid] == version && readonly_reqs.contains_key(rid) && readonly_reqs[rid].is_Req())
}


} // end verus!

}


// the simple log model
pub mod simple_log{
#[allow(unused_imports)]

// trusted: top level
//#![verus::trusted]

use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use crate::{AsyncLabel, InputOperation, OutputOperation};

use vstd::prelude::*;

use super::types::*;

use crate::Dispatch;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Simple Log
// ==========
//
// The Simple Log is capturing requests to a data structure in an abstract and unbouned log
// represented as a mathematical sequence. In contrast to the node replication algorithm, the
// Simple Log does not store / wrap a data structure. Instead, it stores all update operations
// in the sequence. The state of the data structure is derived based on the version after N update
// operations have been applied. The version of the data structure is defined by the value of teh
// completion tail (ctail) at the time the operation is dispatched.
//
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Simple Log State Machine
////////////////////////////////////////////////////////////////////////////////////////////////////

vstd::prelude::verus! {

/// Represents the state of a read-request
#[is_variant]
pub ghost enum ReadReq<R> {
    /// a new read request that has entered the system
    Init { op: R },
    /// a request that has been dispatched at a specific version
    Req { version: LogIdx, op: R },
}

impl<R> ReadReq<R> {
    pub open spec fn op(self) -> R {
        match self {
            ReadReq::Init { op } => op,
            ReadReq::Req { op, ..} => op
        }
    }
}

/// Represents the state of an update requeset, returning the index of the update in the log
pub ghost struct UpdateResp(pub LogIdx);

state_machine! {
    SimpleLog<DT: Dispatch> {
        fields {
            /// a sequence of update operations,
            pub log: Seq<DT::WriteOperation>,
            /// the completion tail current index into the log
            pub version: LogIdx,
            /// in flight read requests
            pub readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>,
            /// inflight update requests
            pub update_reqs: Map<ReqId, DT::WriteOperation>,
            /// responses to update requests that haven't been returned
            pub update_resps: Map<ReqId, UpdateResp>,
        }

        pub type Label<DT> = AsyncLabel<DT>;

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Invariant
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// the version of the log must be less than the length of the log
        #[invariant]
        pub fn inv_version(&self) -> bool {
            self.version <= self.log.len()
        }

        /// all update responses must have version that are less than the length of the log
        #[invariant]
        pub fn inv_update_resp_version(&self) -> bool {
            forall |rid: ReqId| {
                #[trigger] self.update_resps.contains_key(rid)
                ==> self.update_resps[rid].0 < self.log.len()
            }
        }

        /// all readonly requests must have a version that is less or equal to the log version
        #[invariant]
        pub fn inv_readonly_req_version(&self) -> bool {
            forall |rid: ReqId| {
                self.readonly_reqs.contains_key(rid)
                ==> if let ReadReq::<DT::ReadOperation>::Req { version, .. } = self.readonly_reqs[rid] {
                        version <= self.version}
                    else { true }
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // State Machine Initialization
        ////////////////////////////////////////////////////////////////////////////////////////////


        init!{
            initialize() {
                init log = Seq::empty();
                init version = 0;
                init readonly_reqs = Map::empty();
                init update_reqs = Map::empty();
                init update_resps = Map::empty();
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // Constructing the DataStructureSpec
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// constructs the state of the data structure at a specific version given the log
        ///
        /// This function recursively applies the update operations to the initial state of the
        /// data structure and returns the state of the data structure at the given  version.
        pub open spec fn nrstate_at_version(&self, version: LogIdx) -> DT::View
            recommends 0 <= version <= self.log.len()
        {
            compute_nrstate_at_version::<DT>(self.log, version)
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        //
        // Read Operation Transitions
        // --------------------------
        //
        // Readonly operations are carried out in three steps:
        //  0. Add the request to the system (readonly requests)
        //  1. When a 'readonly' request begins record the version of the log.
        //  2. When it ends, we must return the answer at some version >= the recorded value.
        //
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// Read Request: Enter the read request operation into the system
        transition!{
            readonly_start(label: Label<DT>, rid: ReqId, op: DT::ReadOperation) {
                require label == AsyncLabel::<DT>::Start(rid, InputOperation::Read(op));
                require(!pre.readonly_reqs.contains_key(rid));
                require(!pre.update_reqs.contains_key(rid));
                require(!pre.update_resps.contains_key(rid));

                update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Init{ op };
            }
        }

        /// Read Request: Read the current version of the log
        transition!{
            readonly_read_version(label: Label<DT>, rid: ReqId) {
                require label.is_Internal();
                require(pre.readonly_reqs.contains_key(rid));
                require let ReadReq::<DT::ReadOperation>::Init { op } = pre.readonly_reqs.index(rid);

                update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Req { op, version: pre.version };
            }
        }

        /// Read Request: Remove the request from the system
        ///
        /// This computes the state at version the request started
        transition!{
            readonly_finish(label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) {
                require label == AsyncLabel::<DT>::End(rid, OutputOperation::Read(ret));

                require(pre.readonly_reqs.contains_key(rid));

                require let ReadReq::<DT::ReadOperation>::Req { op, version: current } = pre.readonly_reqs.index(rid);

                require(current <= version <= pre.log.len());
                require(version <= pre.version);
                require(ret == DT::dispatch_spec(pre.nrstate_at_version(version), op));

                update readonly_reqs = pre.readonly_reqs.remove(rid);
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        //
        // Update Operation Transitions
        // ----------------------------
        //
        // Update operation happen in two steps:
        //  1. add the update to the local update requests
        //  2. collect the updates and store them in the log
        //  3. increase the version of the log
        //  4. return the version of the log at the update
        //
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// Update Request: place an update request in the system
        transition!{
            update_start(label: Label<DT>, rid: ReqId, op: DT::WriteOperation) {
                require label == AsyncLabel::<DT>::Start(rid, InputOperation::Write(op));

                require(!pre.readonly_reqs.contains_key(rid));
                require(!pre.update_reqs.contains_key(rid));
                require(!pre.update_resps.contains_key(rid));

                update update_reqs[rid] = op;
            }
        }

        /// Update Request: Add the update operations to the log
        ///
        /// Collect the updates given by the sequence of requests ids and place them in the log
        /// in-order. This moves the requests from update_reqs to update_resps.
        // transition!{
        //     update_add_ops_to_log(rids: Seq<ReqId>) {
        //         // all request ids must be in the update requests
        //         require(forall |r: ReqId|  #[trigger] rids.contains(r) ==> pre.update_reqs.contains_key(r));
        //         // the request ids must be unique, the sequence defines the update order
        //         require(seq_unique(rids));

        //         // add the update operations to the log
        //         update log = pre.log + Seq::new(rids.len(), |i: int| pre.update_reqs[i as nat]);

        //         // remove all update requests
        //         update update_reqs = pre.update_reqs.remove_keys(Set::new(|i| rids.contains(i)));

        //         // add the responses to the update requests
        //         update update_resps = pre.update_resps.union_prefer_right(
        //                 Map::new(|r: ReqId| { rids.contains(r) },
        //                          |r: ReqId| { UpdateResp(pre.log.len() + rids.index_of(r) as nat)})
        //         );
        //     }
        // }

        /// Update Request: Add the update operations to the log
        ///
        /// Collect the updates given by the sequence of requests ids and place them in the log
        /// in-order. This moves the requests from update_reqs to update_resps.
        transition!{
            update_add_op_to_log(label: Label<DT>, rid: ReqId) {
                require label.is_Internal();

                // all request ids must be in the update requests
                require(pre.update_reqs.contains_key(rid));

                // add the update operations to the log
                update log = pre.log.push(pre.update_reqs[rid]);

                // remove all update requests
                update update_reqs = pre.update_reqs.remove(rid);

                // add the responses to the update requests
                update update_resps = pre.update_resps.insert(rid, UpdateResp(pre.log.len()));
            }
        }

        /// Update: Increasing the version of the log
        ///
        /// The version value is monotonically increasing and must not be larger than the
        /// length of the log.
        transition!{
            update_incr_version(label: Label<DT>, new_version: LogIdx) {
                require label.is_Internal();

                require(pre.version <= new_version <= pre.log.len());
                update version = new_version;
            }
        }

        /// Update: Finish the update operation by removing it from the update responses
        transition!{
            update_finish(label: Label<DT>, rid: nat, ret: DT::Response) {
                require label == AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));

                require(pre.update_resps.contains_key(rid));
                let uidx = pre.update_resps.index(rid).0;

                require(pre.version > uidx);
                require(pre.log.len() > uidx);
                require(ret == DT::dispatch_mut_spec(pre.nrstate_at_version(uidx), pre.log[uidx as int]).1);

                update update_resps = pre.update_resps.remove(rid);
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // Stutter Step
        ////////////////////////////////////////////////////////////////////////////////////////////


        transition!{
            no_op(label: Label<DT>, ) {
                require label.is_Internal();
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // Inductiveness Proofs
        ////////////////////////////////////////////////////////////////////////////////////////////


        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(readonly_start)]
        fn readonly_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::ReadOperation) { }

        #[inductive(readonly_read_version)]
        fn readonly_read_version_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

        #[inductive(readonly_finish)]
        fn readonly_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) { }

        #[inductive(update_start)]
        fn update_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::WriteOperation) { }

        // #[inductive(update_add_ops_to_log)]
        // fn update_add_ops_to_log_inductive(pre: Self, post: Self, rids: Seq<ReqId>) { }

        #[inductive(update_add_op_to_log)]
        fn update_add_op_to_log_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

        #[inductive(update_incr_version)]
        fn update_incr_version_inductive(pre: Self, post: Self, label: Label<DT>, new_version: LogIdx) { }

        #[inductive(update_finish)]
        fn update_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: nat,  ret: DT::Response) { }

        #[inductive(no_op)]
        fn no_op_inductive(pre: Self, post: Self, label: Label<DT>) { }
    }
}

}

verus! {

/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given  version.
pub open spec fn compute_nrstate_at_version<DT: Dispatch>(log: Seq<DT::WriteOperation>, version: LogIdx) -> DT::View
    recommends 0 <= version <= log.len()
    decreases version
{
    // decreases_when(version >= 0);
    if version == 0 {
        DT::init_spec()
    } else {
        DT::dispatch_mut_spec(compute_nrstate_at_version::<DT>(log, (version - 1) as nat), log[version - 1]).0
    }
}

}

}


// unbounded log and refinement
#[macro_use]
pub mod unbounded_log{
// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::map::Map;
use vstd::seq::Seq;
use vstd::set::Set;

use state_machines_macros::*;

use crate::Dispatch;

use super::types::*;
use super::utils::*;

vstd::prelude::verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Unbounded Log
// =============
//
// ...
//
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Read Only Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// ReadonlyState: Tracking the progress of read-only queries
///
/// Used to track the progress of a read-only queries on the data structure.
///
/// A readonly query takes place on a given node (`nid`), and follows the following algorithm:
///
///  1. Read the global value 'version_upper_bound'.
///  2. Wait until node-local value 'local_head' is greater than the value
///     of 'version_upper_bound' that was read in step 1.
///  3. Execute the query against the node-local replica and return the result.
///
/// (In real life, the thread does not just sit around 'waiting' in step 2;
/// it might run a combiner phase in order to advance the local_head.)
///
/// These 3 steps progress the status of the request through the cycle
///    Init -> VersionUpperBound -> ReadyToRead -> Done
///
/// Note that the request itself does not "care" which nodeId it takes place on;
/// we only track the nodeId to make sure that steps 2 and 3 use the same node.
///
#[is_variant]
pub ghost enum ReadonlyState<DT: Dispatch> {
    /// a new read request that has come in
    Init { op: DT::ReadOperation },
    /// has read the version upper bound value
    VersionUpperBound {
        op: DT::ReadOperation,
        version_upper_bound: LogIdx,
    },
    /// ready to read
    ReadyToRead {
        op: DT::ReadOperation,
        node_id: NodeId,
        version_upper_bound: LogIdx,
    },
    /// read request is done
    Done {
        op: DT::ReadOperation,
        ret: DT::Response,
        node_id: NodeId,
        version_upper_bound: LogIdx,
    },
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Update Operation
////////////////////////////////////////////////////////////////////////////////////////////////////

////////// Updates and the combiner phase
//
// This part is a lot more complex; the lifecycle of an "update" is inherently
// tied to the lifecycle of the combiner, so I have to explain the entire combiner
// cycle for this to make sense.
//
// In particular, the combiner cycle starts with some (potentially empty) bulk collection
// of Update requests, which all start in UpdateState::Init.
// By the end of the combiner cycle (when it has gone back to 'Ready'), all the updates
// in that collection will be in UpdateState::Done.
//
// The combiner works as follows (keep in mind this is abstracted a bit from the
// real implementation).
//
//  1. Advance the 'tail' value by 1 for each update in the collection.
//     This creates a "LogEntry" for the given op at the given index.
//     It also updates the update from UpdateState::Init to UpdateState::Placed.
//
//      Note: This always appends to the log; there are never any "holes" in the log,
//      and the 'tail' always marks the end of the log. The log is unbounded
//      and not garbage-collected.
//      Keep in mind that the 'log' here is just an abstraction, and the "cyclic buffer"
//      that physically stores the log entries in real life has additional complexities.
//      We do not handle those complexities at this level of abstraction.
//
//      Note: Even when we have a bulk collection of updates, we still append the log
//      entries one at a time, once for each update. This means the log entries might
//      interleave with those of another thread.
//      This is more permissive than the real implementation, which advances the
//      'tail' with a single CAS operation, meaning that all the log entries
//      for the cycle will be contiguous in the log.
//      In the original Linear Dafny NR project, we modeled this step as a bulk update,
//      matching the implemenation. However, it turned out that:
//          (i) modeling 'bulk update' steps is kind of annoying
//          (ii) we never took advantage of the contiguity in the invariants
//      Since the single-step version is easier to model, and we don't lose anything for it,
//      that's what we do here.
//
//  2. Read the 'local_head' value for the given node.
//
//  3. Read the global 'tail' value.
//
//  4. Process all log entries in the range local_head..tail.
//     (This should include both the log entries we just creates, plus maybe some other
//     log entries from other nodes.)
//
//      NOTE: the global 'tail' value might change over the course of execution,
//      but we're going to stick with the local copy that we just read
//      (i.e., the value on the stack).
//
//     To process a log entry, we first apply the operation to the replica, and get
//     back a "return value". Next, we check if the log entry is for the given nodeId,
//     classifying it as "remote" or "local".
//      - If it's remote, we're done.
//      - If it's local, then we find the Update object in our bulk collection, and
//        update it from UpdateState::Placed to UpdateState::Applied, recording the
//        return value.
//
//  5. Update the global value of 'version_upper_bound'.
//     This step lets us move all the updates to UpdateState::Done.
//
//  6. Update the value of 'local_head'.
//
// Now, there are a bunch of things we need to prove so that the whole thing makes sense
// and so that the implementation can actually follow along and return data to the clients.
//
// Specifically, we have a sequence of "return ids" (recorded in the 'queued_ops' field)
// that need to get processed. When the implementation handles a "local" operation off the
// log, it appends the return value into a buffer; when it's done, it expects the buffer
// of return values to line up with all the update requests that it started with.
//
// What this means is that we need to show:
//   - When we process a "local" operation, its ReqId corresponds to the next
//     ReqId recorded in the queued_ops (i.e., the one at 'queue_index'.)
//   - When we have finished the entire loop, we have finished processing all
//     the ReqIds we expected (i.e., `queue_index == queued_ops.len()`).
//
// This means we need to establish an invariant between the combiner state and the
// log state at all times. Specifically, we need an invariant that relates the combiner
// state to the log entries whose node_ids match the combiner's node, describing where
// they are and in what order.
//
// The invariant roughly says that during step (4), (the "Loop" state):
//   The ReqIds in `queued_ops`, sliced from queue_index .. queued_ops.len()
//   match
//   The ReqIds in the log that are local, sliced from
//          local_head .. tail
// (Note that queue_index and local_head are the cursors that advance throughout the loop,
// while tail is the one recorded in step 3, so it's fixed.)
// Furthermore:
//   There are no local operations in the log between
//   the recorded tail and the global tail.
// See the invariant `wf_combiner_for_node_id`, as well as the predicates
// `LogRangeMatchesQueue` and `LogRangeNoNodeId`.
//
// Example: suppose N is the local node_id, and [a, b, c, d] are the request ids.
// We might be in a state that looks like this: (Here, '...' indicates remote entries,
// and '(N, x)' means a log entry with node id N that corresponds to request id x.)
//
//       CombinerState                                           CombinerState   global
//       local_head                                              tail     tail
//          |                                                              |               |
//       ===================================================================================
//          |          |       |       |        |       |          |       |       |       |
//  Log:    |  (N, b)  |  ...  |  ...  | (N, c) |  ...  |  (N, d)  |  ...  |  ...  |  ...  |
//          |          |       |       |        |       |          |       |       |       |
//       ===================================================================================
//
//  ---- Combiner state (in `CombinerState::Loop` phase).
//
//      queued_ops =  [  a,   b,   c,   d   ]
//                          ^
//                          |
//                  queue_index = 1
//
// ---- Update state:
//
//    a => UpdateState::Applied { ... }
//    b => UpdateState::Placed { ... }
//    c => UpdateState::Placed { ... }
//    d => UpdateState::Placed { ... }
//
// In the example, `LogRangeMatchesQueue` is the relation that shows that (b, c, d)
// agree between the queued_ops and the log; whereas `LogRangeNoNodeId` shows that there
// are no more local entries between the Combiner tail and the global tail.
//
// And again, in the real implementation, b, c, d will actually be contiguous in the log,
// but the state shown above is permitted by the model here.
// If we _were_ going to make use of contiguity, then the place to do it would probably
// be the definition of `LogRangeMatchesQueue`, but as I explained earlier, I didn't
// find it helpful.
//
// Another technical note: the LogEntry doesn't actually store the ReqId on it;
// `LogRangeMatchesQueue` has to connect the request id to the UpdateState, which then
// has a pointer into the log via `idx`. (It's possible that this could be simplified.)

#[is_variant]
pub ghost enum UpdateState<DT: Dispatch> {
    /// upated request has entered the system
    Init { op: DT::WriteOperation },
    /// update has been placed into the log
    Placed { op: DT::WriteOperation, idx: LogIdx },
    /// the update has been applied to the data structure
    Applied { ret: DT::Response, idx: LogIdx },
    /// the update is ready to be returned
    Done { ret: DT::Response, idx: LogIdx },
}

#[is_variant]
pub ghost enum CombinerState {
    Ready,
    Placed {
        queued_ops: Seq<ReqId>,
    },
    LoadedLocalVersion {
        queued_ops: Seq<ReqId>,
        lversion: LogIdx,
    },
    Loop {
        /// sequence of request ids of the local node
        queued_ops: Seq<ReqId>,
        /// version of the local replica
        lversion: LogIdx,
        /// index into the queued ops
        idx: nat,
        /// the global tail we'v read
        tail: LogIdx,
    },
    UpdatedVersion {
        queued_ops: Seq<ReqId>,
        tail: LogIdx,
    },
}

impl CombinerState {
    pub open spec fn queued_ops(self) -> Seq<ReqId> {
        match self {
            CombinerState::Ready => Seq::empty(),
            CombinerState::Placed{queued_ops} => queued_ops,
            CombinerState::LoadedLocalVersion{queued_ops, ..} => queued_ops,
            CombinerState::Loop{queued_ops, ..} => queued_ops,
            CombinerState::UpdatedVersion{queued_ops, ..} => queued_ops,
        }
    }

    pub open spec fn queued_ops_set(&self) -> Set<ReqId> {
        seq_to_set(self.queued_ops())
    }

}

} // end verus!

tokenized_state_machine! {
UnboundedLog<DT: Dispatch> {
    fields {
        /// the number of replicas
        #[sharding(constant)]
        pub num_replicas: nat,

        #[sharding(map)]
        pub log: Map<LogIdx, LogEntry<DT>>,

        #[sharding(variable)]
        pub tail: nat,

        #[sharding(map)]
        pub replicas: Map<NodeId, DT::View>,

        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>, // previously called "local tails"

        #[sharding(variable)]
        pub version_upper_bound: LogIdx, // previously called "ctail"

        #[sharding(map)]
        pub local_reads: Map<ReqId, ReadonlyState<DT>>,

        #[sharding(map)]
        pub local_updates: Map<ReqId, UpdateState<DT>>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState>
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////

    #[invariant]
    pub fn inv_request_ids_finite(&self) -> bool {
        &&& self.local_reads.dom().finite()
        &&& self.local_updates.dom().finite()
        &&& self.combiner.dom().finite()
    }

    // /// there must be a replicat for all nodes
    // #[invariant]
    // pub fn inv_replicas_complete(&self) -> bool {
    //     forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
    //         self.replicas.contains_key(node_id)
    // }

    // /// ther emust be a local version for all nodes
    // #[invariant]
    // pub fn inv_local_versions_complete(&self) -> bool {
    //     forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
    //         self.local_versions.contains_key(node_id)
    // }

    /// there must be a combiner for all node
    #[invariant]
    pub fn inv_local_combiner_complete(&self) -> bool {
        forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
            self.combiner.contains_key(node_id)
    }

    #[invariant]
    pub fn combiner_local_versions_domains(&self) -> bool {
        forall |k| self.local_versions.contains_key(k) <==> self.combiner.contains_key(k)
    }

    #[invariant]
    pub fn combiner_replicas_domains(&self) -> bool {
        forall |k| #![auto] self.replicas.contains_key(k) <==> self.combiner.contains_key(k)
    }

    pub open spec fn wf_node_id(&self, node_id: NodeId) -> bool {
        &&& 0 <= node_id < self.num_replicas
        &&& self.combiner.contains_key(node_id)
        &&& self.local_versions.contains_key(node_id)
        &&& self.replicas.contains_key(node_id)
    }


    // #[invariant]
    // pub fn inv_queued_ops_in_local_updates(&self) -> bool {
    //     forall |node_id, rid|
    //         (#[trigger] self.combiner.contains_key(node_id) && !(#[trigger] self.local_updates.contains_key(rid)))
    //             ==> !self.combiner[node_id].queued_ops().contains(rid)
    // }



    // && Inv_WF(s)
    // && Inv_GlobalTailCompleteTailOrdering(s)

    /// the version upper bound must be smaller or equal to the global tail
    /// Inv_GlobalTailCompleteTailOrdering
    #[invariant]
    pub fn inv_version_in_range(&self) -> bool {
        self.version_upper_bound <= self.tail
    }


    /// all local versions are less or equal to the version upper bound
    /// Inv_CompletedTailLowerBound && Inv_GlobalTailLowerBound(s)
    #[invariant]
    pub fn inv_local_version_upper_bound_heads(&self) -> bool {
        forall |node_id| (#[trigger]  self.local_versions.contains_key(node_id))
            ==> self.local_versions[node_id] <= self.version_upper_bound
    }


    /// The read request states are valid
    /// Inv_ReadRequest_WF(s) && Inv_ReadOnlyCtailsCompleteTailOrdering(s) && Inv_ReadOnlyStateNodeIdExists(s)
    #[invariant]
    pub fn inv_readonly_requests_wf(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
             ==> self.wf_readstate(self.local_reads[rid])
    }

    pub open spec fn wf_readstate(&self, rs: ReadonlyState<DT>) -> bool {
        match rs {
            ReadonlyState::Init{op} => {
                true
            }
            ReadonlyState::VersionUpperBound{op, version_upper_bound} => {
                version_upper_bound <= self.version_upper_bound
            }
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
            ReadonlyState::Done{op, ret, node_id, version_upper_bound } => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
        }
    }


    /// the combiner states are wellformed
    /// Inv_CombinerStateValid(s)
    #[invariant]
    pub open spec fn combiner_states_wf(&self) -> bool {
        forall |node_id| (#[trigger] self.combiner.contains_key(node_id))
             ==> self.wf_combiner_for_node_id(node_id)
    }

    pub open spec fn wf_combiner_for_node_id(&self, node_id: NodeId) -> bool
        recommends self.wf_node_id(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready => {
                // from other inv
                // &&& self.local_versions.contains_key(node_id)
                // &&& self.local_versions[node_id] <= self.tail
                &&& LogRangeNoNodeId(self.log, self.local_versions[node_id], self.tail, node_id)
            }
            CombinerState::Placed { queued_ops } => {
                // &&& self.local_versions.contains_key(node_id)
                // &&& self.local_versions[node_id] <= self.tail
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, self.local_versions[node_id], self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
               // we've just read the local tail value, and no-one else should modify that
                &&& lversion == self.local_versions[node_id]
                // by transitivity we have lversion <= self.version_upper_bound and self.tail
                // the local tail should be smaller or equal than the ctail
                // &&& lversion <= self.version_upper_bound
                // &&& lversion <= self.tail
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, lversion, self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                // the global tail may have already advanced...
                &&& tail <= self.tail
                // we're advancing the local tail here
                &&& lversion >= self.local_versions[node_id]
                // the local tail should always be smaller or equal to the global tail
                &&& lversion <= tail
                // the log now contains all entries up to localtail
                &&& LogContainsEntriesUpToHere(self.log, lversion)
                &&& 0 <= idx <= queued_ops.len()
                &&& LogRangeMatchesQueue(queued_ops, self.log, idx, lversion, tail, node_id, self.local_updates)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, idx)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, idx)
                &&& seq_unique(queued_ops)
            }
            CombinerState::UpdatedVersion{ queued_ops, tail } => {
                // the global tail may have already advanced...
                // tail <= self.tail // by transitivity: self.version_upper_bound <= self.tail
                // update the ctail value
                &&& tail <= self.version_upper_bound
                // the local tail should be smaller than this one here
                &&& self.local_versions[node_id] <= tail
                // the log now contains all entries up to tail
                &&& LogContainsEntriesUpToHere(self.log, tail)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, queued_ops.len())
                &&& seq_unique(queued_ops)
            }
        }
    }


    /// the log contains entries up to the global tail
    /// Inv_LogEntriesGlobalTail(s)
    ///
    /// Inv_LogEntriesUpToCTailExists(s) && Inv_LogEntriesUpToLocalTailExist(s) are implied
    #[invariant]
    pub fn inv_log_complete(&self) -> bool {
        &&& LogContainsEntriesUpToHere(self.log, self.tail)
        &&& LogNoEntriesFromHere(self.log, self.tail)
    }


    /// Wellformed local update state
    /// Inv_LocalUpdatesIdx(s)
    #[invariant]
    pub fn inv_local_updates(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.inv_local_updates_wf(self.local_updates[rid])
    }

    pub open spec fn inv_local_updates_wf(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Init { op } => { true },
            UpdateState::Placed { op: _, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Applied { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Done { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.version_upper_bound
            },
        }
    }


    /// The results of the read operation must match
    /// Inv_ReadOnlyResult(s)
    #[invariant]
    pub fn inv_read_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
            ==>  self.read_results_match(self.local_reads[rid])
    }

    pub open spec fn read_results_match(&self, read: ReadonlyState<DT>) -> bool {
        match read {
            ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                exists |v: nat| (#[trigger] rangeincl(version_upper_bound, v, self.version_upper_bound))
                    && ret == DT::dispatch_spec(compute_nrstate_at_version(self.log, v), op)
            },
            _ => true,
        }
    }


    /// The results of the updates must match
    /// Inv_UpdateResults(s)
    #[invariant]
    pub fn inv_update_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.update_results_match(self.local_updates[rid])
    }

    pub open spec fn update_results_match(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Applied { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            UpdateState::Done { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            _ => true,
        }
    }


    /// All combiners must have distinct request ids they are working on
    /// Inv_CombinerRidsDistinct(s)
    #[invariant]
    pub fn inv_combiner_rids_distinct(&self) -> bool
    {
      forall |node_id1, node_id2|
          (#[trigger] self.combiner.contains_key(node_id1)
          && #[trigger] self.combiner.contains_key(node_id2)
          && node_id1 != node_id2) ==>
            seq_disjoint(self.combiner[node_id1].queued_ops(), self.combiner[node_id2].queued_ops())
    }


    /// the state of the replica must match the current version of the log
    #[invariant]
    pub open spec fn replica_state(&self) -> bool {
        forall |node_id| (#[trigger] self.replicas.contains_key(node_id)) ==>
            self.replicas[node_id] == compute_nrstate_at_version(self.log, self.current_local_version(node_id))
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // State Machine Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////

    init!{
        initialize(number_of_nodes: nat) {
            require(number_of_nodes > 0);

            init num_replicas = number_of_nodes;
            init log = Map::empty();
            init tail = 0;
            init replicas = Map::new(|n: NodeId| n < number_of_nodes, |n| DT::init_spec());
            init local_versions = Map::new(|n: NodeId| n < number_of_nodes, |n| 0);
            init version_upper_bound = 0;
            init local_reads = Map::empty();
            init local_updates = Map::empty();
            init combiner = Map::new(|n: NodeId| n < number_of_nodes, |n| CombinerState::Ready);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Readonly Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////

    /*/// Read Request: Enter the read request operation into the system
    transition!{
        readonly_start(op: DT::ReadOperation) {
            //birds_eye let rid_fn = |rid| !pre.local_reads.contains_key(rid);
            birds_eye let rid = get_fresh_nat(pre.local_reads.dom(), pre.combiner);
            add local_reads += [ rid => ReadonlyState::Init {op} ] by {
                get_fresh_nat_not_in(pre.local_reads.dom(), pre.combiner);
            };
        }
    }*/

    /// Read Request: Read the version of the log
    ///
    /// The algorithm waits while local_version < read_version
    transition!{
        readonly_version_upper_bound(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::Init { op } ];
            add    local_reads += [ rid => ReadonlyState::VersionUpperBound {
                                                op, version_upper_bound: pre.version_upper_bound } ];
        }
    }

    /// Read Request: wait until the version of the state has reached the version of the log
    ///
    /// The algorithm waits while local_version < read_version
    transition!{
        readonly_ready_to_read(rid: ReqId, node_id: NodeId) {
            remove local_reads    -= [ rid => let ReadonlyState::VersionUpperBound { op, version_upper_bound } ];
            have   local_versions >= [ node_id => let local_head ];

            require(local_head >= version_upper_bound);

            add local_reads += [ rid => ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} ];
        }
    }

    /// Read Request: perform the read request on the local replica, the combiner must not be busy
    transition!{
        readonly_apply(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::ReadyToRead { op, node_id, version_upper_bound } ];
            have   combiner    >= [ node_id => CombinerState::Ready ];
            have   replicas    >= [ node_id => let state ];

            let ret = DT::dispatch_spec(state, op);

            add local_reads += [ rid => ReadonlyState::Done{ op, node_id, version_upper_bound, ret } ];
        }
    }

    /*/// Read Request: remove the read request from the request from the state machine
    transition!{
        readonly_finish(rid: ReqId, rop: DT::ReadOperation, result: DT::Response) {
            remove local_reads -= [ rid => let ReadonlyState::Done { op, ret, version_upper_bound, node_id } ];

            require(op == rop);
            require(ret == result);
        }
    }*/

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Update Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////

    /*/// Update: A new update request enters the system
    transition!{
        update_start(op: DT::WriteOperation) {

            birds_eye let combiner = pre.combiner;
            birds_eye let rid_fn = |rid| !pre.local_updates.contains_key(rid)
                            && combiner_request_id_fresh(combiner, rid);
            birds_eye let rid = get_fresh_nat(pre.local_updates.dom(), combiner);
            add local_updates += [ rid => UpdateState::Init { op } ] by {
                get_fresh_nat_not_in(pre.local_updates.dom(), combiner);
            };

            assert(combiner_request_id_fresh(combiner, rid)) by {
                get_fresh_nat_not_in(pre.local_updates.dom(), combiner);
            };
        }
    }*/

    /*pub open spec fn request_id_fresh(&self, rid: ReqId) -> bool {
        &&& !self.local_reads.contains_key(rid)
        &&& !self.local_updates.contains_key(rid)
        &&& combiner_request_id_fresh(self.combiner, rid)
    }*/

    /*
    /// Combiner: Collect the operations and place them into the log
    transition!{
        update_place_ops_in_log(node_id: NodeId, request_ids: Seq<ReqId>,
            //old_updates: Map<nat, UpdateState>,
        ) {

            let old_updates = Map::<ReqId, UpdateState>::new(
                |rid| request_ids.contains(rid),
                |rid| pre.local_updates[rid]
            );

            remove local_updates -= (old_updates);

             require(forall(|rid|
                 old_updates.contains_key(rid) >>=
                     old_updates[rid].is_Init() && request_ids.contains(rid)));
             require(forall(|i|
                 0 <= i && i < request_ids.len() >>=
                     old_updates.contains_key(request_ids.index(i))));

             remove updates -= (old_updates);
             remove combiner -= [node_id => Combiner::Ready];

             let new_log = Map::<nat, LogEntry>::new(
                 |n| pre.tail <= n && n < pre.tail + request_ids.len(),
                 |n| LogEntry{
                     op: old_updates.index(request_ids.index(n)).get_Init_op(),
                     node_id: node_id,
                 },
             );
             let new_updates = Map::<nat, UpdateState>::new(
                 |rid| old_updates.contains_key(rid),
                 |rid| UpdateState::Placed{
                     op: old_updates[rid].get_Init_op(),
                     idx: idx_of(request_ids, rid),
                 }
             );

             add log += (new_log);
             add local_updates += (new_updates);
             add combiner += [node_id => Combiner::Placed{queued_ops: request_ids}];
             update tail = pre.tail + request_ids.len();
        }
    }
    */

    /// Combiner: Collect the operations and place them into the log
    transition!{
        update_place_ops_in_log_one(node_id: NodeId, rid: ReqId) {
            // Only allowing a single request at a time
            // (in contrast to the seagull one which does it in bulk).
            // Hopefully this leads to some easier proofs.
            remove combiner      -= [ node_id => let CombinerState::Placed{ queued_ops } ];
            remove local_updates -= [ rid => let UpdateState::Init{ op }];

            update tail = pre.tail + 1;
            add log           += [ pre.tail => LogEntry{ op, node_id }];
            add local_updates += [ rid => UpdateState::Placed{ op, idx: pre.tail }];
            add combiner      += [ node_id => CombinerState::Placed { queued_ops: queued_ops.push(rid) } ];
        }
    }

    transition!{
        update_done(rid:ReqId) {
            remove local_updates -= [ rid => let UpdateState::Applied { ret, idx } ];

            // we must have applied the
            require(pre.version_upper_bound > idx);

            add local_updates += [ rid => UpdateState::Done { ret, idx } ];
        }
    }

    /*/// Update: Remove a finished update from the system
    transition!{
        update_finish(rid:ReqId) {
            remove local_updates -= [ rid => let UpdateState::Done { ret, idx } ];
        }
    }*/


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Execute Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// Combiner: start the combiner to execute the update operations on the local replica
    transition!{
        exec_trivial_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Ready ];

            add    combiner += [ node_id => CombinerState::Placed { queued_ops: Seq::empty() } ];
        }
    }

    /// Combiner: read the version of the local replica
    transition!{
        exec_load_local_version(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Placed { queued_ops } ];

            have   local_versions >= [node_id => let lversion];

            add    combiner      += [ node_id => CombinerState::LoadedLocalVersion { queued_ops, lversion }];
        }
    }

    /// Combiner: read the global tail
    transition!{
        exec_load_global_head(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            add    combiner += [ node_id => CombinerState::Loop { queued_ops, lversion, idx: 0, tail: pre.tail } ];
        }
    }

    /// Combiner: Safety condition, the queue index must be within bounds
    property!{
        pre_exec_dispatch_local(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];
            have log      >= [ lversion => let log_entry ];

            require(log_entry.node_id == node_id);
            require(lversion < tail);
            assert(idx < queued_ops.len()) by {
                // assert(pre.wf_combiner_for_node_id(node_id));
                // assert(lversion < tail);
                // assert(pre.log.index(lversion).node_id == node_id);
            };
            assert(queued_ops.len() > 0);
        }
    }

    /// Combiner: dispatch a local update and apply it to the local replica and record the outcome of the update
    transition!{
        exec_dispatch_local(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx } ];
            remove replicas      -= [ node_id => let old_nr_state ];
            let rid = queued_ops.index(idx as int);
            remove local_updates -= [ rid => let local_update ];

            have log >= [lversion => let log_entry];

            // require(local_update.is_Placed());

            // apply all updates between lhead and global tail that were enqueued from local node
            require(lversion < tail);
            require(log_entry.node_id == node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add local_updates += [ rid => UpdateState::Applied { ret, idx: lversion }];
            add replicas      += [ node_id => new_nr_state];
            add combiner      += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx: idx + 1}];
        }
    }

    /// Combiner: dispatch a remote update and apply it to the local replica
    transition!{
        exec_dispatch_remote(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState:: Loop { queued_ops, lversion, tail, idx } ];
            remove replicas -= [ node_id => let old_nr_state ];

            have   log      >= [ lversion => let log_entry ];

            // apply all updates between lhead and global tail that were enqueued from remote nodes
            require(lversion < tail);
            require(log_entry.node_id != node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add replicas    += [ node_id => new_nr_state ];
            add combiner    += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx}];
        }
    }

    /// Combiner: Safety condition, if we applied all updates, idx must be the length of the list
    property!{
        pre_exec_update_version_upper_bound(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];

            require(lversion == tail);
            assert(idx == queued_ops.len()) by {
                // assert(pre.wf_combiner_for_node_id(node_id));
                // assert(lversion == tail);
            };
        }
    }

    /// Combiner: update the version upper bound when all updates have been applied to the local replica
    transition!{
        exec_update_version_upper_bound(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx, }];

            // we applied all updates up to the global tail we've read
            require(lversion == tail);

            // assert(idx == queued_ops.len()) by {
            //     //assert(pre.wf_combiner_for_node_id(node_id));
            // };

            update version_upper_bound = if pre.version_upper_bound >= tail {
                pre.version_upper_bound
            } else {
                tail
            };
            add combiner += [ node_id => CombinerState::UpdatedVersion { queued_ops, tail } ];
        }
    }

    /// Combiner: is done, bump the local version and combiner returns to ready state
    transition!{
        exec_finish(node_id: NodeId) {
            remove combiner       -= [ node_id => let CombinerState::UpdatedVersion { queued_ops, tail } ];
            remove local_versions -= [ node_id => let old_local_head ];

            // here have the local updates updated to done.

            add    local_versions += [ node_id => tail ];
            add    combiner       += [ node_id => CombinerState::Ready ];
        }
    }

    /// Combiner: is done, without any change
    transition!{
        exec_finish_no_change(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            require(lversion == pre.tail);
            assert(queued_ops.len() == 0);

            add    combiner += [ node_id => CombinerState::Ready];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Inductiveness Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[inductive(initialize)]
    fn initialize_inductive(post: Self, number_of_nodes: nat) {

        // XXX: is it really that hard to show finetness of map domain?
        let max_dom = (post.num_replicas - 1) as nat;
        let cmap = map_new_rec(max_dom, CombinerState::Ready);
        assert(cmap.dom().finite()) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> post.combiner.contains_key(n));
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n)) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n));
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> cmap.contains_key(n));

        assert(forall |n: nat| post.combiner.contains_key(n) <==> #[trigger]cmap.contains_key(n));
        assert(post.combiner.dom() =~= cmap.dom());
        assert(forall |n| #[trigger]post.combiner.contains_key(n) ==> post.combiner[n] == CombinerState::Ready);

        assert(forall |n| #[trigger]cmap.contains_key(n) ==> cmap[n] == CombinerState::Ready) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(post.combiner =~= cmap);
        // assert_maps_equal!(post.combiner, cmap);
    }

    /*#[inductive(readonly_start)]
    fn readonly_start_inductive(pre: Self, post: Self, op: DT::ReadOperation) { }*/

    #[inductive(readonly_version_upper_bound)]
    fn readonly_version_upper_bound_inductive(pre: Self, post: Self, rid: ReqId) { }

    #[inductive(readonly_ready_to_read)]
    fn readonly_ready_to_read_inductive(pre: Self, post: Self, rid: ReqId, node_id: NodeId) {
        match post.local_reads[rid] {
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                assert(post.combiner.contains_key(node_id));
                assert(post.local_versions.contains_key(node_id));
                assert(post.replicas.contains_key(node_id));
                assert(version_upper_bound <= post.version_upper_bound);
                assert(version_upper_bound <= post.current_local_version(node_id));
            }
            _ => { }
        };
        assert(post.wf_readstate(post.local_reads[rid]));
    }

    #[inductive(readonly_apply)]
    fn readonly_apply_inductive(pre: Self, post: Self, rid: ReqId) {
        let ret = post.local_reads[rid].get_Done_ret();
        let nid = post.local_reads[rid].get_Done_node_id();
        let vup = post.local_reads[rid].get_Done_version_upper_bound();
        let v = post.local_versions[nid];
        assert(rangeincl(vup, v, post.version_upper_bound));
    }

    //#[inductive(readonly_finish)]
    //fn readonly_finish_inductive(pre: Self, post: Self, rid: ReqId, rop: DT::ReadOperation, result: DT::Response) { }

    pub proof fn add_ticket_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: crate::InputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::add_ticket(pre, post, input, rid),
            rid == get_fresh_nat(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner)
        ensures post.invariant(),
    {
        get_fresh_nat_not_in(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner);
        match input {
            crate::InputOperation::Read(op) => {
                assert(post.inv_request_ids_finite());
                assert(post.inv_local_combiner_complete());
                assert(post.invariant());
            }
            crate::InputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    assert(post.combiner[node_id] == pre.combiner[node_id]);
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {
                        }
                    }
                }
            }
        }
    }

    /*#[inductive(update_start)]
    fn update_start_inductive(pre: Self, post: Self, op: DT::WriteOperation) {
        // get the rid that has been added
        let rid = choose|rid: nat| ! #[trigger] pre.local_updates.contains_key(rid)
                && post.local_updates == pre.local_updates.insert(rid, UpdateState::Init { op })
                && combiner_request_id_fresh(pre.combiner, rid);

        assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
            assert(post.combiner[node_id] == pre.combiner[node_id]);
            match post.combiner[node_id] {
                CombinerState::Placed { queued_ops } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                }
                _ => {

                }
            }
    }*/

    #[inductive(update_done)]
    fn update_done_inductive(pre: Self, post: Self, rid: ReqId) {
        assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
            match post.combiner[node_id] {
                CombinerState::Placed { queued_ops } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                }
                _ => {}
            }
        }
    }

    pub proof fn consume_stub_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: crate::OutputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::consume_stub(pre, post, output, rid),
        ensures post.invariant(),
    {
        match output {
            crate::OutputOperation::Read(op) => { }
            crate::OutputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::Loop { queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /*#[inductive(update_finish)]
    fn update_finish_inductive(pre: Self, post: Self, rid: ReqId) {
        assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
            match post.combiner[node_id] {
                CombinerState::Placed { queued_ops } => {
                    LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                    LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop { queued_ops, idx, lversion, tail } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                }
                _ => {}
            }
        }
    }*/

    #[inductive(exec_trivial_start)]
    fn exec_trivial_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        concat_LogRangeNoNodeId_LogRangeMatchesQueue(
            Seq::empty(), post.log, 0,
            pre.local_versions[node_id],
            pre.tail,
            post.tail,
            node_id,
            post.local_updates);

        assert(post.wf_combiner_for_node_id(node_id));
    }

    // #[inductive(update_place_ops_in_log)]
    // fn update_place_ops_in_log_inductive(pre: Self, post: Self, node_id: NodeId, request_ids: Seq<ReqId>) { }

    #[inductive(update_place_ops_in_log_one)]
    fn update_place_ops_in_log_one_inductive(pre: Self, post: Self, node_id: NodeId, rid: ReqId) {

        let old_queued_ops = pre.combiner[node_id].get_Placed_queued_ops();
        let op = pre.local_updates[rid].get_Init_op();

        assert(post.wf_combiner_for_node_id(node_id)) by {
            match post.combiner[node_id] {
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append(old_queued_ops, pre.log, post.log, 0,
                        post.local_versions[node_id], pre.tail,
                        node_id, pre.local_updates, post.local_updates, rid,
                        LogEntry{ op, node_id });
                }
                _ => { }
            }
        }

        assert(post.inv_local_updates_wf(post.local_updates[rid]));

        assert forall |node_id1| #[trigger] post.combiner.contains_key(node_id1)
            && node_id1 != node_id
            implies post.wf_combiner_for_node_id(node_id1)
        by {
            assert(pre.combiner[node_id1] === post.combiner[node_id1]);
            assert(pre.wf_combiner_for_node_id(node_id1));
            match pre.combiner[node_id1] {
                CombinerState::Ready => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        post.local_versions[node_id1], pre.tail, node_id1, LogEntry{ op, node_id });
                }
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, post.local_versions[node_id1], pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, lversion, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::Loop{queued_ops, lversion, idx, tail} => {
                    LogRangeMatchesQueue_append_other(queued_ops, pre.log, post.log,
                        idx, lversion, tail, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail,
                        node_id1, LogEntry{ op, node_id });
                }
                CombinerState::UpdatedVersion{queued_ops, tail} => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail, node_id1, LogEntry{ op, node_id });
                }
            }
        }

        assert (forall |nid| (#[trigger] pre.replicas.contains_key(nid)) ==> pre.local_versions.contains_key(nid));

        assert forall |nid| (#[trigger] post.replicas.contains_key(nid)) implies
            post.replicas[nid] == compute_nrstate_at_version(post.log, post.current_local_version(nid)) by
        {
            compute_nrstate_at_version_preserves(pre.log, post.log, post.current_local_version(nid));
        }

        assert forall |rid| (#[trigger] post.local_updates.contains_key(rid))
            implies post.update_results_match(post.local_updates[rid]) by
        {
            match post.local_updates[rid] {
                UpdateState::Applied { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                UpdateState::Done { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                _ => {},
            }
        }

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid))
            implies post.read_results_match(post.local_reads[rid]) by
        {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(pre.log, ver), op));
                    compute_nrstate_at_version_preserves(pre.log, post.log, ver);
                },
                _ => {},
            }
        }
    }


    #[inductive(exec_load_local_version)]
    fn exec_load_local_version_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_load_global_head)]
    fn exec_load_global_head_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_dispatch_local)]
    fn exec_dispatch_local_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.wf_combiner_for_node_id(node_id)) by {
            LogRangeMatchesQueue_update_change(
                post.combiner[node_id].get_Loop_queued_ops(),
                post.log, post.combiner[node_id].get_Loop_idx(), post.combiner[node_id].get_Loop_lversion(),
                pre.combiner[node_id].get_Loop_tail(), node_id, pre.local_updates, post.local_updates);
        }

        let c = pre.combiner[node_id];
        let rid = c.get_Loop_queued_ops().index(c.get_Loop_idx() as int);
        assert forall |node_id0| #[trigger] post.combiner.contains_key(node_id0) && node_id0 != node_id
            implies post.wf_combiner_for_node_id(node_id0)
        by {
            match pre.combiner[node_id0] {
            CombinerState::Ready => {
            }
            CombinerState::Placed{queued_ops} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, post.local_versions[node_id0], post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, lversion, post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::Loop{queued_ops, idx, lversion, tail} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, idx, lversion, tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::UpdatedVersion{queued_ops, tail} => {
            }
            }
        }
    }

    #[inductive(exec_dispatch_remote)]
    fn exec_dispatch_remote_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_update_version_upper_bound)]
    fn exec_update_version_upper_bound_inductive(pre: Self, post: Self, node_id: NodeId) {
        // assert(post.log == pre.log);
        assert(post.version_upper_bound >= pre.version_upper_bound);

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid)) implies post.read_results_match(post.local_reads[rid]) by {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(post.log, ver), op));
                    assert(rangeincl(version_upper_bound, ver, post.version_upper_bound));
                },
                _ => {}
            }
        }
    }

    #[inductive(exec_finish)]
    fn exec_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_finish_no_change)]
    fn exec_finish_no_change_inductive(pre: Self, post: Self, node_id: NodeId) { }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Helper Functions
    ////////////////////////////////////////////////////////////////////////////////////////////////

    /// obtains the current local version for the given node depending on the combiner state
    pub open spec fn current_local_version(&self, node_id: NodeId) -> nat
        recommends self.combiner.contains_key(node_id) && self.local_versions.contains_key(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready                              => self.local_versions[node_id],
            CombinerState::Placed{ .. }                       => self.local_versions[node_id],
            CombinerState::LoadedLocalVersion{ lversion, .. } => lversion,
            CombinerState::Loop { lversion, .. }              => lversion,
            CombinerState::UpdatedVersion { tail, .. }        => tail,
        }
    }

    // pub open spec fn combiners_fresh_req_id(&self, rid: ReqId) -> bool {
    //     forall |n| self.combiner.contains_key(n)
    //         ==> !self.combiner[n].queued_ops().contains(rid)
    // }
}

} // end tokenized_state_machine!

verus! {

// pub open spec fn combiner_request_ids(node_ids: Set<NodeId>, combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
//     recommends (forall |n| (#[trigger] node_ids.contains(n)) ==> #[trigger]combiners.contains_key(n))
//     decreases node_ids.len() when (node_ids.finite() && node_ids.len() >= 0)
// {
//     if node_ids.finite() {
//         if node_ids.len() == 0 {
//             Set::empty()
//         } else {
//             let node_id = node_ids.choose();
//             combiner_request_ids(node_ids.remove(node_id), combiners) + seq_to_set(combiners[node_id].queued_ops())
//         }
//     } else {
//         arbitrary()
//     }
// }

pub open spec fn combiner_request_ids(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    decreases combiners.dom().len()  when (combiners.dom().finite() && combiners.dom().len() >= 0) via combiner_request_ids_decreases
{
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
            Set::empty()
        } else {
            let node_id = combiners.dom().choose();
            let req_ids = combiner_request_ids(combiners.remove(node_id));
            req_ids + seq_to_set(combiners[node_id].queued_ops())
        }
    } else {
        arbitrary()
    }
}

#[via_fn]
proof fn combiner_request_ids_decreases(combiners: Map<NodeId, CombinerState>) {
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
        } else {
            let node_id = combiners.dom().choose();
            assert(combiners.remove(node_id).dom().len() < combiners.dom().len()); // INCOMPLETENESS weird incompleteness
        }
    } else {
    }
}

pub proof fn combiner_request_ids_proof(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    requires combiners.dom().finite()
    decreases combiners.dom().len()
{
    if combiners.dom().len() == 0 {
        Set::empty()
    } else {
        let node_id = combiners.dom().choose();
        let s1 = combiner_request_ids_proof(combiners.remove(node_id));
        s1 + seq_to_set(combiners[node_id].queued_ops())
        // combiner_request_ids_proof(combiners.remove(node_id)) + seq_to_set(combiners[node_id].queued_ops())
    }
}


pub open spec fn combiner_request_id_fresh(combiners: Map<NodeId, CombinerState>, rid: ReqId) -> bool
{
    forall |n| (#[trigger] combiners.contains_key(n)) ==> !combiners[n].queued_ops().contains(rid)
}

pub proof fn combiner_request_ids_not_contains(combiners: Map<NodeId, CombinerState>, rid: ReqId)
    requires combiners.dom().finite()
    ensures combiner_request_id_fresh(combiners,rid) <==> !combiner_request_ids(combiners).contains(rid)
    decreases combiners.dom().len()
{
    if !(combiners.dom() =~= Set::empty()) {
        let node_id = combiners.dom().choose();
        combiner_request_ids_not_contains(combiners.remove(node_id), rid);
        assert(combiner_request_id_fresh(combiners.remove(node_id),rid) <==> !combiner_request_ids(combiners.remove(node_id)).contains(rid));

        if !combiners[node_id].queued_ops().contains(rid) {
            if combiner_request_id_fresh(combiners.remove(node_id),rid) {
                assert forall |n| (#[trigger] combiners.contains_key(n)) implies !combiners[n].queued_ops().contains(rid) by {
                    if n != node_id {
                        assert(combiners.remove(node_id).contains_key(n));
                    }
                }
            }
        }
    }
}

pub proof fn combiner_request_ids_finite(combiners: Map<NodeId, CombinerState>)
    requires combiners.dom().finite()
    ensures combiner_request_ids(combiners).finite()
    decreases combiners.dom().len()
{
    if combiners.dom().len() == 0 {
        assert(combiner_request_ids(combiners).finite())
    } else {
        let node_id = combiners.dom().choose();
        assert(combiner_request_ids(combiners.remove(node_id)).finite()) by {
            combiner_request_ids_finite(combiners.remove(node_id));
        }

        assert(seq_to_set(combiners[node_id].queued_ops()).finite()) by {
            seq_to_set_is_finite(combiners[node_id].queued_ops());
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper Functions
////////////////////////////////////////////////////////////////////////////////////////////////////


pub closed spec fn get_fresh_nat(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>) -> nat
    recommends reqs.finite() && combiner.dom().finite()
{
    choose |n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n)
}


proof fn max_of_set(s:Set<nat>) -> (r:nat)
    requires s.finite(),
    ensures forall |x:nat| #[trigger] s.contains(x) ==> x <= r
    decreases s.len(),
{
  if s.is_empty() {
      0
  } else {
      let v1 = s.choose();
      let v2 = max_of_set(s.remove(v1));
      assert (forall |x:nat| #[trigger] s.contains(x) && x != v1 ==> s.remove(v1).contains(x));
      if v1 >= v2 { v1 } else { v2 }
  }
}

proof fn element_outside_set(s:Set<nat>) -> (r:nat)
requires s.finite(),
ensures !s.contains(r),
{
  max_of_set(s) + 1
}


pub proof fn get_fresh_nat_not_in(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>)
    requires
        reqs.finite(),
        combiner.dom().finite()
    ensures
        !reqs.contains(get_fresh_nat(reqs, combiner)),
        combiner_request_id_fresh(combiner, get_fresh_nat(reqs, combiner))

{
    let rid = get_fresh_nat(reqs, combiner);
    let combiner_req_ids = combiner_request_ids(combiner);
    assert(!combiner_req_ids.contains(rid) == combiner_request_id_fresh(combiner, rid)) by {
        combiner_request_ids_not_contains(combiner, rid);
    }
    assert(combiner_req_ids.finite()) by {
        combiner_request_ids_finite(combiner);
    }

    let req_ids = reqs + combiner_req_ids;
    assert(req_ids.finite());

    let r = element_outside_set(req_ids);

    // let r = choose |r| !req_ids.contains(r);
    assert(!reqs.contains(r));
    assert(!combiner_req_ids.contains(r) );
    assert(combiner_request_id_fresh(combiner, r)) by {
        combiner_request_ids_not_contains(combiner, r);
    }

    assert(exists |n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n));
}


/// the log contains all entries up to, but not including the provided end
pub open spec fn LogContainsEntriesUpToHere<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>, end: LogIdx) -> bool {
    forall |i: nat| 0 <= i < end ==> log.contains_key(i)
}

/// the log doesn't contain any entries at or above the provided start index
pub open spec fn LogNoEntriesFromHere<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>, start: LogIdx) -> bool {
    forall |i: nat| start <= i ==> !log.contains_key(i)
}

/// the log contains no entries with the given node id between the supplied indices
pub open spec fn LogRangeNoNodeId<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>, start: LogIdx, end: LogIdx, node_id: NodeId) -> bool
{
  decreases_when(start <= end);
  decreases(end - start);

  (start < end ==> {
    &&& log.contains_key(start)
    &&& log.index(start).node_id != node_id
    &&& LogRangeNoNodeId(log, start +  1, end, node_id)
  })
}

/// predicate that the a range in the log matches the queue of updates
pub open spec fn LogRangeMatchesQueue<DT: Dispatch>(queue: Seq<ReqId>, log: Map<LogIdx, LogEntry<DT>>, queueIndex: nat,
                                      logIndexLower: LogIdx, logIndexUpper: LogIdx, nodeId: NodeId,
                                      updates: Map<ReqId, UpdateState<DT>>) -> bool
{
  recommends([ 0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper) ]);
  decreases_when(logIndexLower <= logIndexUpper);
  decreases(logIndexUpper - logIndexLower);

  // if we hit the end of the log range, we should be at the end of the queue
  &&& (logIndexLower == logIndexUpper ==> queueIndex == queue.len())
  // otherwise, we check the log
  &&& (logIndexLower < logIndexUpper ==> {
    &&& log.contains_key(logIndexLower)
    // local case: the entry has been written by the local node
    &&& (log.index(logIndexLower).node_id == nodeId ==> {
      // there must be an entry in the queue that matches the log entry
      &&& queueIndex < queue.len()
      &&& updates.contains_key(queue.index(queueIndex as int))
      &&& updates.index(queue.index(queueIndex as int)).is_Placed()
      &&& updates.index(queue.index(queueIndex as int)).get_Placed_idx() == logIndexLower
      &&& LogRangeMatchesQueue(queue, log, queueIndex + 1, logIndexLower + 1, logIndexUpper, nodeId, updates)
    })
    // remote case: the entry has been written by the local node, there is nothing to match, recourse
    &&& (log.index(logIndexLower).node_id != nodeId ==>
      LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower + 1, logIndexUpper, nodeId, updates)
    )
  })
}


pub open spec fn LogRangeMatchesQueue2<DT: Dispatch>(queue: Seq<ReqId>, log: Map<LogIdx, LogEntry<DT>>, queueIndex: nat,
    logIndexLower: LogIdx, logIndexUpper: LogIdx, nodeId: NodeId,
    updates: Map<ReqId, UpdateState<DT>>) -> bool
{
    recommends([ 0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper) ]);
    decreases_when(logIndexLower <= logIndexUpper);
    decreases(logIndexUpper - logIndexLower);

    // if we hit the end of the log range, we should be at the end of the queue
    &&& (logIndexLower == logIndexUpper ==> queueIndex == queue.len())
    // otherwise, we check the log
    &&& (logIndexLower < logIndexUpper ==> {
        &&& log.contains_key(logIndexLower)
        // local case: the entry has been written by the local node
        &&& (log.index(logIndexLower).node_id == nodeId ==> {
            // there must be an entry in the queue that matches the log entry
            &&& queueIndex < queue.len()
            // &&& updates.contains_key(queue.index(queueIndex as int))
            // &&& updates.index(queue.index(queueIndex as int)).is_Placed()
            // &&& updates.index(queue.index(queueIndex as int)).get_Placed_idx() == logIndexLower
            &&& LogRangeMatchesQueue2(queue, log, queueIndex + 1, logIndexLower + 1, logIndexUpper, nodeId, updates)
        })
        // remote case: the entry has been written by the local node, there is nothing to match, recourse
        &&& (log.index(logIndexLower).node_id != nodeId ==>
            LogRangeMatchesQueue2(queue, log, queueIndex, logIndexLower + 1, logIndexUpper, nodeId, updates)
        )
    })
}

proof fn LogRangeMatchesQueue_update_change<DT: Dispatch>(queue: Seq<nat>, log: Map<nat, LogEntry<DT>>,
    queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
        forall |rid| #[trigger] updates1.contains_key(rid) ==>
        updates1[rid].is_Placed() && logIndexLower <= updates1[rid].get_Placed_idx() < logIndexUpper ==>
            updates2.contains_key(rid) && updates2[rid] === updates1[rid],
    ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2)
    decreases logIndexUpper - logIndexLower
{
  if logIndexLower == logIndexUpper {
  } else {
    if log.index(logIndexLower).node_id == nodeId {
      LogRangeMatchesQueue_update_change(queue, log, queueIndex + 1, logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    } else {
      LogRangeMatchesQueue_update_change(queue, log, queueIndex, logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    }
  }
}

proof fn LogRangeMatchesQueue_update_change_2<DT: Dispatch>(queue: Seq<nat>, log: Map<nat, LogEntry<DT>>,
    queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>, updates2: Map<ReqId, UpdateState<DT>>)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
        forall |rid| #[trigger] updates1.contains_key(rid) ==> queue.contains(rid) ==>
            updates2.contains_key(rid) && updates2[rid] === updates1[rid],
    ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2),
    decreases logIndexUpper - logIndexLower,
{
  if logIndexLower == logIndexUpper {
  } else {
    if log.index(logIndexLower).node_id == nodeId {
      LogRangeMatchesQueue_update_change_2(queue, log, queueIndex + 1, logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    } else {
      LogRangeMatchesQueue_update_change_2(queue, log, queueIndex, logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    }
  }
}

proof fn LogRangeMatchesQueue_append<DT: Dispatch>(
      queue: Seq<nat>,
      log: Map<nat, LogEntry<DT>>, new_log: Map<nat, LogEntry<DT>>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
      updates: Map<ReqId, UpdateState<DT>>, new_updates: Map<ReqId, UpdateState<DT>>,
      new_rid: ReqId, log_entry: LogEntry<DT>)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id == node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{ op: log_entry.op, idx: logIndexUpper,}),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.contains_key(rid) && rid != new_rid ==>
            new_updates.contains_key(rid)
            && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logIndexUpper, log_entry),

    ensures LogRangeMatchesQueue(
        queue.push(new_rid),
        new_log,
        queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.contains_key(logIndexLower) );
     if new_log.index(logIndexLower).node_id == node_id {
        assert(LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex+1, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
      }
      if new_log.index(logIndexLower).node_id != node_id {
        assert(LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
      }
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        LogRangeMatchesQueue_append(queue, log, new_log, queueIndex + 1, logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
        assert(LogRangeMatchesQueue( queue.push(new_rid), new_log, queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
    } else {
        LogRangeMatchesQueue_append(queue, log, new_log, queueIndex, logIndexLower + 1, logIndexUpper,
                                    node_id, updates, new_updates, new_rid, log_entry);
    }
  }
}

proof fn LogRangeMatchesQueue_append_other<DT: Dispatch>(
      queue: Seq<nat>,
      log: Map<nat, LogEntry<DT>>, new_log: Map<nat, LogEntry<DT>>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, logLen: nat, node_id: NodeId,
      updates: Map<ReqId, UpdateState<DT>>, new_updates: Map<ReqId, UpdateState<DT>>,
      new_rid: ReqId, log_entry: LogEntry<DT>)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper <= logLen,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{ op: log_entry.op, idx: logLen }),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.contains_key(rid) && rid != new_rid ==>
            new_updates.contains_key(rid)
            && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logLen, log_entry),

    ensures LogRangeMatchesQueue(
        queue,
        new_log,
        queueIndex, logIndexLower, logIndexUpper, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper {
     //assert( new_log.contains_key(logIndexLower) );
     //assert(new_log.index(logIndexLower).node_id != node_id);
     //assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        LogRangeMatchesQueue_append_other(queue, log, new_log, queueIndex + 1,
            logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
    } else {
      LogRangeMatchesQueue_append_other(queue, log, new_log, queueIndex,
        logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
    }
  }
}

proof fn LogRangeMatchesQueue_append_other_augment<DT: Dispatch>(
      queue: Seq<nat>,
      log: Map<nat, LogEntry<DT>>, new_log: Map<nat, LogEntry<DT>>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
      updates: Map<ReqId, UpdateState<DT>>, new_updates: Map<ReqId, UpdateState<DT>>,
      new_rid: ReqId, log_entry: LogEntry<DT>)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{ op: log_entry.op, idx: logIndexUpper }),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.contains_key(rid) && rid != new_rid ==>
            new_updates.contains_key(rid)
            && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logIndexUpper, log_entry),

    ensures LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.contains_key(logIndexLower) );
     assert(new_log.index(logIndexLower).node_id != node_id);
     assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        LogRangeMatchesQueue_append_other_augment(queue, log, new_log, queueIndex + 1,
            logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);

        assert(LogRangeMatchesQueue(queue,new_log,queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
    } else {
      LogRangeMatchesQueue_append_other_augment(queue, log, new_log, queueIndex,
        logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
    }
  }
}


proof fn LogRangeNoNodeId_append_other<DT: Dispatch>(
      log: Map<nat, LogEntry<DT>>, new_log: Map<nat, LogEntry<DT>>,
      logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
      log_entry: LogEntry<DT>)
    requires
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),
    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.contains_key(logIndexLower) );
     assert(new_log.index(logIndexLower).node_id != node_id);
     assert(LogRangeNoNodeId(new_log, logIndexLower+1, logIndexUpper+1, node_id));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        LogRangeNoNodeId_append_other(log, new_log, logIndexLower + 1, logIndexUpper, node_id, log_entry);
        assert(LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id));
    } else {
      LogRangeNoNodeId_append_other(log, new_log, logIndexLower + 1, logIndexUpper, node_id, log_entry);
    }
  }
}



/// the updates below the current pointer are either in the applied or done state.
pub open spec fn QueueRidsUpdateDone<DT: Dispatch>(queued_ops: Seq<ReqId>, localUpdates: Map<ReqId, UpdateState<DT>>, bound: nat) -> bool
    recommends 0 <= bound <= queued_ops.len(),
{
    // Note that use localUpdates.contains_key(queued_ops[j]) as a *hypothesis*
    // here. This is because the model actually allows an update to "leave early"
    // before the combiner phase completes. (This is actually an instance of our
    // model being overly permissive.)
    forall |j| 0 <= j < bound ==>
        localUpdates.contains_key(#[trigger] queued_ops[j]) ==> {
            ||| localUpdates.index(queued_ops[j]).is_Applied()
            ||| localUpdates.index(queued_ops[j]).is_Done()
        }
}

/// the updates in the queue above or equal the current pointer are in placed state
pub open spec fn QueueRidsUpdatePlaced<DT: Dispatch>(queued_ops: Seq<ReqId>, localUpdates: Map<ReqId, UpdateState<DT>>, bound: nat) -> bool
    recommends 0 <= bound <= queued_ops.len(),
{
    forall |j| bound <= j < queued_ops.len() ==> {
        &&& localUpdates.contains_key(#[trigger] queued_ops[j])
        &&& localUpdates.index(queued_ops[j]).is_Placed()
    }
}




proof fn concat_LogRangeNoNodeId_LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>, log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat, a: nat, b: nat, c: nat, nodeId: nat, updates: Map<ReqId, UpdateState<DT>>)
    requires
        a <= b <= c,
        0 <= queueIndex <= queue.len(),
        LogRangeNoNodeId(log, a, b, nodeId),
        LogRangeMatchesQueue(queue, log, queueIndex, b, c, nodeId, updates),
    ensures LogRangeMatchesQueue(queue, log, queueIndex, a, c, nodeId, updates)
decreases b - a
{
  if a == b {
  } else {
    concat_LogRangeNoNodeId_LogRangeMatchesQueue(queue, log, queueIndex, a+1, b, c, nodeId, updates);
  }
}


/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given  version.
pub open spec fn compute_nrstate_at_version<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>, version: LogIdx) -> DT::View
    recommends forall |i| 0 <= i < version ==> log.contains_key(i)
    decreases version
{
    // decreases_when(version >= 0);
    if version == 0 {
        DT::init_spec()
    } else {
        let ver =  (version - 1) as nat;
        DT::dispatch_mut_spec(compute_nrstate_at_version(log, ver), log[ver].op).0
    }
}


pub proof fn compute_nrstate_at_version_preserves<DT: Dispatch>(a: Map<LogIdx, LogEntry<DT>>, b: Map<LogIdx, LogEntry<DT>>, version: LogIdx)
    requires
        forall |i| 0 <= i < version ==> a.contains_key(i),
        forall |i| 0 <= i < version ==> a[i] == b[i]
    ensures compute_nrstate_at_version(a, version) == compute_nrstate_at_version(b, version)
    decreases version
{
  if version > 0 {
    compute_nrstate_at_version_preserves(a, b, (version-1) as nat );
  }
}

} // end verus!

}

pub mod unbounded_log_refines_simplelog{
// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)] use vstd::pervasive::arbitrary;
use vstd::map::*;
use vstd::seq::Seq;
use vstd::seq_lib::*;

#[cfg(verus_keep_ghost)] use state_machines_macros::*;

use crate::{Dispatch, InputOperation, OutputOperation, ReqId};

#[cfg(verus_keep_ghost)] use super::simple_log::{
    compute_nrstate_at_version as s_nrstate_at_version, ReadReq as SReadReq, SimpleLog,
    UpdateResp as SUpdateResp,
};
use super::types::*;
#[cfg(verus_keep_ghost)] use super::unbounded_log::{
    compute_nrstate_at_version as i_nrstate_at_version,
    ReadonlyState, UnboundedLog, UpdateState,
};
use super::utils::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Refinement Proof: UnboundedLog refines SimpleLog
// ================================================
//
// ...
//
////////////////////////////////////////////////////////////////////////////////////////////////////

verus! {

#[verifier::external_body]
pub tracked  struct RefinementProof<#[verifier::reject_recursive_types] DT: Dispatch> {
    _p: std::marker::PhantomData<DT>,
}

impl<DT: Dispatch> crate::UnboundedLogRefinesSimpleLog<DT> for RefinementProof<DT> {
    closed spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT> { interp(s) }
    proof fn refinement_inv(vars: UnboundedLog::State<DT>) { refinement_inv(vars); }
    proof fn refinement_init(post: UnboundedLog::State<DT>) { refinement_init(post); }
    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>) {
        refinement_next(pre, post);
    }

    open spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId {
        crate::spec::unbounded_log::get_fresh_nat(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner)
    }

    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>)
    {
        crate::spec::unbounded_log::get_fresh_nat_not_in(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner);
    }

    proof fn refinement_add_ticket(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>, input: InputOperation<DT>) {
        let rid = Self::get_fresh_rid(pre);
        let aop = crate::AsyncLabel::Start(rid, input);
        crate::spec::unbounded_log::get_fresh_nat_not_in(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner);
        UnboundedLog::State::add_ticket_inductive(pre, post, input, rid);
        match input {
            InputOperation::Read(read_op) => {
                assert_maps_equal!(
                    pre.local_reads.insert(rid, ReadonlyState::Init {op: read_op}),
                    post.local_reads
                );
                assert_maps_equal!(
                    interp(pre).readonly_reqs.insert(rid, SReadReq::Init{op: read_op}),
                    interp(post).readonly_reqs
                );
                SimpleLog::show::readonly_start(interp(pre), interp(post), aop, rid, read_op);
            }
            InputOperation::Write(write_op) => {
                assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
                assert_maps_equal!(
                    interp(pre).update_reqs.insert(rid, write_op),
                    interp(post).update_reqs
                );
                SimpleLog::show::update_start(interp(pre), interp(post), aop, rid, write_op);
            }
        }
    }

    proof fn refinement_consume_stub(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>, output: OutputOperation<DT>, rid: ReqId) {
        let aop = crate::AsyncLabel::End(rid, output);
        UnboundedLog::State::consume_stub_inductive(pre, post, output, rid);
        match output {
            OutputOperation::Read(response) => {
                let op = pre.local_reads.index(rid).get_Done_op();
                let version_upper_bound = pre.local_reads.index(rid).get_Done_version_upper_bound();

                assert(exists |version: nat| #[trigger]rangeincl(version_upper_bound, version, pre.version_upper_bound) && result_match(pre.log, response, version, op)) ;

                let version : nat = choose |version| {
                    version_upper_bound <= version <= pre.version_upper_bound
                    && #[trigger] result_match(pre.log, response, version, op)
                };

                assert(response == DT::dispatch_spec(interp(pre).nrstate_at_version(version), op)) by {
                    state_at_version_refines(interp(pre).log, pre.log, pre.tail, version);
                }

                assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
                assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
                assert_maps_equal!(interp(pre).readonly_reqs.remove(rid), interp(post).readonly_reqs);

                SimpleLog::show::readonly_finish(interp(pre), interp(post), aop, rid, version, response);

            }
            OutputOperation::Write(response) => {
                assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
                assert_maps_equal!(interp(pre).update_resps.remove(rid), interp(post).update_resps);
                let version = pre.local_updates[rid].get_Done_idx();
                assert(response == DT::dispatch_mut_spec(interp(pre).nrstate_at_version(version), interp(pre).log[version as int]).1) by {
                    state_at_version_refines(interp(pre).log, pre.log, pre.tail, version);
                }

                SimpleLog::show::update_finish(interp(pre), interp(post), aop, rid, response);
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interpretation Function
////////////////////////////////////////////////////////////////////////////////////////////////////


spec fn interp_log<DT: Dispatch>(global_tail: nat, log: Map<nat, LogEntry<DT>>) -> Seq<DT::WriteOperation> {
    Seq::new(global_tail, |i| log.index(i as nat).op)
}

spec fn interp_readonly_reqs<DT: Dispatch>(local_reads: Map<nat, ReadonlyState<DT>>) -> Map<ReqId, SReadReq<DT::ReadOperation>> {
    Map::new(
        |rid| local_reads.contains_key(rid),
        |rid| match local_reads.index(rid) {
            ReadonlyState::Init { op } => SReadReq::Init { op },
            ReadonlyState::VersionUpperBound { version_upper_bound: idx, op } => SReadReq::Req { op, version: idx },
            ReadonlyState::ReadyToRead { version_upper_bound: idx, op, .. } => SReadReq::Req { op, version: idx },
            ReadonlyState::Done { version_upper_bound: idx, op, .. } => SReadReq::Req { op, version: idx },
        },
    )
}

spec fn interp_update_reqs<DT: Dispatch>(local_updates: Map<LogIdx, UpdateState<DT>>) -> Map<LogIdx, DT::WriteOperation> {
    Map::new(
        |rid| local_updates.contains_key(rid) && local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => op,
            _ => arbitrary(),
        }
    )
}

spec fn interp_update_resps<DT: Dispatch>(local_updates: Map<nat, UpdateState<DT>>) -> Map<ReqId, SUpdateResp> {
    Map::new(
        |rid| local_updates.contains_key(rid) && !local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => arbitrary(),
            UpdateState::Placed{op, idx} => SUpdateResp(idx),
            UpdateState::Applied{ret, idx} => SUpdateResp(idx),
            UpdateState::Done{ret, idx} => SUpdateResp(idx),
        },
    )
}

spec fn interp<DT: Dispatch>(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT> {
    SimpleLog::State {
        log: interp_log(s.tail, s.log),
        version: s.version_upper_bound,
        readonly_reqs: interp_readonly_reqs(s.local_reads),
        update_reqs: interp_update_reqs(s.local_updates),
        update_resps: interp_update_resps(s.local_updates),
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////

proof fn refinement_inv<DT: Dispatch>(vars: UnboundedLog::State<DT>)
    requires vars.invariant()
    ensures interp(vars).invariant()
{
}

proof fn refinement_init<DT: Dispatch>(post: UnboundedLog::State<DT>)
    requires
        post.invariant(),
        UnboundedLog::State::init(post)
    ensures
        SimpleLog::State::init(interp(post)),
{
    case_on_init!{ post, UnboundedLog::<DT> => {
        initialize(number_of_nodes) => {
            assert_maps_equal!(interp(post).readonly_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_resps, Map::empty());
            assert_seqs_equal!(interp(post).log, Seq::empty());
            SimpleLog::show::initialize(interp(post));
        }
    }}
}


proof fn refinement_next<DT: Dispatch>(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
    requires
        pre.invariant(),
        post.invariant(),
        UnboundedLog::State::next_strong(pre, post),
    ensures
        SimpleLog::State::next(interp(pre), interp(post), crate::AsyncLabel::Internal),
{
    let aop = crate::AsyncLabel::Internal;
    case_on_next_strong! {
      pre, post, UnboundedLog::<DT> => {
        /*readonly_start(op) => {

            let rid = get_fresh_nat(pre.local_reads.dom(), pre.combiner);
            assert_maps_equal!(
                pre.local_reads.insert(rid, ReadonlyState::Init {op}),
                post.local_reads
            );
            assert_maps_equal!(
                interp(pre).readonly_reqs.insert(rid, SReadReq::Init{op}),
                interp(post).readonly_reqs
            );

            SimpleLog::show::readonly_start(interp(pre), interp(post), rid, op);
        }*/

        readonly_version_upper_bound(rid) => {
            let op = pre.local_reads.index(rid).get_Init_op();

            assert_maps_equal!(
                interp(pre).readonly_reqs.insert(rid, SReadReq::Req { op, version: pre.version_upper_bound }),
                interp(post).readonly_reqs
            );

            SimpleLog::show::readonly_read_version(interp(pre), interp(post), aop, rid);
        }

        readonly_ready_to_read(rid, node_id) => {
            assert_maps_equal!(interp(pre).readonly_reqs, interp(post).readonly_reqs);
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        readonly_apply(rid) => {
            assert_maps_equal!(interp(pre).readonly_reqs, interp(post).readonly_reqs);
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        /*readonly_finish(rid, op, ret) => {
            // corresponds toConsumeStub_Refines_End
            // let version = 0;

            assert(op == pre.local_reads.index(rid).get_Done_op());
            assert(op == interp(pre).readonly_reqs.index(rid).get_Req_op());

            assert(pre.local_reads.index(rid).is_Done());
            assert(ret == pre.local_reads.index(rid).get_Done_ret());

            let version_upper_bound = pre.local_reads.index(rid).get_Done_version_upper_bound();

            // assert(node_id == pre.local_reads.index(rid).get_Done_node_id());

            assert(version_upper_bound <= pre.version_upper_bound);
            assert(rangeincl(version_upper_bound, version_upper_bound, pre.version_upper_bound));
            assert(exists |v| rangeincl(version_upper_bound, v, pre.version_upper_bound));

            assert(pre.version_upper_bound  <= interp(pre).log.len());


            assert(forall |version| 0 <= version <= pre.version_upper_bound ==> #[trigger] version_in_log(pre.log, version));
            assert(forall |version| version_upper_bound <= version <= pre.version_upper_bound ==> #[trigger] version_in_log(pre.log, version));
            assert(forall |v| version_upper_bound <= v <= pre.version_upper_bound <==> #[trigger] dummy(version_upper_bound, v, pre.version_upper_bound));

            assert(forall |version|#[trigger]rangeincl(version_upper_bound, version, pre.version_upper_bound) ==> version_in_log(pre.log, version));

            // assert(exists |version : nat | version_upper_bound <= version <= pre.version_upper_bound
            // ==> VersionInLog(pre.log, version) && result_match(s.log, output, version,  s.localReads[rid].op)) by

            assert(exists |version: nat| #[trigger]rangeincl(version_upper_bound, version, pre.version_upper_bound) && result_match(pre.log, ret, version, op)) ;

            let version : nat = choose |version| {
                version_upper_bound <= version <= pre.version_upper_bound
                && #[trigger] result_match(pre.log, ret, version, op)
            };

            assert(version_in_log(pre.log, version));
            assert(version <= pre.version_upper_bound);
            assert(version <= interp(pre).version);
            assert(0 <= version <=  interp(pre).log.len());
            assert(interp(pre).readonly_reqs.index(rid).get_Req_version() <= version <= interp(pre).log.len());

            assert(ret == DT::dispatch_spec(interp(pre).nrstate_at_version(version), op)) by {
                state_at_version_refines(interp(pre).log, pre.log, pre.tail, version);
            }

            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).readonly_reqs.remove(rid), interp(post).readonly_reqs);

            SimpleLog::show::readonly_finish(interp(pre), interp(post), rid, version, ret);
        }*/

        /*update_start(op) => {
            let rid = get_fresh_nat(pre.local_updates.dom(), pre.combiner);

            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(
                interp(pre).update_reqs.insert(rid, op),
                interp(post).update_reqs
            );

            SimpleLog::show::update_start(interp(pre), interp(post), rid, op);
        }*/

        update_place_ops_in_log_one(node_id, rid) => {
            let op = pre.local_updates.index(rid).get_Init_op();

            assert_seqs_equal!(interp(pre).log.push(op), interp(post).log);
            assert_maps_equal!(interp(pre).update_reqs.remove(rid), interp(post).update_reqs);
            assert_maps_equal!(
                interp(pre).update_resps.insert(rid, SUpdateResp(pre.tail)),
                interp(post).update_resps
            );

            SimpleLog::show::update_add_op_to_log(interp(pre), interp(post), aop, rid);
        }

        update_done(rid) => {
            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);

            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        /*update_finish(rid) => {
            let ret = pre.local_updates.index(rid).get_Done_ret();
            let idx = pre.local_updates.index(rid).get_Done_idx();

            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).update_resps.remove(rid), interp(post).update_resps);

            SimpleLog::show::update_finish(interp(pre), interp(post), rid);
        }*/

        exec_trivial_start(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_load_local_version(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_load_local_version(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_load_global_head(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_dispatch_local(node_id) => {
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_dispatch_remote(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_update_version_upper_bound(node_id) => {
            let global_tail = pre.combiner.index(node_id).get_Loop_tail();
            let version = if pre.version_upper_bound >= global_tail{
                pre.version_upper_bound
            } else {
                global_tail
            };
            SimpleLog::show::update_incr_version(interp(pre), interp(post), aop, version);
        }

        exec_finish(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }

        exec_finish_no_change(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post), aop);
        }
      }
    }
}

pub open spec fn dummy(lower:nat, mid: nat, upper: nat) -> bool
    recommends lower <= upper
{
    lower <= mid <= upper
}

pub open spec fn dummy2(lower:nat, mid: nat, upper: nat) -> bool
    recommends lower < upper
{
    lower <= mid < upper
}


pub open spec fn version_in_log<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>, version: LogIdx) -> bool
{
    forall |i| 0 <= i < version ==> log.contains_key(i)
}

pub open spec fn result_match<DT: Dispatch>(log: Map<LogIdx, LogEntry<DT>>,  output: DT::Response, version: LogIdx, op: DT::ReadOperation) -> bool
    recommends version_in_log(log, version)
{

    output == DT::dispatch_spec(i_nrstate_at_version(log, version), op)
}


proof fn state_at_version_refines<DT: Dispatch>(s_log: Seq<DT::WriteOperation>, i_log: Map<LogIdx, LogEntry<DT>>, gtail: nat, idx:nat)
    requires
      forall |i| 0 <= i < gtail ==> i_log.contains_key(i),
      0 <= idx <= s_log.len(),
      idx <= gtail,
      s_log == interp_log(gtail, i_log),
    ensures
      s_nrstate_at_version::<DT>(s_log, idx) == i_nrstate_at_version::<DT>(i_log, idx)
    decreases idx
{
    if idx > 0 {
        state_at_version_refines(s_log, i_log, gtail, (idx - 1) as nat);
    }
}

} // end verus!

}


// cyclic buffer
#[macro_use]
pub mod cyclicbuffer{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

use vstd::cell::{CellId, PointsTo};

use state_machines_macros::*;

use crate::Dispatch;

use super::types::*;
use super::unbounded_log::UnboundedLog;
use super::utils::*;

#[cfg(verus_keep_ghost)] use vstd::prelude::OptionAdditionalFns;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Cyclic Buffer
// =============
//
// Dafny: https://github.com/secure-foundations/iron-sync/blob/concurrency-experiments/concurrency/node-replication/CyclicBuffer.i.dfy
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
//
////////////////////////////////////////////////////////////////////////////////////////////////////

// rust_verify/tests/example.rs ignore

pub type LogicalLogIdx = int;

type Key = int;

verus! {
    use crate::constants::LOG_SIZE;

    // pub type StoredType = PointsTo<LogEntry>;

///  - Dafny: glinear datatype StoredType = StoredType(CellContents<ConcreteLogEntry>, glOption<Log>)
pub tracked struct StoredType<DT: Dispatch> {
    pub cell_perms: PointsTo<Option<ConcreteLogEntry<DT>>>,
    pub log_entry: Option<UnboundedLog::log<DT>>
}

pub open spec fn stored_type_inv<DT: Dispatch>(st: StoredType<DT>, idx: int, cell_id: CellId, unbounded_log_instance: UnboundedLog::Instance<DT>) -> bool {
    // also match the cell id
    &&& st.cell_perms@.value.is_Some()
    &&& st.cell_perms@.pcell == cell_id
    &&& idx >= 0 ==> {
        &&& st.log_entry.is_Some()
        &&& st.log_entry.get_Some_0()@.key == idx
        &&& st.log_entry.get_Some_0()@.instance == unbounded_log_instance
        &&& st.cell_perms@.value.get_Some_0().is_Some()
        &&& st.cell_perms@.value.get_Some_0().get_Some_0().node_id as NodeId == st.log_entry.get_Some_0()@.value.node_id
        &&& st.cell_perms@.value.get_Some_0().get_Some_0().op == st.log_entry.get_Some_0()@.value.op
    }
    &&& idx < 0 ==> {
        &&& true
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Read Only Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

///
#[is_variant]
pub tracked enum ReaderState<DT: Dispatch> {
    ///
    Starting {
        ///
        start: LogIdx,
    },
    /// reader in the range
    Range {
        start: LogIdx,
        end: LogIdx,
        cur: LogIdx,
    },
    /// Guard
    Guard {
        start: LogIdx,
        end: LogIdx,
        cur: LogIdx,
        val: StoredType<DT>,
    },
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Combiner
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents the combiner
#[is_variant]
pub tracked enum CombinerState<DT: Dispatch> {
    Idle,
    Reading(ReaderState<DT>),
    AdvancingHead { idx: LogIdx, min_local_version: LogIdx },
    AdvancingTail { observed_head: LogIdx },
    Appending { cur_idx: LogIdx, tail: LogIdx },
}


impl<DT: Dispatch> CombinerState<DT> {
    pub open spec fn no_overlap_with(self, other: Self) -> bool {
        match self {
            CombinerState::Appending{cur_idx, tail} => {
                match other {
                    CombinerState::Reading(ReaderState::Guard{start, end, cur, val}) => {
                        (cur_idx > cur)     // self is after the other
                          || (tail <= cur)  // self is before the other
                    }
                    CombinerState::Appending{cur_idx: cur_idx2, tail: tail2} => {
                        (cur_idx >= tail2)       // self is after the other
                          || (tail <= cur_idx2)  // self is before the other
                    }
                    _ => { true }
                }
            }
            _ => { true }
        }
    }
}

tokenized_state_machine! { CyclicBuffer<DT: Dispatch> {
    fields {
        #[sharding(constant)]
        pub unbounded_log_instance: UnboundedLog::Instance::<DT>,

        #[sharding(constant)]
        pub cell_ids: Seq<CellId>,

        /// the size of the buffer
        #[sharding(constant)]
        pub buffer_size: LogIdx,

        /// the number of replicas
        #[sharding(constant)]
        pub num_replicas: nat,

        // Logical index into the above slice at which the log starts.
        // Note: the head does _not_ necessarily advance monotonically.
        // (It could go backwards in the event of two threads overlapping
        // in their AdvancingHead cycles.)
        // It's only guaranteed to be <= all the local heads.

        #[sharding(variable)]
        pub head: LogIdx,

        // Logical index into the above slice at which the log ends.
        // New appends go here.

        #[sharding(variable)]
        pub tail: LogIdx,

        // Array consisting of the local head of each replica registered with the log.
        // Required for garbage collection; since replicas make progress over the log
        // independently, we want to make sure that we don't garbage collect operations
        // that haven't been executed by all replicas.

        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>,    // previously called local_tails

        /// the contents of the buffer/log.
        #[sharding(storage_map)]
        pub contents: Map<LogicalLogIdx, StoredType<DT>>,

        // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
        // and sometimes 'false' means 'alive'.
        // entry is an index into the buffer (0 <= entry < LOG_SIZE)

        #[sharding(map)]
        pub alive_bits: Map</* entry: */ LogIdx, /* bit: */ bool>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState<DT>>
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[invariant]
    pub spec fn log_size(&self) -> bool {
        self.buffer_size == LOG_SIZE
    }

    #[invariant]
    pub spec fn cell_ids(&self) -> bool {
        self.cell_ids.len() == self.buffer_size
    }

    #[invariant]
    pub spec fn complete(&self) -> bool {
        &&& (forall |i| 0 <= i < self.num_replicas <==> self.local_versions.contains_key(i))
        &&& (forall |i| 0 <= i < self.buffer_size  <==> self.alive_bits.contains_key(i))
        &&& (forall |i| 0 <= i < self.num_replicas <==> self.combiner.contains_key(i))
        &&& (forall |i| self.contents.contains_key(i) ==> -self.buffer_size <= i < self.tail)
    }

    #[invariant]
    pub spec fn pointer_ordering(&self) -> bool {
        &&& self.head <= self.tail
        &&& (forall |i| #[trigger] self.local_versions.contains_key(i) ==>
            self.head <= self.local_versions[i] <= self.tail)
        &&& (forall |i| #[trigger] self.local_versions.contains_key(i) ==>
            self.tail <= self.local_versions[i] +  self.buffer_size)
    }

    #[invariant]
    pub spec fn pointer_differences(&self) -> bool {
        forall |i| self.local_versions.contains_key(i) ==>
            self.local_versions[i] <= self.tail <= self.local_versions[i] + self.buffer_size
    }

    #[invariant]
    pub spec fn ranges_no_overlap(&self) -> bool {
        (forall |i, j| self.combiner.contains_key(i) && self.combiner.contains_key(j) && i != j ==>
            self.combiner[i].no_overlap_with(self.combiner[j])
        )
    }

    #[invariant]
    pub spec fn upcoming_bits_are_not_alive(&self) -> bool {
        let min_local_head = map_min_value(self.local_versions, (self.num_replicas - 1) as nat);
        forall |i|
            self.tail <= i < min_local_head + self.buffer_size
            ==> !log_entry_is_alive(self.alive_bits, i, self.buffer_size)
    }

    #[invariant]
    pub spec fn inv_buffer_contents(&self) -> bool {
        &&& (forall |i: int| self.tail - self.buffer_size <= i < self.tail ==> (
            (log_entry_is_alive(self.alive_bits, i, self.buffer_size) ||
                i < map_min_value(self.local_versions, (self.num_replicas - 1) as nat))
            <==>
            #[trigger] self.contents.contains_key(i)
        ))
        &&& (forall |i: int| self.tail <= i ==> ! #[trigger] self.contents.contains_key(i))
    }

    #[invariant]
    pub spec fn contents_meet_inv(&self) -> bool {
        forall |i: int| #[trigger] self.contents.contains_key(i) ==>
            stored_type_inv(self.contents[i], i, self.cell_ids[log_entry_idx(i, self.buffer_size) as int], self.unbounded_log_instance)
    }

    #[invariant]
    pub spec fn all_reader_state_valid(&self) -> bool {
        forall |node_id| #![trigger self.combiner[node_id]] #[trigger] self.combiner.contains_key(node_id) && self.combiner[node_id].is_Reading() ==>
          self.reader_state_valid(node_id, self.combiner[node_id].get_Reading_0())
    }

    pub closed spec fn reader_state_valid(&self, node_id: NodeId, rs: ReaderState<DT>) -> bool {
        match rs {
            ReaderState::Starting{start} => {
                // the starting value should match the local tail
                &&& start == self.local_versions[node_id]
                &&& start <= self.tail
            }
            ReaderState::Range{start, end, cur} => {
                // the start must be our local tail
                &&& self.local_versions[node_id] == start
                // the start must be before the end, can be equial if ltail == tail
                &&& start <= end
                // we've read the tail, but the tail may have moved
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                // current is between start and end
                &&& start <= cur <= end
                // the entries up to, and including  current must be alive
                &&& (forall |i| start <= i < cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                // the entries up to, and including current must have something in the log
                &&& (forall |i| start <= i < cur ==> self.contents.contains_key(i))
            }
            ReaderState::Guard{start, end, cur, val} => {
                // the start must be our local tail
                &&& self.local_versions[node_id] == start
                // the start must be before the end, can be equial if ltail == tail
                &&& start <= end
                // we've read the tail, but the tail may have moved
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                // current is between start and end
                &&& start <= cur < end
                // the entries up to, and including  current must be alive
                &&& (forall |i| start <= i <= cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                // the entries up to, and including current must have something in the log
                &&& (forall |i| start <= i <= cur ==> self.contents.contains_key(i))
                // the thing we are ready should match the log content
                &&& self.contents.contains_key(cur as int)
                &&& self.contents[cur as int] === val
            }
        }
    }

    #[invariant]
    pub spec fn all_combiner_valid(&self) -> bool {
        forall |node_id| #[trigger] self.combiner.contains_key(node_id) ==>
          self.combiner_valid(node_id, self.combiner[node_id])
    }

    pub closed spec fn combiner_valid(&self, node_id: NodeId, cs: CombinerState<DT>) -> bool {
        match cs {
            CombinerState::Idle => true,
            CombinerState::Reading(_) => true, // see reader_state_valid instead
            CombinerState::AdvancingHead{idx, min_local_version} => {
                // the index is always within the defined replicas
                &&& idx <= self.num_replicas as nat
                // forall replicas we'e seen, min_local_version is smaller than all localTails
                &&& (forall |n| 0 <= n < idx ==> min_local_version <= self.local_versions[n])
            }
            CombinerState::AdvancingTail{observed_head} => {
                // the observed head is smaller than all local tails
                &&& (forall |n| 0 <= n < self.num_replicas as nat ==> observed_head <= self.local_versions[n])
            }
            CombinerState::Appending{cur_idx, tail} => {
                // the current index is between local tails and tail.
                &&& self.local_versions[node_id] <= cur_idx <= tail
                // the read tail is smaller or equal to the current tail.
                &&& tail <= self.tail
                //
                &&& (self.tail as int) - (self.buffer_size as int) <= cur_idx <= (self.tail as int)
                // all the entries we're writing must not be alive.
                &&& (forall |i : nat| cur_idx <= i < tail ==> (
                  !(log_entry_is_alive(self.alive_bits, i as int, self.buffer_size))))
            }
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////

    init!{
        initialize(buffer_size: nat, num_replicas: nat, contents: Map<int, StoredType<DT>>, cell_ids: Seq<CellId>, unbounded_log_instance: UnboundedLog::Instance<DT>, ) {
            require(num_replicas > 0);
            require(buffer_size == LOG_SIZE);
            require(cell_ids.len() == buffer_size);

            init unbounded_log_instance = unbounded_log_instance;
            init cell_ids = cell_ids;
            init buffer_size = buffer_size;
            init num_replicas = num_replicas;
            init head = 0;
            init tail = 0;
            init local_versions = Map::new(|i: NodeId| 0 <= i < num_replicas, |i: NodeId| 0);

            require(forall |i: int| (-buffer_size <= i < 0 <==> contents.contains_key(i)));
            require(forall |i: int| #[trigger] contents.contains_key(i) ==> stored_type_inv(contents[i], i, cell_ids[log_entry_idx(i, buffer_size) as int], unbounded_log_instance));
            init contents = contents;

            init alive_bits = Map::new(|i: nat| 0 <= i < buffer_size, |i: nat| !log_entry_alive_value(i as int, buffer_size));
            init combiner = Map::new(|i: NodeId| 0 <= i < num_replicas, |i: NodeId| CombinerState::Idle);
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Reader Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The reader transitions traverse the log and read the entries in it.
    //

    /// start the reader on the provided node, the combiner must be in idle state.
    transition!{
        reader_start(node_id: NodeId) {
            have   local_versions    >= [ node_id => let local_head ];

            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [
                node_id => CombinerState::Reading(ReaderState::Starting { start: local_head })
            ];
        }
    }

    /// enter the reading phase
    transition!{
        reader_enter(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Starting { start })
            ];
            add combiner += [
                node_id => CombinerState::Reading(ReaderState::Range { start, end: pre.tail, cur: start })
            ];
            assert start <= pre.tail;
        }
    }

    /// read the value of the current entry to process it
    transition!{
        reader_guard(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading( ReaderState::Range{ start, end, cur })
            ];

            require(cur < end);

            have alive_bits >= [ log_entry_idx(cur as int, pre.buffer_size) => log_entry_alive_value(cur as int, pre.buffer_size) ];

            birds_eye let val = pre.contents.index(cur as int);

            add combiner += [
                node_id => CombinerState::Reading( ReaderState::Guard{ start, end, cur, val })
            ];

            // assert(stored_type_inv(val, cur as int));
        }
    }

    /// the value of the log must not change while we're processing it
    property!{
        guard_guards(node_id: NodeId) {
            have combiner >= [
                node_id => let CombinerState::Reading( ReaderState::Guard{ start, end, cur, val })
            ];
            guard contents >= [ cur as int => val ];

            assert(stored_type_inv(val, cur as int, pre.cell_ids[log_entry_idx(cur as int, pre.buffer_size) as int],  pre.unbounded_log_instance));
        }
    }

    /// finish processing the entry, increase current pointer
    transition!{
        reader_unguard(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Guard{ start, end, cur, val })
            ];
            add combiner += [
                node_id => CombinerState::Reading(ReaderState::Range{ start, end, cur: cur + 1 })
            ];
        }
    }

    /// finish the reading whith, place the combiner into the idle state
    transition!{
        reader_finish(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Range{ start, end, cur })
            ];
            add    combiner += [ node_id => CombinerState::Idle ];

            remove local_versions -= [ node_id => let _ ];
            add    local_versions += [ node_id => end ];

            require(cur == end);
        }
    }

    /// abort reading, place the combiner back into the idle state
    transition!{
        reader_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Reading(r) ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(r.is_Starting() || r.is_Range());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Head Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The advance head transitions update the global head of the log with the minimum value
    // of all local heads.

    /// start the advancing of the head by reading the local head of node 0
    transition!{
        advance_head_start(node_id: NodeId) {
            have   local_versions >= [ 0 => let local_head_0 ];
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingHead { idx: 1, min_local_version: local_head_0,} ];
        }
    }

    /// read the next local head
    transition!{
        advance_head_next(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];

            have   local_versions    >= [ idx => let local_head_at_idx ];
            require(idx < pre.num_replicas);

            let new_min = min(min_local_version, local_head_at_idx);
            add combiner += [ node_id => CombinerState::AdvancingHead { idx: idx + 1, min_local_version: new_min } ];
        }
    }

    /// update the head value with the current collected miniumu
    transition!{
        advance_head_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];
            add    combiner += [ node_id => CombinerState::Idle ];
            update head      = min_local_version;

            require(idx == pre.num_replicas);
        }
    }

    /// stop the advancing head transition without uppdating the head
    transition!{
        advance_head_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Tail Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The advance tail transition bump the tail of the log to make space for new entries.
    // We first read the current head as this defines the maximum value the tail can be advanced to
    // as we need to ensure that we do not overrun existing entries.

    /// start the advancing of the head tail by reading the head value
    transition!{
        advance_tail_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingTail { observed_head: pre.head } ];
        }
    }

    /// advance the tail to the new value
    transition!{
        advance_tail_finish(node_id: NodeId, new_tail: nat) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { observed_head } ];
            add    combiner += [ node_id => CombinerState::Appending { cur_idx: pre.tail, tail: new_tail } ];
            update tail      = new_tail;

            // only allow advances and must not overwrite still active entries
            require(pre.tail <= new_tail <= observed_head + pre.buffer_size);

            // construct the entries in the log we withdraw
            birds_eye let withdrawn = Map::new(
                |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size,
                |i: int| pre.contents[i],
            );

            withdraw contents -= (withdrawn) by {
                assert forall |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size implies pre.contents.contains_key(i) by {
                    let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
                    map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
                }
            };

            assert forall
              |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size
                ==> stored_type_inv(#[trigger] withdrawn[i], i, pre.cell_ids[log_entry_idx(i, pre.buffer_size) as int], pre.unbounded_log_instance) by {

                assert forall
                  |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size
                    implies stored_type_inv(#[trigger] withdrawn[i], i, pre.cell_ids[log_entry_idx(i, pre.buffer_size) as int], pre.unbounded_log_instance) by {
                        assert(pre.contents.contains_key(i) && #[trigger] withdrawn.contains_key(i)) by {
                            let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
                            map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
                        };
                    };
                };
        }
    }

    /// aborts the advancing tail transitions
    transition!{
        advance_tail_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Tail Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////


    transition!{
        append_flip_bit(node_id: NodeId, deposited: StoredType<DT>) {
            remove combiner -= [ node_id => let CombinerState::Appending { cur_idx, tail } ];
            add    combiner += [ node_id => CombinerState::Appending { cur_idx: cur_idx + 1, tail } ];

            remove alive_bits -= [ log_entry_idx(cur_idx as int, pre.buffer_size) => let bit ];
            add    alive_bits += [ log_entry_idx(cur_idx as int, pre.buffer_size) => log_entry_alive_value(cur_idx  as int, pre.buffer_size) ];

            require(cur_idx < tail);
            require(stored_type_inv(deposited, cur_idx as int, pre.cell_ids[log_entry_idx(cur_idx as int, pre.buffer_size) as int],  pre.unbounded_log_instance));

            deposit contents += [ cur_idx as int => deposited ] by {
                map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
            };
        }
    }

    /// finish the appending parts
    transition!{
        append_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Appending { cur_idx, tail } ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(cur_idx == tail);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////////

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, buffer_size: nat, num_replicas: nat, contents: Map<int, StoredType<DT>>, cell_ids: Seq<CellId>,  unbounded_log_instance: UnboundedLog::Instance<DT>, ) {
        assert forall |i| post.tail <= i < post.buffer_size implies !log_entry_is_alive(post.alive_bits, i, post.buffer_size) by {
            int_mod_less_than_same(i, post.buffer_size as int);
        }
    }

    #[inductive(advance_head_start)]
    fn advance_head_start_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_next)]
    fn advance_head_next_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_abort)]
    fn advance_head_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_finish)]
    fn advance_head_finish_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.local_versions.contains_key(node_id));
    }

    #[inductive(advance_tail_start)]
    fn advance_tail_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert forall |n| 0 <= n < post.num_replicas as nat implies post.head <= post.local_versions[n] by {
            assert(post.local_versions.contains_key(n));
        }
     }

    #[inductive(advance_tail_abort)]
    fn advance_tail_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_tail_finish)]
    fn advance_tail_finish_inductive(pre: Self, post: Self, node_id: NodeId, new_tail: nat) {
        assert(post.local_versions.contains_key(node_id));

        let mycur_idx = post.combiner[node_id].get_Appending_cur_idx();
        let mytail = post.combiner[node_id].get_Appending_tail();
        assert(mycur_idx == pre.tail);

        let min_local_versions = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        map_min_value_smallest(post.local_versions,  (post.num_replicas - 1) as nat);
        assert(mycur_idx >= min_local_versions);
    }

    #[inductive(append_flip_bit)]
    fn append_flip_bit_inductive(pre: Self, post: Self, node_id: NodeId, deposited: StoredType<DT>) {
        assert(post.local_versions.contains_key(node_id));

        let myidx = pre.combiner[node_id].get_Appending_cur_idx();
        let mytail = pre.combiner[node_id].get_Appending_tail();

        let min_local_head = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        map_min_value_smallest(post.local_versions, (post.num_replicas - 1) as nat);

        log_entry_idx_wrap_around(min_local_head, post.buffer_size, myidx);

        assert(forall |i| min_local_head <= i < min_local_head + post.buffer_size && i != myidx ==>
            log_entry_is_alive(pre.alive_bits, i, pre.buffer_size) == log_entry_is_alive(post.alive_bits, i, post.buffer_size));

        // overlap check
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j
            implies post.combiner[i].no_overlap_with(post.combiner[j]) by {
            assert(pre.combiner[i].no_overlap_with(pre.combiner[j]));
        }

        // combiner state
        assert forall |nid| #[trigger] post.combiner.contains_key(nid) implies
            post.combiner_valid(nid, post.combiner[nid]) by
        {
            if nid != node_id {
                assert(pre.combiner[node_id].no_overlap_with(pre.combiner[nid]));
            }
        };
    }

    #[inductive(append_finish)]
    fn append_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_start)]
    fn reader_start_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_enter)]
    fn reader_enter_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_guard)]
    fn reader_guard_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.local_versions.contains_key(node_id));
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j
        implies post.combiner[i].no_overlap_with(post.combiner[j]) by {
            if (j == node_id && post.combiner[i].is_Appending()) {
                let cur = post.combiner[j].get_Reading_0().get_Guard_cur();
                assert(log_entry_is_alive(post.alive_bits, cur as int, post.buffer_size));
            }
        }
    }

    #[inductive(reader_unguard)]
    fn reader_unguard_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) {

        let min_local_versions_pre = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
        let min_local_versions_post = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);

        // there was a change in the minimum of the local heads, meaning the minimum was updated by us.
        if min_local_versions_pre != min_local_versions_post {

            let start = pre.combiner[node_id].get_Reading_0().get_Range_start();
            let end = pre.combiner[node_id].get_Reading_0().get_Range_end();

            map_min_value_smallest(pre.local_versions, (pre.num_replicas - 1) as nat);
            map_min_value_smallest(post.local_versions, (post.num_replicas - 1) as nat);

            assert(pre.local_versions[node_id] != post.local_versions[node_id]);

            log_entry_alive_wrap_around(post.alive_bits, post.buffer_size, min_local_versions_pre, min_local_versions_post );
            log_entry_alive_wrap_around_helper(post.alive_bits, post.buffer_size, min_local_versions_pre, min_local_versions_post );
        }
    }

    #[inductive(reader_abort)]
    fn reader_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }
}}

pub open spec fn min(x: nat, y: nat) -> nat {
    if x < y { x } else { y }
}

pub open spec fn map_min_value(m: Map<NodeId, nat>, idx: nat) -> nat
  decreases idx
{
    if idx === 0 {
        m.index(0)
    } else {
        min(
            map_min_value(m, (idx - 1) as nat),
            m.index(idx),
        )
    }
}

proof fn map_min_value_smallest(m: Map<NodeId, nat>, idx: nat)
    requires forall |i| 0 <= i <= idx ==> m.contains_key(i)
    ensures
       forall |n| 0 <= n <= idx as nat ==> map_min_value(m, idx) <= m.index(n),
       map_contains_value(m, map_min_value(m, idx))
    decreases idx
{
    if idx == 0 {
        assert(m.contains_key(0));
    } else {
        map_min_value_smallest(m, (idx - 1) as nat);
        if m.index(idx) < map_min_value(m, (idx - 1) as nat) {
            assert(m.contains_key(idx));
        }
    }
}



/// converts the logical to the physical log index
pub open spec fn log_entry_idx(logical: LogicalLogIdx, buffer_size: nat) -> LogIdx
    recommends buffer_size == LOG_SIZE
{
    (logical % (buffer_size as int)) as nat
}


pub proof fn log_entry_idx_wrap_around(start: nat, buffer_size: nat, idx: nat)
  requires
    buffer_size == LOG_SIZE,
    start <= idx < start + buffer_size
  ensures
    forall |i| start <= i < start + buffer_size && i != idx ==>
            log_entry_idx(i, buffer_size) != log_entry_idx(idx as int, buffer_size)
{ }



/// predicate to check whether a log entry is alive
pub open spec fn log_entry_is_alive(alive_bits: Map<LogIdx, bool>, logical: LogicalLogIdx, buffer_size: nat) -> bool
    recommends buffer_size == LOG_SIZE
{
    let phys_id = log_entry_idx(logical, buffer_size);
    alive_bits[phys_id as nat] == log_entry_alive_value(logical, buffer_size)
}

/// the value the alive but must have for the entry to be alive, this flips on wrap around
pub open spec fn log_entry_alive_value(logical: LogicalLogIdx, buffer_size: nat) -> bool
    recommends buffer_size == LOG_SIZE
{
    ((logical / buffer_size as int) % 2) == 0
}

spec fn add_buffersize(i: int, buffer_size: nat) -> int {
    i + buffer_size
}

proof fn log_entry_alive_wrap_around(alive_bits: Map<LogIdx, bool>,  buffer_size: nat,  low: nat, high: nat)
    requires
        buffer_size == LOG_SIZE,
        forall |i:nat| i < buffer_size <==> alive_bits.contains_key(i),
        low <= high <= low + buffer_size,
    ensures
        forall |i:int| low <= i < high ==>  log_entry_is_alive(alive_bits, i, buffer_size) == ! #[trigger] log_entry_is_alive(alive_bits,  add_buffersize(i, buffer_size), buffer_size)
{

}

proof fn log_entry_alive_wrap_around_helper(alive_bits: Map<LogIdx, bool>, buffer_size: nat,  low: nat, high: nat)
    requires
        buffer_size == LOG_SIZE,
        // forall |i:nat| i < buffer_size ==> alive_bits.contains_key(i),
        low <= high <= low + buffer_size,
        forall |i:int| low <= i < high ==> ! #[trigger] log_entry_is_alive(alive_bits, add_buffersize(i, buffer_size), buffer_size)
    ensures forall |i:int| low + buffer_size <= i < high  + buffer_size ==> ! #[trigger] log_entry_is_alive(alive_bits, i, buffer_size)
{
    assert forall |i:int| low + buffer_size <= i < high + buffer_size implies ! #[trigger] log_entry_is_alive(alive_bits, i, buffer_size) by {
        let j = i - buffer_size;
        assert(low <= j < high);
        assert(!log_entry_is_alive(alive_bits, add_buffersize(j, buffer_size), buffer_size));
    }
}

#[verifier(nonlinear)]
pub proof fn log_entry_alive_value_wrap_around(i: LogicalLogIdx, buffer_size: nat)
    requires buffer_size > 0
    ensures log_entry_alive_value(i, buffer_size) != log_entry_alive_value(i + (buffer_size as int), buffer_size)
{
    assert(((i + (buffer_size as int)) / buffer_size as int) == ((i / buffer_size as int) + 1));
}

} // verus!

}


// the flag combiner
pub mod flat_combiner{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

use state_machines_macros::*;

use super::types::*;
// use super::utils::*;

verus! {

/// represents the state of a client thread
#[is_variant]
pub tracked enum ClientState {
    Idle,
    Waiting(ReqId),
}

/// represents the state of a request in the queue
#[is_variant]
pub tracked enum SlotState {
    Empty,
    Request(ReqId),
    InProgress(ReqId),
    Response(ReqId),
}

impl SlotState {
    pub open spec fn get_ReqId(&self) -> ReqId {
        match self {
            SlotState::Empty => arbitrary(),
            SlotState::Request(reqid) => *reqid,
            SlotState::InProgress(reqid) => *reqid,
            SlotState::Response(reqid) => *reqid,
        }
    }
}

/// represents the combiner state
#[is_variant]
pub tracked enum CombinerState {
    Collecting(Seq<Option<ReqId>>),
    Responding(Seq<Option<ReqId>>, nat),
}

impl CombinerState {
    pub open spec fn req_len(self) -> nat {
        match self {
            CombinerState::Collecting(reqs) => reqs.len(),
            CombinerState::Responding(reqs, _) => reqs.len(),
        }
    }

    pub open spec fn req_is_none(self, tid: nat) -> bool
        recommends 0 <= tid < self.req_len()
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_None(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_None(),
        }
    }

    pub open spec fn req_is_some(self, tid: nat) -> bool
        recommends 0 <= tid < self.req_len()
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_Some(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_Some(),
        }
    }
}


// The flat combiner state machine
tokenized_state_machine! {
FlatCombiner {
    fields {
        /// the number of threads
        #[sharding(constant)]
        pub num_threads: nat,

        /// clients of the replica
        #[sharding(map)]
        pub clients: Map<ThreadId, ClientState>,

        #[sharding(map)]
        pub slots: Map<ThreadId, SlotState>,

        #[sharding(variable)]
        pub combiner: CombinerState,
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////

    #[invariant]
    pub fn inv_complete(&self) -> bool {
        // clients are complete
        &&& (forall |i| self.clients.contains_key(i) <==> i < self.num_threads)
        // slots are complete
        &&& (forall |i| self.slots.contains_key(i) <==> i < self.num_threads)
    }


    // && Complete(x)
    #[invariant]
    pub fn inv_client_slot_empty(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i)
            ==>  (self.clients[i].is_Idle() <==> self.slots[i].is_Empty())
    }

    #[invariant]
    pub fn inv_client_reqids(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i) && self.clients[i].is_Waiting()
            ==> self.clients[i].get_Waiting_0() == self.slots[i].get_ReqId()
    }

    #[invariant]
    pub fn inv_combiner_elements(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                elems.len() <= self.num_threads
            },
            CombinerState::Responding(elems, idx) => {
                &&& elems.len() == self.num_threads
                &&& idx <= elems.len()
            },
        }
    }

    pub open spec fn slot_in_progress(slots: Map<nat, SlotState>, tid: nat) -> bool
        recommends slots.contains_key(tid)
    {
        slots[tid].is_InProgress()
    }

    #[invariant]
    pub fn inv_combiner_slots_not_in_progress(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                // fff
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_None()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) //Self::slot_in_progress(self.slots, i)))
                // everything above is not in progress
                &&& (forall |i: nat| elems.len() <= i < self.num_threads ==> !self.slots[i].is_InProgress())
            },
            CombinerState::Responding(elems, idx) => {
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_None()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) //Self::slot_in_progress(self.slots, i)))
                &&& (forall |i: nat| 0 <= i < idx ==> !self.slots[i].is_InProgress())
            },
        }
    }

    #[invariant]
    pub fn inv_combiner_request_ids(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                forall |i:nat| (0 <= i < elems.len() && elems[i as int].is_Some())
                    ==> (#[trigger] self.slots[i]).is_InProgress() && (#[trigger] self.slots[i]).get_InProgress_0() == elems[i as int ].get_Some_0()
            },
            CombinerState::Responding(elems, idx) => {
                forall |i:nat| idx <= i < elems.len() && elems[i as int].is_Some()
                   ==> (#[trigger] self.slots[i]).is_InProgress() && (#[trigger] self.slots[i]).get_InProgress_0() == elems[i as int].get_Some_0()
            },
        }
    }




    ////////////////////////////////////////////////////////////////////////////////////////////
    // Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////


    init!{
        initialize(num_threads: nat) {
            init num_threads = num_threads;

            init clients = Map::new(|i:ThreadId| i < num_threads, |i| ClientState::Idle);
            init slots = Map::new(|i: ThreadId| i < num_threads, |i| SlotState::Empty);

            init combiner = CombinerState::Collecting(Seq::empty());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Collection of Requests
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// the combiner collects no request from the client
    transition!{
        combiner_collect_empty() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            have slots >= [ tid => let (SlotState::Empty { .. } | SlotState::Response { .. }) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::None));
        }
    }


    /// the combiner collects a request from the client
    transition!{
        combiner_collect_request() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            remove slots -= [ tid => let SlotState::Request(rid) ];
            add    slots += [ tid => SlotState::InProgress(rid) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::Some(rid)));
        }
    }


    /// Safety Condition: the slot state is not in progress when collecting
    property!{
        pre_combiner_collect_request() {
            require(pre.combiner.is_Collecting());
            let idx = pre.combiner.get_Collecting_0().len();
            require(idx < pre.num_threads);
            have slots >= [ idx => let slot_state ];

            assert(!slot_state.is_InProgress());
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Responding to Requests
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// combiner starts responding to requests
    transition!{
        combiner_responding_start() {
            require(pre.combiner.is_Collecting());
            require(pre.combiner.get_Collecting_0().len() == pre.num_threads);

            update combiner = CombinerState::Responding(pre.combiner.get_Collecting_0(), 0);
        }
    }

    /// combiner responds to an empty request
    transition!{
        combiner_responding_empty() {
            require(pre.combiner.is_Responding());
            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
        }
    }

    /// combiner responds to a request
    transition!{
        combiner_responding_result() {
            require(pre.combiner.is_Responding());

            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(!pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
            remove slots -= [ tid => let r ];
            assert let SlotState::InProgress(rid) = r;
            assert pre.combiner.get_Responding_0()[tid as int].get_Some_0() == rid;
            add    slots += [ tid => SlotState::Response(rid) ];
        }
    }

    /// combiner is done responding to requests
    transition!{
        combiner_responding_done() {
            require(pre.combiner.is_Responding());
            require(pre.combiner.get_Responding_1() == pre.num_threads);

            update combiner = CombinerState::Collecting(Seq::empty());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Sending
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// Safety Condition: the slot state is not in progress when collecting
    property!{
        pre_send_request(tid: ThreadId) {

            have clients >= [ tid => let ClientState::Idle ];
            have slots   >= [ tid => let slot_state ];

            assert(slot_state.is_Empty());
        }
    }

    transition!{
        send_request(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => let ClientState::Idle ];
            add    clients += [ tid => ClientState::Waiting(rid) ];

            remove slots -= [ tid => let SlotState::Empty ];
            add    slots += [ tid => SlotState::Request(rid) ];
        }
    }

    /// Safety Condition: the slot state is not in progress when collecting
    property!{
        pre_recv_response(tid: ThreadId) {

            have clients >= [ tid => let ClientState::Waiting(rid) ];
            have slots   >= [ tid => let slot_state ];

            assert(!slot_state.is_Empty());
            assert(slot_state.get_ReqId() == rid);
        }
    }

    transition!{
        recv_response(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => ClientState::Waiting(rid) ];
            add    clients += [ tid => ClientState::Idle ];

            remove slots -= [ tid => SlotState::Response(rid) ];
            add    slots += [ tid => SlotState::Empty ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[inductive(initialize)]
    fn initialize_inductive(post: Self, num_threads: nat) { }

    #[inductive(combiner_collect_empty)]
    fn combiner_collect_empty_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_collect_request)]
    fn combiner_collect_request_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Collecting(elems) => {
                let idx = pre.combiner.get_Collecting_0().len();
                assert(forall |i: nat| 0 <= i < idx
                    ==> Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_start)]
    fn combiner_responding_start_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_empty)]
    fn combiner_responding_empty_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Responding(elems, idx) => {
                assert(!Self::slot_in_progress(pre.slots, (idx - 1) as nat));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_result)]
    fn combiner_responding_result_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_done)]
    fn combiner_responding_done_inductive(pre: Self, post: Self) { }

    #[inductive(send_request)]
    fn send_request_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));

    }

    #[inductive(recv_response)]
    fn recv_response_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
    }

}} // tokenized_state_machine! { FlatCombiner { ...

} // verus!

}


// the RW lock
pub mod rwlock{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{
    prelude::*,
    multiset::*,};
use state_machines_macros::tokenized_state_machine;

verus!{

tokenized_state_machine!{
    RwLockSpec<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
        fields {
            #[sharding(constant)]
            pub user_inv: Set<T>,

            #[sharding(constant)]
            pub rc_width: int,

            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(variable)]
            pub exc_locked: bool,

            #[sharding(map)]
            pub ref_counts: Map<int, int>,

            #[sharding(option)]
            pub exc_pending: Option<int>,

            #[sharding(option)]
            pub exc_guard: Option<()>,

            #[sharding(multiset)]
            pub shared_pending: Multiset<int>,

            #[sharding(multiset)]
            pub shared_guard: Multiset<(int, T)>,
        }

        init!{
            initialize(rc_width: int, init_t: T, user_inv: Set<T>,) {
                require(0 < rc_width);
                require(user_inv.contains(init_t));
                init rc_width = rc_width;
                init user_inv = user_inv;
                init storage = Option::Some(init_t);
                init exc_locked = false;
                init ref_counts = Map::new(
                    |i| 0 <= i < rc_width,
                    |i| 0,
                );
                init exc_pending = Option::None;
                init exc_guard = Option::None;
                init shared_pending = Multiset::empty();
                init shared_guard = Multiset::empty();
            }
        }

        transition!{
            exc_start() {
                require(!pre.exc_locked);
                update exc_locked = true;
                add exc_pending += Some(0);
            }
        }

        transition!{
            exc_check_count() {
                remove exc_pending -= Some(let r);
                have ref_counts >= [r => 0];

                add exc_pending += Some(r + 1);
            }
        }

        transition!{
            exc_finish() {
                remove exc_pending -= Some(pre.rc_width);
                add exc_guard += Some(());

                birds_eye let x = pre.storage.get_Some_0();

                withdraw storage -= Some(x);
                assert(pre.user_inv.contains(x));
            }
        }

        transition!{
            exc_release(t: T) {
                require(pre.user_inv.contains(t));
                update exc_locked = false;
                remove exc_guard -= Some(());
                deposit storage += Some(t);
            }
        }

        transition!{
            shared_start(r: int) {
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc + 1];
                add shared_pending += {r};
            }
        }

        transition!{
            shared_abandon(r: int) {
                remove ref_counts -= [r => let rc];
                require(rc > 0);
                add ref_counts += [r => rc - 1];
                remove shared_pending -= {r};
            }
        }

        transition!{
            shared_finish(r: int) {
                require(!pre.exc_locked);
                remove shared_pending -= {r};

                birds_eye let t = pre.storage.get_Some_0();
                add shared_guard += {(r, t)};

                assert(pre.user_inv.contains(t));
            }
        }

        transition!{
            shared_release(val: (int, T)) {
                // require(pre.user_inv.contains(val.1));
                remove shared_guard -= {val};

                let r = val.0;
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc - 1];

                assert(rc > 0) by {
                    assert(0 <= r < pre.rc_width);
                    assert(pre.shared_guard.count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).len() > 0);
                    assert(pre.ref_counts.index(r) > 0);
                };
            }
        }

        property!{
            do_guard(val: (int, T)) {
                have shared_guard >= {val};
                guard storage >= Some(val.1);
            }
        }

        property!{
            rc_not_zero_guard(r: int) {
                have shared_pending >= {r};
                have ref_counts >= [r => let rc];
                assert(rc > 0);
            }
        }


        ///// Invariants and proofs

        #[invariant]
        pub fn sto_user_inv(&self) -> bool {
            self.storage.is_Some() ==>
                self.user_inv.contains(self.storage.get_Some_0())
        }

        #[invariant]
        pub fn ref_counts_domain(&self) -> bool {
            &&& 0 < self.rc_width
            &&& forall |i: int| 0 <= i < self.rc_width <==> self.ref_counts.dom().contains(i)
        }

        #[invariant]
        pub fn exc_inv(&self) -> bool {
            &&& self.exc_locked <==> (self.exc_pending.is_Some() || self.exc_guard.is_Some())
            &&& self.storage.is_Some() <==> self.exc_guard.is_None()
            &&& if let Option::Some(cur_r) = self.exc_pending {
                &&& 0 <= cur_r <= self.rc_width
                &&& self.exc_guard.is_None()
                &&& forall |x| self.shared_guard.count(x) > 0 ==> !(0 <= x.0 < cur_r)
            } else {
                true
            }
        }

        #[invariant]
        pub fn shared_pending_in_range(&self) -> bool {
            forall |r| self.shared_pending.count(r) > 0 ==> (0 <= r < self.rc_width)
        }

        #[invariant]
        pub fn shared_guard_in_range(&self) -> bool {
            forall |x| self.shared_guard.count(x) > 0 ==> (0 <= x.0 < self.rc_width)
        }

        #[invariant]
        pub fn shared_inv_agree(&self) -> bool {
            forall |v| #[trigger] self.shared_guard.count(v) > 0 ==>
                self.storage === Option::Some(v.1)
        }

        pub closed spec fn filter_r(shared_guard: Multiset<(int, T)>, r: int) -> Multiset<(int, T)> {
            shared_guard.filter(|val: (int, T)| val.0 == r)
        }

        #[invariant]
        pub fn shared_counts_agree(&self) -> bool {
            forall |r| 0 <= r < self.rc_width ==>
                #[trigger] self.ref_counts.index(r) ==
                    self.shared_pending.count(r) as int +
                        Self::filter_r(self.shared_guard, r).len() as int
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, rc_width: int, init_t: T,  user_inv: Set<T>) {
            assert forall |r| 0 <= r < post.rc_width implies
                #[trigger] post.ref_counts.index(r) ==
                    post.shared_pending.count(r) as int +
                        Self::filter_r(post.shared_guard, r).len() as int
            by {
                assert(post.ref_counts.index(r) == 0);
                assert(post.shared_pending.count(r) == 0);
                assert(Self::filter_r(post.shared_guard, r) =~= Multiset::empty());
                assert(Self::filter_r(post.shared_guard, r).len() == 0);
            }
            assert(post.shared_counts_agree());
        }

        #[inductive(exc_start)]
        fn exc_start_inductive(pre: Self, post: Self) {

        }

        #[inductive(exc_check_count)]
        fn exc_check_count_inductive(pre: Self, post: Self) {
            let prev_r = pre.exc_pending.get_Some_0();
            assert forall |x| #[trigger] post.shared_guard.count(x) > 0
                && x.0 == prev_r implies false
            by {
                assert(Self::filter_r(post.shared_guard, prev_r).count(x) > 0);
            }
        }

        #[inductive(exc_finish)]
        fn exc_finish_inductive(pre: Self, post: Self) {
        }

        #[inductive(exc_release)]
        fn exc_release_inductive(pre: Self, post: Self, t: T) {

        }

        #[inductive(shared_start)]
        fn shared_start_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_abandon)]
        fn shared_abandon_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_finish)]
        fn shared_finish_inductive(pre: Self, post: Self, r: int) {
            let t = pre.storage.get_Some_0();

            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r == r0 {
                    assert(pre.shared_pending =~= post.shared_pending.add(Multiset::singleton(r)));
                    assert(Self::filter_r(post.shared_guard, r) =~= Self::filter_r(pre.shared_guard, r).add(Multiset::singleton((r, t))));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                }
            }
        }

        #[inductive(shared_release)]
        fn shared_release_inductive(pre: Self, post: Self, val: (int, T)) {
            let r = val.0;
            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r0 == r {
                    assert(Self::filter_r(pre.shared_guard, r) =~= Self::filter_r(post.shared_guard, r).add(Multiset::singleton(val)));
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                }
            }
        }
    }
}


} // verus!
}


}

mod exec{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

use crate::Dispatch;

// spec imports
use crate::spec::{
    cyclicbuffer::CyclicBuffer,
    unbounded_log::UnboundedLog,
};

// exec imports
use crate::exec::log::{NrLog, NrLogTokens};
use crate::exec::replica::{Replica, ReplicaConfig, ReplicaId};
use crate::exec::context::ThreadToken;

use crate::AffinityFn;
use crate::constants::{MAX_REPLICAS, LOG_SIZE, MAX_THREADS_PER_REPLICA};

pub mod rwlock{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{
    prelude::*,
    cell::{PCell, PointsTo},
    atomic_ghost::{AtomicBool, AtomicU64},
    atomic_with_ghost
};

use crate::spec::rwlock::RwLockSpec;
use crate::exec::CachePadded;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockWriteGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// structure used to release the exclusive write access of a lock when dropped.
//
/// This structure is created by the write and try_write methods on RwLockSpec.
pub tracked struct RwLockWriteGuard<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
    handle:  Tracked<RwLockSpec::exc_guard<PointsTo<T>>>,
    cell_perms:  Tracked<PointsTo<T>>
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//  RwLockReadGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// RAII structure used to release the shared read access of a lock when dropped.
///
/// This structure is created by the read and try_read methods on RwLockSpec.
pub struct RwLockReadGuard<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)]T> {
    tid: usize,
    perms: Ghost<PointsTo<T>>,
    handle: Tracked<RwLockSpec::shared_guard<PointsTo<T>>>,
}

impl<T> RwLockReadGuard<T> {
    pub closed spec fn view(&self) -> T {
        self.handle@@.key.1.view().value.get_Some_0()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockDist Impl
////////////////////////////////////////////////////////////////////////////////////////////////////

pub const MAX_RC: u64 =  0xffff_ffff_ffff_fff0;

#[verus::trusted] #[verifier(external_body)] /* vattr */
pub fn warn_with_ref_count_too_big() {
    panic!("WARNING: Refcount value exceeds the maximum value of u64.");
}

struct_with_invariants!{
    pub struct RwLock<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
        /// cell containing the data
        data: PCell<T>,
        /// flag indicating whether the writer lock is held or being acquired
        exc_locked: CachePadded<AtomicBool<_, RwLockSpec::exc_locked<PointsTo<T>>, _>>,
        /// map of readers that want to acquire the reader lock
        ref_counts: Vec<CachePadded<AtomicU64<_, RwLockSpec::ref_counts<PointsTo<T>>, _>>>,
        /// the spec instance
        inst: Tracked<RwLockSpec::Instance<PointsTo<T>>>,
        user_inv: Ghost<Set<T>>,
    }

    pub closed spec fn wf(&self) -> bool {

        predicate {
            &&& self.inst@.rc_width() == self.ref_counts@.len()
            // &&& self.ref_counts@.len() > 0

            &&& forall |i: int| #![trigger self.ref_counts@.index(i)] (0 <= i && i < self.ref_counts@.len()) ==>
                self.ref_counts@.index(i).0.well_formed()
                && self.ref_counts@.index(i).0.constant() === (self.inst, i)

            &&& forall |v: PointsTo<T>| #[trigger] self.inst@.user_inv().contains(v) == (
                equal(v@.pcell, self.data.id()) && v@.value.is_Some()
                        && self.user_inv@.contains(v@.value.get_Some_0())
            )
        }

        invariant on exc_locked with (inst) specifically (self.exc_locked.0) is (b: bool, g: RwLockSpec::exc_locked<PointsTo<T>>) {
            &&& g@.instance == inst@
            &&& g@.value == b
        }

        invariant on ref_counts with (inst)
            forall |i: int| where (0 <= i < self.ref_counts@.len()) specifically (self.ref_counts@[i].0)
            is (v: u64, g: RwLockSpec::ref_counts<PointsTo<T>>)
        {
            &&& g@.instance == inst@
            &&& g@.key == i
            &&& g@.value == v as int
            &&& g@.value <= MAX_RC
        }
    }
}


impl<T> RwLock<T> {

    /// Invariant on the data
    pub closed spec fn inv(&self, t: T) -> bool {
        self.user_inv@.contains(t)
    }

    pub open spec fn thread_id_valid(&self, t: nat) -> bool {
        0 <= t && t < self.max_threads()
    }

    pub closed spec fn max_threads(&self) -> nat {
        self.ref_counts@.len()
    }

    pub closed spec fn wf_read_handle(&self, read_handle: &RwLockReadGuard<T>) -> bool {
        &&& self.thread_id_valid(read_handle.tid as nat)
        &&& read_handle.handle@@.instance == self.inst
        &&& read_handle.handle@@.count == 1
        &&& read_handle.handle@@.key == (read_handle.tid as int, read_handle.perms@)
        &&& read_handle.perms@@.pcell == self.data.id()
        &&& read_handle.perms@@.value.is_Some()
    }

    pub closed spec fn wf_write_handle(&self, write_handle: &RwLockWriteGuard<T>) -> bool {
        &&& write_handle.handle@@.instance == self.inst
        &&& write_handle.cell_perms@@.pcell == self.data.id()
        &&& write_handle.cell_perms@@.value.is_None()
    }

    #[verifier(spinoff_prover)]
    pub fn new(rc_width: usize, t: T, inv: Ghost<FnSpec(T) -> bool>) -> (s: Self)
        requires
            0 < rc_width && inv@(t)
        ensures
            s.wf() && s.max_threads() == rc_width,
            forall |v: T| s.inv(v) == inv@(v),
    {
        let tracked inst;
        let tracked exc_locked_token;
        let tracked mut ref_counts_tokens;

        // create the pcell object
        let (pcell_data, Tracked(mut pcell_token)) = PCell::new(t);

        // create the set of allowed data structures
        let ghost set_inv = Set::new(inv@);
        let ghost user_inv = Set::new(|s: PointsTo<T>| {
            &&& equal(s@.pcell, pcell_data.id())
            &&& s@.value.is_Some()
            &&& set_inv.contains(s@.value.get_Some_0())
        });

        proof {
            // user_inv: Set<T>, t: T
            // initialize_full(user_inv, perm@, Option::Some(perm.get()));
            //
            // initialize(rc_width: int, init_t: T, user_inv: Set<T>,) {
            let tracked (Tracked(inst0), Tracked(exc_locked_token0), Tracked(ref_counts_tokens0), _, _, _, _) =
                RwLockSpec::Instance::initialize(rc_width as int,  pcell_token, user_inv, Option::Some(pcell_token));
            inst = inst0;
            exc_locked_token = exc_locked_token0;
            ref_counts_tokens = ref_counts_tokens0;
        }

        let tracked_inst: Tracked<RwLockSpec::Instance<PointsTo<T>>> = Tracked(inst.clone());
        let exc_locked_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(exc_locked_token));

        let mut v: Vec<CachePadded<AtomicU64<(Tracked<RwLockSpec::Instance<PointsTo<T>>>, int), RwLockSpec::ref_counts<PointsTo<T>>, _>>>
            = Vec::new();
        let mut i: usize = 0;

        assert forall |j: int| i <= j && j < rc_width implies
            #[trigger] ref_counts_tokens.dom().contains(j)
                  && equal(ref_counts_tokens.index(j)@.instance, inst)
                  && equal(ref_counts_tokens.index(j)@.key, j)
                  && equal(ref_counts_tokens.index(j)@.value, 0)
        by {
            assert(ref_counts_tokens.dom().contains(j));
            assert(equal(ref_counts_tokens.index(j)@.instance, inst));
            assert(equal(ref_counts_tokens.index(j)@.key, j));
            assert(equal(ref_counts_tokens.index(j)@.value, 0));
        }

        assert(forall |j: int|
          #![trigger( ref_counts_tokens.dom().contains(j) )]
          #![trigger( ref_counts_tokens.index(j) )]
            i <= j && j < rc_width ==> (
            ref_counts_tokens.dom().contains(j)
            && equal(ref_counts_tokens.index(j)@.instance, inst)
            && equal(ref_counts_tokens.index(j)@.key, j)
            && equal(ref_counts_tokens.index(j)@.value, 0)
        ));

        while i < rc_width
            invariant
                i <= rc_width,
                v@.len() == i as int,
                forall|j: int| #![trigger v@.index(j)] 0 <= j && j < i ==>
                    v@.index(j).0.well_formed() && equal(v@.index(j).0.constant(), (tracked_inst, j)),
                tracked_inst@ == inst,
                forall |j: int|
                    #![trigger( ref_counts_tokens.dom().contains(j) )]
                    #![trigger( ref_counts_tokens.index(j) )]
                    i <= j && j < rc_width ==> (
                        ref_counts_tokens.dom().contains(j)
                        && equal(ref_counts_tokens.index(j)@.instance, inst)
                        && equal(ref_counts_tokens.index(j)@.key, j)
                        && equal(ref_counts_tokens.index(j)@.value, 0)
                    ),
        {
            assert(ref_counts_tokens.dom().contains(i as int));

            let tracked ref_count_token = ref_counts_tokens.tracked_remove(i as int);

            let rc_atomic = AtomicU64::new(Ghost((tracked_inst, i as int)), 0, Tracked(ref_count_token));
            v.push(CachePadded(rc_atomic));

            i = i + 1;

            assert forall |j: int| i <= j && j < rc_width implies
                #[trigger] ref_counts_tokens.dom().contains(j)
                      && equal(ref_counts_tokens.index(j)@.instance, inst)
                      && equal(ref_counts_tokens.index(j)@.key, j)
                      && equal(ref_counts_tokens.index(j)@.value, 0)
            by {
                assert(ref_counts_tokens.dom().contains(j));
                assert(equal(ref_counts_tokens.index(j)@.instance, inst));
                assert(equal(ref_counts_tokens.index(j)@.key, j));
                assert(equal(ref_counts_tokens.index(j)@.value, 0));
            }
        }

        let s = RwLock {
            user_inv: Ghost(set_inv),
            data: pcell_data,
            inst: Tracked(inst),
            exc_locked: CachePadded(exc_locked_atomic),
            ref_counts: v,
        };

        assert(s.inst@.rc_width() == s.ref_counts@.len());

        s
    }


    pub fn acquire_write(&self) -> (res: (T, Tracked<RwLockWriteGuard<T>>))
        requires
            self.wf()
        ensures
            self.wf() && self.wf_write_handle(&res.1@) && self.inv(res.0)
    {
        // -----------------------------------------------------------------------------------------
        // First: acquire the write lock
        // -----------------------------------------------------------------------------------------
        let tracked mut token : Option<RwLockSpec::exc_pending<PointsTo<T>>> = None;
        let mut acquired = false;
        while !acquired
            invariant
                self.wf(),
                acquired ==> token.is_Some() && token.get_Some_0()@.instance == self.inst && token.get_Some_0()@.value == 0
        {
            let result = atomic_with_ghost!(
                &self.exc_locked.0 => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res.is_Ok() {
                    token = Option::Some(self.inst.borrow().exc_start(&mut g));
                }
            });
            acquired = result.is_ok();
        }

        let tracked mut token = token.tracked_unwrap();

        // -----------------------------------------------------------------------------------------
        // Next: wait until all readers have released their lock
        // -----------------------------------------------------------------------------------------

        let mut idx = 0;
        while idx < self.ref_counts.len()
            invariant
                self.wf(),
                idx <= self.ref_counts.len(),
                token@.instance == self.inst,
                token@.value == idx
        {

            // wait until the reader hasn't taken the reader lock yet
            let mut taken = true;
            while taken
                invariant
                    self.wf(),
                    idx < self.ref_counts.len(),
                    token@.instance == self.inst,
                    taken ==> token@.value == idx,
                    !taken ==> token@.value == idx + 1
            {
                let result = atomic_with_ghost!(
                    &self.ref_counts[idx].0 => load();
                    returning res;
                    ghost g => {
                        if res == 0 {
                            token = self.inst.borrow().exc_check_count(&g, token);
                        }
                });
                taken = result != 0;
            }
            idx = idx + 1;
        }

        // (Ghost<Option<PointsTo<T>>>, Tracked<T>, Tracked<exc_guard<T>>>)
        let tracked (_, Tracked(cell_perms), handle) = self.inst.borrow().exc_finish(token);

        // obtain the data
        let t = self.data.take(Tracked(&mut cell_perms));

        // return the Writer Guard
        (t , Tracked(RwLockWriteGuard { handle, cell_perms: Tracked(cell_perms) }))
    }


    pub fn acquire_read<'a>(&'a self, tid: usize) -> (res: RwLockReadGuard<T>)
        requires
            self.wf() && self.thread_id_valid(tid as nat)
        ensures
            self.wf() && self.wf_read_handle(&res) && self.inv(res@)
    {
        loop
            invariant
                self.wf() &&  tid < self.ref_counts.len()
        {
            // TODO: figure out how to do the optimized read here!
            let rc = atomic_with_ghost!(
                &self.ref_counts[tid].0 => load();
                returning rc;
                ghost g => { }
            );

            if rc == MAX_RC {
                warn_with_ref_count_too_big();
                ////////////////////////////////////////////////////////////////////////////////////
                // !!! THIS IS A PANIC CASE! WE DO NOT RETURN FROM HERE !!!
                ////////////////////////////////////////////////////////////////////////////////////
                #[allow(while_true)]
                while true {} // TODO: is that fine?
            }

            // fetch add on the reader lock
            // let tracked mut ref_counts : Tracked<RwLockSpec::ref_counts<PointsTo<T>>>;
            let tracked mut shared_pending: Option<RwLockSpec::shared_pending<PointsTo<T>>>;
            let res = atomic_with_ghost!(
                &self.ref_counts[tid].0 => compare_exchange(rc, rc+1);
                update prev->next;
                ghost g =>
            {
                if prev == rc {
                    assert(rc < MAX_RC);
                    // Tracked<ref_counts<T>>,Tracked<shared_pending<T>>
                    let tracked (_ref_counts, _shared_pending) = self.inst.borrow().shared_start(tid as int, g);
                    // ref_counts = _ref_counts;
                    shared_pending = Some(_shared_pending.get());
                    g = _ref_counts.get();

                    // assert(g@.value <= MAX_RC);
                } else {
                    shared_pending = None;
                }

                // assume(g@.value < MAX_RC);
                // // Tracked<ref_counts<T>>,Tracked<shared_pending<T>>
                // let tracked (_ref_counts, _shared_pending) = self.inst.borrow().shared_start(tid as int, g);
                // // ref_counts = _ref_counts;
                // shared_pending = Some(_shared_pending.get());
                // g = _ref_counts.get();

                // assert(g@.instance == self.inst@);
                // assert(g@.key == tid as nat);
            });

            if res.is_err() {
                continue;
            }

            // exc_locked: CachePadded<AtomicBool<_, RwLockSpec::exc_locked<PointsTo<T>>, _>>,
            let ghost mut perms : PointsTo<T>;
            let tracked shared_guard : Option<RwLockSpec::shared_guard<PointsTo<T>>>;
            let is_exc_locked = atomic_with_ghost!(
                &self.exc_locked.0 => load();
                returning res;
                ghost g => {
                    if !res {
                        let tracked (_perms, _shared_guard) = self.inst.borrow().shared_finish(tid as int, &g, shared_pending.tracked_unwrap());
                        perms = _perms@.unwrap();
                        shared_guard = Some(_shared_guard.get());
                        shared_pending = None;
                    } else {
                        shared_guard = None;
                    }
            });

            let perms = Ghost(perms);

            if is_exc_locked {
                // writer lock still held, try again
                let res = atomic_with_ghost!(
                    &self.ref_counts[tid].0 => fetch_sub(1);
                    ghost g => {
                    let tracked shared_pending = shared_pending.tracked_unwrap();
                    self.inst.borrow().rc_not_zero_guard(tid as int, &g, &shared_pending);
                    g = self.inst.borrow().shared_abandon(tid as int, g, shared_pending);
                });
            } else {
                // create the read guard lock
                return RwLockReadGuard { tid, perms, handle: Tracked(shared_guard.tracked_unwrap()) };
            }
        }
    }

    pub fn borrow<'a>(&'a self, read_handle: Tracked<&'a RwLockReadGuard<T>>) -> (res: &'a T)
        requires
            self.wf() && self.wf_read_handle(&read_handle@)
        ensures
            res == read_handle@@
    {
        let ghost val = (read_handle@.tid as int, read_handle@.perms@);
        let tracked handle = read_handle.borrow().handle.borrow();
        let tracked perm = self.inst.borrow().do_guard(val, &handle);
        self.data.borrow(Tracked(&perm))
    }


    pub fn release_write(&self, val: T, write_handle: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf() && self.inv(val) && self.wf_write_handle(&write_handle@)
        ensures
            self.wf()
    {
        let tracked RwLockWriteGuard { cell_perms, handle } = write_handle.get();
        let tracked mut cell_perms = cell_perms.get();

        self.data.put(Tracked(&mut cell_perms), val);

        let res = atomic_with_ghost!(
            &self.exc_locked.0 => store(false);
            ghost g => {
            let tracked exc_guard = handle.get();
            self.inst.borrow().exc_release(cell_perms, cell_perms, &mut g, exc_guard);
        });
    }


    pub fn release_read(&self, read_handle: RwLockReadGuard<T>)
        requires
            self.wf() && self.wf_read_handle(&read_handle)
        ensures
            self.wf()
    {
        let RwLockReadGuard {tid, perms, handle } = read_handle;
        let res = atomic_with_ghost!(
            &self.ref_counts[tid].0 => fetch_sub(1);
            ghost g => {
                let val = (tid as int, perms@);
                g = self.inst.borrow().shared_release(val, g, handle.get());
        });

    }

}

} // verus!

}

pub mod log{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    prelude::*,
    map::Map,
    cell::{PCell, CellId},
    atomic_ghost::{AtomicU64, AtomicBool},
    atomic_with_ghost,
};

use crate::Dispatch;
use crate::spec::types::{
    NodeId, ReqId, LogIdx, ConcreteLogEntry,
};
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::cyclicbuffer::{CyclicBuffer, StoredType, LogicalLogIdx};
#[cfg(verus_keep_ghost)] use crate::spec::cyclicbuffer::{stored_type_inv, log_entry_idx, log_entry_alive_value};

use crate::constants::{MAX_REQUESTS, MAX_REPLICAS, MAX_IDX, GC_FROM_HEAD, WARN_THRESHOLD, LOG_SIZE};
use crate::exec::replica::{ReplicaToken, ReplicaId};
use crate::exec::CachePadded;


verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Utils
////////////////////////////////////////////////////////////////////////////////////////////////////

#[verus::line_count::ignore] #[verus::trusted] #[verifier(external_body)] /* vattr */
pub fn print_starvation_warning(line: u32) {
    eprintln!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verus::trusted] #[verifier(external_body)] /* vattr */
pub fn warn_with_tail_too_big() {
    eprintln!("WARNING: Tail value exceeds the maximum value of u64.");
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Log Entries
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// An entry that sits on the log. Each entry consists of three fields: The operation to
/// be performed when a thread reaches this entry on the log, the replica that appended
/// this operation, and a flag indicating whether this entry is valid.
///
/// `T` is the type on the operation - typically an enum class containing opcodes as well
/// as arguments. It is required that this type be sized and cloneable.
#[repr(align(128))]
pub struct BufferEntry<DT: Dispatch> {
    /// The operation that this entry represents.
    ///
    ///  - Dafny: linear cell: Cell<CB.ConcreteLogEntry>, where
    ///            datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
    ///  - Rust:  pub(crate) operation: Option<T>,
    // pub(crate) operation: Option<UOp>,

    /// Identifies the replica that issued the above operation.
    ///
    ///  - Dafny: as part of ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
    ///  - Rust:  pub(crate) replica: usize,
    // pub(crate) replica: usize,
    pub log_entry: PCell<Option<ConcreteLogEntry<DT>>>,

    /// Indicates whether this entry represents a valid operation when on the log.
    ///
    ///  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
    ///  - Rust:  pub(crate) alivef: AtomicBool,
    pub alive: AtomicBool<_, CyclicBuffer::alive_bits<DT>, _>,

    /// the index into the cyclic buffer of this entry into the cyclig buffer.
    pub cyclic_buffer_idx: Ghost<nat>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>
}

pub open spec fn wf(&self, idx: nat, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.cyclic_buffer_instance@ == cb_inst
        &&& self.cyclic_buffer_idx == idx
    }
    invariant on alive with (cyclic_buffer_idx, cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits<DT>) {
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.key == cyclic_buffer_idx@
        &&& g@.value === v
    }
}
} // struct_with_invariants


////////////////////////////////////////////////////////////////////////////////////////////////////
// NR Log
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// A log of operations that is typically accessed by multiple Replicas/Nodes
///
/// Corresponds to
///  - `pub struct Log<T, LM, M>` in the upstream code
///  - `linear datatype NR` in the dafny code
#[repr(align(128))]
pub struct NrLog<DT: Dispatch>
{
    /// The actual log, a slice of entries.
    ///  - Dafny: linear buffer: lseq<BufferEntry>,
    ///           glinear bufferContents: GhostAtomic<CBContents>,
    ///  - Rust:  pub(crate) slog: Box<[Cell<Entry<T, M>>]>,
    pub slog: Vec<BufferEntry<DT>>,

    /// Completed tail maintains an index <= tail that points to a log entry after which there
    /// are no completed operations across all replicas registered against this log.
    ///
    ///  - Dafny: linear ctail: CachePadded<Atomic<uint64, Ctail>>,
    ///  - Rust:  pub(crate) ctail: CachePadded<AtomicUsize>,
    pub version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound<DT>, _>>,

    /// Logical index into the above slice at which the log starts.
    ///
    ///  - Dafny: linear head: CachePadded<Atomic<uint64, CBHead>>,
    ///  - Rust:  pub(crate) head: CachePadded<AtomicUsize>,
    pub head: CachePadded<AtomicU64<_, CyclicBuffer::head<DT>, _>>,

    /// Logical index into the above slice at which the log ends. New appends go here.
    ///
    ///  - Dafny: linear globalTail: CachePadded<Atomic<uint64, GlobalTailTokens>>,
    ///  - Rust:  pub(crate) tail: CachePadded<AtomicUsize>,
    pub tail: CachePadded<AtomicU64<_, (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>), _>>,

    /// Array consisting of the local tail of each replica registered with the log.
    /// Required for garbage collection; since replicas make progress over the log
    /// independently, we want to make sure that we don't garbage collect operations
    /// that haven't been executed by all replicas.
    ///
    ///  - Dafny: linear node_info: lseq<NodeInfo>, // NodeInfo is padded
    ///  - Rust:  pub(crate) ltails: [CachePadded<AtomicUsize>; MAX_REPLICAS_PER_LOG],
    ///
    pub/*REVIEW: (crate)*/ local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>), _>>>,  // NodeInfo is padded

    // The upstream Rust version also contains:
    //  - pub(crate) next: CachePadded<AtomicUsize>, the identifier for the next replica
    //  - pub(crate) lmasks: [CachePadded<Cell<bool>>; MAX_REPLICAS_PER_LOG], tracking of alivebits

    pub num_replicas: Ghost<nat>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& 0 < self.num_replicas@ <=  MAX_REPLICAS

        &&& self.local_versions.len() == self.num_replicas

        &&& self.slog.len() == LOG_SIZE
        &&& self.slog.len() == self.cyclic_buffer_instance@.buffer_size()
        &&& self.slog.len() == self.cyclic_buffer_instance@.cell_ids().len()
        &&& (forall |i| #![trigger self.slog[i]] 0 <= i < self.slog.len() ==> {
            &&& self.slog[i].log_entry.id() == (#[trigger]self.cyclic_buffer_instance@.cell_ids()[i])
        })

        &&& (forall |i: nat| i < LOG_SIZE ==> (#[trigger] self.slog[i as int]).wf(i, self.cyclic_buffer_instance@))

        &&& self.unbounded_log_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.unbounded_log_instance() == self.unbounded_log_instance
    }

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound<DT>) {
        &&& g@.instance == unbounded_log_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head<DT>) {
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>)) {
        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>)) {

        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.key == i
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.key == i
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }
}
} // struct_with_invariants!{



impl<DT: Dispatch> NrLog<DT> {
    /// initializes the NrLOg
    pub fn new(num_replicas: usize, log_size: usize) -> (res: (Self, Vec<ReplicaToken>, Tracked<NrLogTokens<DT>>))
        requires
            log_size == LOG_SIZE,
            0 < num_replicas && num_replicas <=  MAX_REPLICAS
        ensures
            res.0.wf(),
            res.0.unbounded_log_instance@ == res.2@.unbounded_log_instance,
            res.0.cyclic_buffer_instance@ == res.2@.cyclic_buffer_instance,
            res.1.len() == num_replicas,
            forall |i| #![trigger res.1[i]] 0 <= i < num_replicas ==> res.1[i].id_spec() == i,
            res.2@.wf(num_replicas as nat)
    {
        //
        // initialize the unbounded log state machine to obtain the tokens
        //
        let tracked unbounded_log_instance     : UnboundedLog::Instance<DT>;
        let tracked ul_log                     : Map<LogIdx, UnboundedLog::log<DT>>;
        let tracked ul_tail                    : UnboundedLog::tail<DT>;
        let tracked ul_replicas                : Map<NodeId,UnboundedLog::replicas<DT>>;
        let tracked mut ul_local_versions      : Map<NodeId,UnboundedLog::local_versions<DT>>;
        let tracked ul_version_upper_bound     : UnboundedLog::version_upper_bound<DT>;
        let tracked ul_combiner                : Map<NodeId,UnboundedLog::combiner<DT>>;

        proof {
            let tracked (
                Tracked(unbounded_log_instance0), // Tracked<Instance>,
                Tracked(ul_log0), //Tracked<Map<LogIdx,log>>,
                Tracked(ul_tail0), //Tracked<tail>,
                Tracked(ul_replicas0), //Tracked<Map<NodeId,replicas>>,
                Tracked(ul_local_versions0), //Tracked<Map<NodeId,local_versions>>,
                Tracked(ul_version_upper_bound0), //Tracked<version_upper_bound>,
                _, //Tracked(ul_local_reads0), //Tracked<Map<ReqId,local_reads>>,
                _, //Tracked(ul_local_updates0), //Tracked<Map<ReqId,local_updates>>,
                Tracked(ul_combiner0), //Tracked<Map<NodeId,combiner>>
                ) = UnboundedLog::Instance::initialize(num_replicas as nat);
            unbounded_log_instance = unbounded_log_instance0;
            ul_log = ul_log0;
            ul_tail = ul_tail0;
            ul_replicas = ul_replicas0;
            ul_local_versions = ul_local_versions0;
            ul_version_upper_bound = ul_version_upper_bound0;
            ul_combiner = ul_combiner0;
        }

        //
        // initialize the log cells
        //

        let ghost mut logical_log_idx;
        proof {
            logical_log_idx = -log_size as int;
        }

        let mut slog_entries : Vec<Option<PCell<Option<ConcreteLogEntry<DT>>>>> = Vec::with_capacity(log_size);
        let ghost mut cell_ids : Seq<CellId> = Seq::empty();
        let tracked mut contents: Map<LogicalLogIdx, StoredType<DT>> = Map::tracked_empty();

        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                log_size == LOG_SIZE,
                logical_log_idx == log_idx - log_size,
                -log_size <= logical_log_idx <= 0,
                slog_entries.len() == log_idx,
                cell_ids.len() == log_idx,
                forall |i| 0 <= i < log_idx ==> (#[trigger] slog_entries[i]).is_Some(),
                forall |i| 0 <= i < log_idx ==> #[trigger] cell_ids[i] == (#[trigger]slog_entries[i]).get_Some_0().id(),
                forall |i| -log_size <= i < logical_log_idx <==> #[trigger] contents.contains_key(i),
                forall |i| #[trigger] contents.contains_key(i) ==> stored_type_inv(contents[i], i, cell_ids[log_entry_idx(i, log_size as nat) as int], unbounded_log_instance),

        {
            // pub log_entry: PCell<ConcreteLogEntry>,
            // create the log entry cell, TODO: create the concrete log entry here?
            let (pcell, token) = PCell::new(Option::None);

            // add the cell to the log entries for later, store the id
            proof { cell_ids = cell_ids.push(pcell.id()); }
            slog_entries.push(Option::Some(pcell));

            // create the stored type
            let tracked stored_type = StoredType {
                cell_perms: token.get(),
                log_entry: Option::None
            };

            // add the stored type to the contents map
            proof {
                contents.tracked_insert(logical_log_idx, stored_type);
            }

            log_idx = log_idx + 1;
            proof {
                logical_log_idx = logical_log_idx + 1;
            }
        }

        //
        // Create the cyclic buffer state machine
        //

        let tracked cyclic_buffer_instance  : CyclicBuffer::Instance<DT>;
        let tracked cb_head                 : CyclicBuffer::head<DT>;
        let tracked cb_tail                 : CyclicBuffer::tail<DT>;
        let tracked mut cb_local_versions   : Map<NodeId, CyclicBuffer::local_versions<DT>>;
        let tracked mut cb_alive_bits       : Map<LogIdx, CyclicBuffer::alive_bits<DT>>;
        let tracked cb_combiners            : Map<NodeId, CyclicBuffer::combiner<DT>>;

        proof {
            let tracked (
                Tracked(cyclic_buffer_instance0), // CyclicBuffer::Instance>;
                Tracked(cb_head0),                // CyclicBuffer::head>;
                Tracked(cb_tail0),                // CyclicBuffer::tail>;
                Tracked(cb_local_versions0),      // Map<NodeId, CyclicBuffer::local_versions>;
                Tracked(cb_alive_bits0),          // Map<LogIdx, CyclicBuffer::alive_bits>;
                Tracked(cb_combiner0),            // Map<NodeId, CyclicBuffer::combiner>;
            ) = CyclicBuffer::Instance::initialize(log_size as nat, num_replicas as nat, contents, cell_ids, unbounded_log_instance, contents);
            cyclic_buffer_instance = cyclic_buffer_instance0;
            cb_head = cb_head0;
            cb_tail = cb_tail0;
            cb_local_versions = cb_local_versions0;
            cb_alive_bits = cb_alive_bits0;
            cb_combiners = cb_combiner0;
        }

        //
        // build up the actual log
        //

        let mut slog : Vec<BufferEntry<DT>> = Vec::with_capacity(log_size);
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                slog_entries.len() == log_size,
                slog.len() == log_idx,
                cell_ids.len() == log_size,
                forall |i| #![trigger slog[i]] 0 <= i < log_idx ==> {
                    &&& slog[i].wf(i as nat, cyclic_buffer_instance)
                    &&& slog[i].log_entry.id() ==  (#[trigger]cell_ids[i])
                },
                forall |i| log_idx <= i < log_size ==> cb_alive_bits.contains_key(i),
                forall |i| #![trigger cb_alive_bits[i]] log_idx <= i < log_size ==> {
                    &&& cb_alive_bits[i]@.key == i
                    &&& cb_alive_bits[i]@.value == false
                    &&& cb_alive_bits[i]@.instance == cyclic_buffer_instance
                },
                forall |i| 0 <= i < log_idx ==> slog_entries.spec_index(i).is_None(),
                forall |i| #![trigger slog_entries[i]] log_idx <= i < log_size ==> {
                    &&& slog_entries[i].is_Some()
                    &&& slog_entries[i].get_Some_0().id() == cell_ids[i]
                }
        {
            let tracked cb_alive_bit;
            proof {
                cb_alive_bit = cb_alive_bits.tracked_remove(log_idx as nat);
            }

            let mut log_entry = Option::None;
            slog_entries.set_and_swap(log_idx, &mut log_entry);
            assert(log_entry.is_Some());
            let log_entry = log_entry.unwrap();

            let cb_inst = Tracked(cyclic_buffer_instance.clone());

            let entry = BufferEntry {
                log_entry: log_entry,
                alive: AtomicBool::new(Ghost((Ghost(log_idx as nat), cb_inst)), false, Tracked(cb_alive_bit)),
                cyclic_buffer_idx: Ghost(log_idx as nat),
                cyclic_buffer_instance: Tracked(cyclic_buffer_instance.clone())
            };
            slog.push(entry);

            log_idx = log_idx + 1;
        }

        let ul_inst = Tracked(unbounded_log_instance.clone());
        let version_upper_bound = CachePadded(AtomicU64::new(Ghost(ul_inst), 0, Tracked(ul_version_upper_bound)));

        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let head = CachePadded(AtomicU64::new(Ghost(cb_inst), 0, Tracked(cb_head)));

        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let ul_inst = Tracked(unbounded_log_instance.clone());
        let tail = CachePadded(AtomicU64::new(Ghost((cb_inst, ul_inst)), 0, Tracked((ul_tail, cb_tail))));
        let mut local_versions : Vec<CachePadded<AtomicU64<(Tracked<UnboundedLog::Instance<DT>>, Tracked<CyclicBuffer::Instance<DT>>, int), (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>), _>>>= Vec::with_capacity(num_replicas);


        let mut nid = 0;
        while nid < num_replicas
            invariant
                0 <= nid <= num_replicas,
                local_versions.len() == nid,
                forall |i| nid <= i < num_replicas ==> ul_local_versions.contains_key(i),
                forall |i| nid <= i < num_replicas ==> cb_local_versions.contains_key(i),
                forall |i| #![trigger cb_local_versions[i]] nid <= i < num_replicas ==> {
                    &&& cb_local_versions[i]@.instance == cyclic_buffer_instance
                    &&& cb_local_versions[i]@.key == i
                    &&& cb_local_versions[i]@.value == 0
                },
                forall |i| #![trigger ul_local_versions[i]] nid <= i < num_replicas ==> {
                    &&& ul_local_versions[i]@.instance == unbounded_log_instance
                    &&& ul_local_versions[i]@.key == i
                    &&& ul_local_versions[i]@.value == 0
                },
                forall |i: int| #![trigger local_versions[i]] 0 <= i < local_versions.len() ==> {
                    &&& local_versions[i].0.well_formed()
                    &&& local_versions[i].0.constant().0 == unbounded_log_instance
                    &&& local_versions[i].0.constant().1 == cyclic_buffer_instance
                    &&& local_versions[i].0.constant().2 == i
                }
        {
            let ghost mut nid_ghost;
            let tracked ul_version;
            let tracked cb_version;
            proof {
                nid_ghost = nid as int;
                ul_version = ul_local_versions.tracked_remove(nid as nat);
                cb_version = cb_local_versions.tracked_remove(nid as nat);
            }

            let cb_inst = Tracked(cyclic_buffer_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());

            local_versions.push(CachePadded(AtomicU64::new(Ghost((ul_inst, cb_inst, nid_ghost)), 0, Tracked((ul_version, cb_version)))));

            nid = nid + 1;
        }

        //
        // Create the replica tokens
        //

        let mut replica_tokens : Vec<ReplicaToken> = Vec::with_capacity(num_replicas);
        let mut idx = 0;
        while idx < num_replicas
            invariant
                0 <= idx <= num_replicas,
                num_replicas <= MAX_REPLICAS,
                replica_tokens.len() == idx,
                forall |i| #![trigger replica_tokens[i]] 0 <= i < idx ==> replica_tokens[i].id_spec() == i,
        {
            replica_tokens.push(ReplicaToken::new(idx as ReplicaId));
            idx = idx + 1;
        }

        let ghost mut num_replicas_ghost; proof { num_replicas_ghost = num_replicas as nat };

        let tracked config = NrLogTokens {
            num_replicas: num_replicas_ghost,
            replicas: ul_replicas,
            combiners: ul_combiner,
            cb_combiners,
            unbounded_log_instance: unbounded_log_instance.clone(),
            cyclic_buffer_instance: cyclic_buffer_instance.clone(),
        };

        let log = NrLog {
            slog,
            version_upper_bound,
            head,
            tail,
            local_versions,
            num_replicas : Ghost(num_replicas as nat),
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
        };

        (log, replica_tokens, Tracked(config))
    }


    /// Returns a physical index given a logical index into the shared log.
    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() == LOG_SIZE
        ensures
            result as nat == self.index_spec(logical as nat),
            result == log_entry_idx(logical as int, self.slog.len() as nat),
            result < self.slog.len()
    {
        (logical as usize) % self.slog.len()
    }

    pub/*REVIEW: (crate)*/ open spec fn index_spec(&self, logical: nat) -> nat
        recommends self.slog.len() == LOG_SIZE
    {
        logical % (self.slog.len() as nat)
    }

    #[inline(always)]
    pub(crate) fn is_alive_value(&self, logical: u64) -> (result: bool)
        requires
            self.slog.len() == LOG_SIZE
        ensures
            result == self.is_alive_value_spec(logical as int),
            result == log_entry_alive_value(logical as int, self.slog.len() as nat)
    {
        ((logical as usize) / LOG_SIZE % 2) == 0
    }

    pub/*REVIEW: (crate)*/ open spec fn is_alive_value_spec(&self, logical: int) -> bool
        recommends self.slog.len() == LOG_SIZE
    {
        ((logical / (LOG_SIZE as int)) % 2) == 0
    }


    /// This method returns the current version upper bound value for the log.
    ///
    ///  - Rust: get_ctail()
    ///  - Dafny: n/a part of do-read
    pub(crate) fn get_version_upper_bound(&self, local_reads: Tracked<UnboundedLog::local_reads<DT>>)
        -> (ret: (u64, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_Init()
        ensures
            ret.1@@.value.is_VersionUpperBound(),
            ret.1@@.value.get_VersionUpperBound_version_upper_bound() == ret.0 as nat,
            ret.1@@.value.get_VersionUpperBound_op() == local_reads@@.value.get_Init_op(),
            ret.1@@.instance == self.unbounded_log_instance@,
            ret.1@@.key == local_reads@@.key
    {
        let tracked local_reads = local_reads.get();
        let ghost rid = local_reads@.key;

        let tracked new_local_reads_g : UnboundedLog::local_reads<DT>;

        let res = atomic_with_ghost!(
            &self.version_upper_bound.0 => load();
            returning res;
            ghost g => {
                new_local_reads_g = self.unbounded_log_instance.borrow()
                                            .readonly_version_upper_bound(rid, &g, local_reads);
            }
        );

        (res, Tracked(new_local_reads_g))
    }

    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(&self, node_id: ReplicaId, version_upper_bound: u64,
                                        local_reads: Tracked<UnboundedLog::local_reads<DT>>)
            -> (result: (bool, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            node_id < self.local_versions.len(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_VersionUpperBound(),
            local_reads@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound
        ensures
            result.0 ==> result.1@@.value.is_ReadyToRead(),
            result.0 ==> result.1@@.value.get_ReadyToRead_node_id() == node_id,
            result.0 ==> result.1@@.value.get_ReadyToRead_op() == local_reads@@.value.get_VersionUpperBound_op(),
            !result.0 ==> result.1 == local_reads,
            result.1@@.instance == self.unbounded_log_instance@,
            result.1@@.key == local_reads@@.key
    {
        // obtain the request id from the local_reads token
        let rid_g : Ghost<ReqId> = Ghost(local_reads@@.key);
        let tracked new_local_reads_g: UnboundedLog::local_reads<DT>;

        // obtain the local version
        let local_version = &self.local_versions[node_id as usize].0;

        let res = atomic_with_ghost!(
            local_version => load();
            returning res;
            ghost g => {
                new_local_reads_g = if res >= version_upper_bound {
                    self.unbounded_log_instance
                        .borrow()
                        .readonly_ready_to_read(rid_g.view(), node_id as NodeId, &g.0, local_reads.get())
                } else {
                    local_reads.get()
                };
            }
        );

        (res >= version_upper_bound, Tracked(new_local_reads_g))
    }


    proof fn unbounded_log_append_entries(tracked &self, nid: nat, ridx: nat, tracked state: AppendEntriesGhostState<DT>) -> (tracked ret: AppendEntriesGhostState<DT>)
        requires
            self.wf(),
            state.idx == 0,
            state.wf(nid, ridx, self.unbounded_log_instance@),
        ensures
            ret.request_ids == state.request_ids,
            ret.operations == state.operations,
            ret.idx == ridx + 1,
            ret.old_tail == state.old_tail,
            ret.wf(nid, ridx, self.unbounded_log_instance@),
        decreases
            ridx
    {
        let tracked mut state = state;

        if ridx != 0 {
            state = self.unbounded_log_append_entries(nid, (ridx - 1) as nat, state);
        }

        let tracked AppendEntriesGhostState {
            idx,
            old_tail,
            mut log_entries,
            mut local_updates,
            combiner,
            mut tail,
            request_ids,
            operations
        } = state;

        // get the local update and the
        let reqid = request_ids[ridx as int];
        let tracked local_update = local_updates.tracked_remove(ridx);

        let tracked update_result = self.unbounded_log_instance.borrow()
            .update_place_ops_in_log_one(nid as nat, reqid, &mut tail, local_update, combiner);

        let tracked combiner = update_result.2.get();
        log_entries.tracked_insert(ridx, update_result.0.get());
        local_updates.tracked_insert(ridx, update_result.1.get());

        let tracked res = AppendEntriesGhostState {
            idx : idx + 1,
            old_tail,
            log_entries,
            local_updates,
            combiner,
            tail,
            request_ids,
            operations
        };
        res
    }


    /// Inserts a slice of operations into the log.
    #[inline(always)]
    pub fn append(&self, replica_token: &ReplicaToken, operations: &Vec<DT::WriteOperation>,
        // responses and actual replica are part of the closure
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        // here we also need to pass the mut replica
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            old(responses).len() == 0,
            ghost_data@.append_pre(replica_token@, old(actual_replica).view(), operations@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
            operations.len() <= MAX_REQUESTS
        ensures
            result@.append_post(ghost_data@, replica_token@, actual_replica.view(), operations@, responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@)
    {
        let tracked mut ghost_data_new = ghost_data.get();

        let nid = replica_token.id() as usize;

        let nops = operations.len();

        let mut iteration = 1;
        let mut waitgc = 1;

        loop
            invariant
                self.wf(),
                0 <= waitgc <= WARN_THRESHOLD,
                0 <= iteration <= WARN_THRESHOLD,
                responses.len() == 0,
                replica_token@ < self.local_versions.len(),
                nid == replica_token@,
                nops == operations.len(),
                nops <= MAX_REQUESTS,
                ghost_data_new.cb_combiner@@.value == ghost_data@.cb_combiner@@.value,
                ghost_data_new.request_ids@ == ghost_data@.request_ids@,
                ghost_data_new.append_pre(replica_token@, actual_replica.view(), operations@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
        {
            // unpack stuff
            let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids} = ghost_data_new;
            let tracked mut cb_combiner = cb_combiner.get();
            let tracked mut combiner = combiner.get();
            let tracked mut local_updates = local_updates.get();

            if iteration == WARN_THRESHOLD {
                print_starvation_warning(line!());
                iteration = 0;
            }

            iteration = iteration + 1;

            // let tail = self.tail.load(Ordering::Relaxed);
            let tail = atomic_with_ghost!(
                &self.tail.0 => load();
                returning tail;
                ghost g => { }
            );

            // let head = self.head.load(Ordering::Relaxed);
            let head = atomic_with_ghost!(
                &self.head.0 => load();
                returning tail;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow()
                        .advance_tail_start(nid as nat, &g, cb_combiner);
                }
            );

            // If there are fewer than `GC_FROM_HEAD` entries on the log, then just
            // try again. The replica that reserved entry (h + self.slog.len() - GC_FROM_HEAD)
            // is currently trying to advance the head of the log. Keep refreshing the
            // replica against the log to make sure that it isn't deadlocking GC.
            // if tail > head + self.slog.len() - GC_FROM_HEAD  {  }
            if tail > head + (self.slog.len() as u64 - GC_FROM_HEAD as u64) {
                if waitgc == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    waitgc = 0;
                }

                waitgc = waitgc + 1;

                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_abort(nid as nat, cb_combiner);
                }

                // overwrite the request_ids here, as we're not executing any local updates
                let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates: Tracked(local_updates), ghost_replica, combiner: Tracked(combiner), cb_combiner: Tracked(cb_combiner), request_ids: Ghost(Seq::empty())};
                let ghost_data0 = self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));

                let tracked ghost_data0 = ghost_data0.get();

                proof {
                    ghost_data_new = NrLogAppendExecDataGhost {
                        local_updates: ghost_data0.local_updates,
                        ghost_replica: ghost_data0.ghost_replica,
                        combiner: ghost_data0.combiner,
                        cb_combiner: ghost_data0.cb_combiner,
                        request_ids
                    };
                }

                // upstream has an advance_head here, but dafny doesn't
                // let ghost_data0 = self.advance_head(replica_token, responses, actual_replica, ghost_data0);
                continue;
            }

            let new_tail = tail + (nops as u64);

            // capture the warning here
            if new_tail >= MAX_IDX {
                warn_with_tail_too_big();
                ////////////////////////////////////////////////////////////////////////////////////
                // !!! THIS IS A PANIC CASE! WE DO NOT RETURN FROM HERE !!!
                ////////////////////////////////////////////////////////////////////////////////////
                #[allow(while_true)]
                while true {} // TODO: is that fine?
            }


            // If on adding in the above entries there would be fewer than `GC_FROM_HEAD`
            // entries left on the log, then we need to advance the head of the log.
            let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64 ;

            // Try reserving slots for the operations. If that fails, then restart
            // from the beginning of this loop.
            // if self.tail.compare_exchange_weak(tail, tail + nops, Ordering::Acquire, Ordering::Acquire) !+ Ok(tail) {
            //     continue;
            // }

            let tracked mut cb_log_entries : Map<int, StoredType<DT>> = Map::tracked_empty();
            let tracked mut log_entries : Map<nat,UnboundedLog::log<DT>> = Map::tracked_empty();

            let result = atomic_with_ghost!(
                //&self.tail.0 => compare_exchange(tail, new_tail);
                &self.tail.0 => compare_exchange_weak(tail, new_tail);
                update prev -> next;
                returning result;
                ghost g => {
                    if matches!(result, Result::Ok(tail)) {
                        let tracked (mut unbounded_tail, mut cb_tail) = g;

                        let tracked (_, Tracked(cb_log_entries0), Tracked(cb_combiner0))
                             = self.cyclic_buffer_instance.borrow()
                                .advance_tail_finish(nid as nat, new_tail as nat, &mut cb_tail, cb_combiner);

                        cb_combiner = cb_combiner0;
                        cb_log_entries = cb_log_entries0;

                        // transition to the placed phase
                        combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);

                        if request_ids.view().len() > 0 {
                            let tracked append_entries_ghost_state = AppendEntriesGhostState {
                                idx : 0,
                                old_tail: tail as nat,
                                log_entries,
                                local_updates,
                                combiner,
                                tail: unbounded_tail,
                                request_ids: request_ids.view(),
                                operations: operations.view()
                            };

                            let tracked append_entries_ghost_state = self.unbounded_log_append_entries(nid as nat, (request_ids.view().len() - 1) as nat, append_entries_ghost_state);
                            log_entries = append_entries_ghost_state.log_entries;
                            combiner = append_entries_ghost_state.combiner;
                            unbounded_tail = append_entries_ghost_state.tail;
                            local_updates = append_entries_ghost_state.local_updates;
                            assert(combiner@.value.get_Placed_queued_ops() =~= request_ids@);
                        } else {
                            assert(combiner@.value.get_Placed_queued_ops() =~= request_ids@);
                        }

                        g = (unbounded_tail, cb_tail);
                    } else {
                        cb_combiner = self.cyclic_buffer_instance
                            .borrow()
                            .advance_tail_abort(nid as nat, cb_combiner);
                    }
                }
            );

            if !matches!(result, Result::Ok(tail)) {
                // assemble the struct again
                proof {
                    ghost_data_new = NrLogAppendExecDataGhost {
                        local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                        ghost_replica,  // Tracked<UnboundedLog::replicas>,
                        combiner: Tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                        cb_combiner: Tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                        request_ids,    // Ghost<Seq<ReqId>>,
                    };
                }
                continue;
            }

            let ghost cell_ids = self.cyclic_buffer_instance@.cell_ids();
            let ghost buffer_size = self.cyclic_buffer_instance@.buffer_size();

            // Successfully reserved entries on the shared log. Add the operations in.
            let mut idx = 0;
            while idx < nops
                invariant
                    self.wf(),
                    0 <= idx <= nops,
                    tail + idx <= new_tail,
                    tail + nops == new_tail,
                    nops == operations.len(),
                    nops == request_ids@.len(),
                    buffer_size == LOG_SIZE,
                    cell_ids == self.cyclic_buffer_instance@.cell_ids(),
                    cell_ids.len() == buffer_size,
                    cb_combiner@.key == nid,
                    cb_combiner@.value.is_Appending(),
                    cb_combiner@.value.get_Appending_cur_idx() == tail + idx,
                    cb_combiner@.value.get_Appending_tail() == new_tail,
                    cb_combiner@.value.get_Appending_cur_idx() <= cb_combiner@.value.get_Appending_tail(),
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    forall |i| #![trigger log_entries[i]] idx <= i < request_ids@.len() ==> {
                        &&& (#[trigger]log_entries.contains_key(i))
                        &&& log_entries[i]@.key == tail + i
                        &&& log_entries[i]@.instance == self.unbounded_log_instance@
                        &&& log_entries[i]@.value.node_id == nid as nat
                        //
                        // The following will result in a resource limit exceeded
                        //
                        &&& log_entries[i]@.value.op == operations[i as int]
                        //
                        // Adding the `&` below will fix this.
                        //
                        // &&& log_entries[i]@.value.op == &operations[i as int]
                    },
                    forall |i| (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(i),
                    forall |i| cb_log_entries.contains_key(i) ==> stored_type_inv(#[trigger] cb_log_entries.index(i), i, cell_ids[log_entry_idx(i, buffer_size) as int], self.unbounded_log_instance@),
            {
                let tracked cb_log_entry;
                proof {
                    cb_log_entry = cb_log_entries.tracked_remove((tail + idx) - LOG_SIZE);
                }
                let tracked mut cb_log_entry_perms = cb_log_entry.cell_perms;


                // the logical index into the log
                let logical_log_idx = tail + idx as u64;
                let log_idx = self.index(logical_log_idx);

                // unsafe { (*e).operation = Some(op.clone()) };
                // unsafe { (*e).replica = idx.0 };
                let new_log_entry = ConcreteLogEntry {
                    op: DT::clone_write_op(&operations[idx as usize]),
                    node_id: nid as u64,
                };

                // update the log entry in the buffer
                self.slog[log_idx].log_entry.replace(Tracked(&mut cb_log_entry_perms), Option::Some(new_log_entry));

                // unsafe { (*e).alivef.store(m, Ordering::Release) };
                let m = self.is_alive_value(logical_log_idx as u64);

                atomic_with_ghost!(
                    &self.slog[log_idx].alive => store(m);
                    ghost g => {
                        let tracked new_stored_type = StoredType {
                            cell_perms: cb_log_entry_perms,
                            log_entry: Option::Some(log_entries.tracked_remove(idx as nat)),
                        };

                        let tracked (Tracked(alive_bit), Tracked(cb_combiner0))
                            = self.cyclic_buffer_instance.borrow()
                            .append_flip_bit(nid as NodeId, new_stored_type, new_stored_type, g, cb_combiner);

                        g = alive_bit;
                        cb_combiner = cb_combiner0;
                    }
                );

                idx = idx + 1;
            }

            assert(forall |i| #![trigger log_entries[i]] idx <= i < request_ids@.len() ==> {
                &&& #[trigger]log_entries.contains_key(i)
                &&& log_entries[i]@.key == tail + i
                &&& log_entries[i]@.instance == self.unbounded_log_instance@
                &&& log_entries[i]@.value.node_id == nid as nat
                &&& log_entries[i]@.value.op == operations[i as int]
            });
            assert(forall |i| (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(i));
            assert(forall |i| cb_log_entries.contains_key(i) ==> stored_type_inv(#[trigger] cb_log_entries.index(i), i, cell_ids[log_entry_idx(i, buffer_size) as int], self.unbounded_log_instance@));


            proof {
                cb_combiner = self.cyclic_buffer_instance.borrow().append_finish(nid as nat, cb_combiner);

                ghost_data_new = NrLogAppendExecDataGhost {
                    local_updates:Tracked(local_updates),   // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,                          // Tracked<UnboundedLog::replicas>,
                    combiner: Tracked(combiner),            // Tracked<UnboundedLog::combiner>,
                    cb_combiner: Tracked(cb_combiner),      // Tracked<CyclicBuffer::combiner>,
                    request_ids,                            // Ghost<Seq<ReqId>>,
                };
            }

            if advance {
                let ghost_data_new = self.advance_head(replica_token, responses, actual_replica, Tracked(ghost_data_new));
                return ghost_data_new;
            } else {
                return Tracked(ghost_data_new);
            }
        }
    }


    /// Advances the head of the log forward. If a replica has stopped making
    /// progress, then this method will never return. Accepts a closure that is
    /// passed into execute() to ensure that this replica does not deadlock GC.
    #[inline(always)]
    fn advance_head(&self, replica_token: &ReplicaToken,
                    // the following were part of the closure
                    responses: &mut Vec<DT::Response>,
                    actual_replica: &mut DT,
                    // ghost state for execute etc.
                    ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>)
            -> (res: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token.wf(self.num_replicas@),
            ghost_data@.advance_head_pre(replica_token.id_spec(), old(actual_replica).view(), old(responses)@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
        ensures
            res@.advance_head_post(ghost_data@, replica_token.id_spec(), actual_replica.view(), responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
    {
        let mut ghost_data_new = ghost_data;

        let mut iteration = 1;
        loop
            invariant
                self.wf(),
                replica_token.wf(self.num_replicas@),
                ghost_data_new@.cb_combiner@@.value.is_Idle(),
                ghost_data_new@.combiner@@.value.is_Placed() ==> ghost_data_new@.pre_exec(responses@),
                ghost_data_new@.advance_head_post(ghost_data@, replica_token.id_spec(), actual_replica.view(), responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
                0 <= iteration <= WARN_THRESHOLD
        {
            let Tracked(ghost_data0) = ghost_data_new;
            let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids } = ghost_data0;
            let tracked mut cb_combiner = cb_combiner.get();

            // let global_head = self.head.load(Ordering::Relaxed);
            let global_head = atomic_with_ghost!(
                &self.head.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );

            // let f = self.tail.load(Ordering::Relaxed);
            let global_tail = atomic_with_ghost!(
                &self.tail.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );

            let (min_local_version, cb_combiner0) = self.find_min_local_version(Tracked(cb_combiner));
            let tracked mut cb_combiner = cb_combiner0.get();

            // If we cannot advance the head further, then start
            // from the beginning of this loop again. Before doing so, try consuming
            // any new entries on the log to prevent deadlock.
            if min_local_version == global_head {
                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_abort(replica_token.id_spec(), cb_combiner);
                }
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    // let tracked cb_combiner = Tracked(cb_combiner);
                    // let tracked ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                    // return Tracked(ghost_data);
                    iteration = 0;
                }
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                ghost_data_new = self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
                continue;
            }



            // There are entries that can be freed up; update the head offset.
            // self.head.store(min_local_tail, Ordering::Relaxed);
            atomic_with_ghost!(
                &self.head.0 => store(min_local_version);
                update old_val -> new_val;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_finish(replica_token.id_spec(), &mut g, cb_combiner);
            });

            if global_tail < min_local_version + self.slog.len() as u64 - GC_FROM_HEAD as u64 {
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data_new = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                return Tracked(ghost_data_new);
            }

            let cb_combiner = Tracked(cb_combiner);
            let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };

            // replica_token@ < self.local_versions.len(),
            ghost_data_new = self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
        }
    }

    /// proof function that transitions local updates into the done state.
    proof fn execute_update_done_multiple(tracked &self, request_ids: Seq<ReqId>,
        tracked local_updates: Map<nat, UnboundedLog::local_updates<DT>>, tracked version_upper_bound: &UnboundedLog::version_upper_bound<DT>)
         -> (tracked res: Map<nat, UnboundedLog::local_updates<DT>>)
        requires
            self.wf(),
            version_upper_bound@.instance == self.unbounded_log_instance@,
            forall |i| #![trigger local_updates[i]]  0 <= i < request_ids.len() ==> {
                &&& #[trigger]local_updates.contains_key(i)
                &&& local_updates[i]@.key == request_ids[i as int]
                &&& local_updates[i]@.instance == self.unbounded_log_instance@
                &&& local_updates[i]@.value.is_Applied()
                &&& local_updates[i]@.value.get_Applied_idx() < version_upper_bound@.value
            },
        ensures
            forall |i| #![trigger res[i]]  0 <= i < request_ids.len() ==> {
                &&& #[trigger]res.contains_key(i)
                &&& res[i]@.key == request_ids[i as int]
                &&& res[i]@.instance == self.unbounded_log_instance@
                &&& res[i]@.value.is_Done()
                &&& res[i]@.value.get_Done_ret() == local_updates[i]@.value.get_Applied_ret()
            }
        decreases
            request_ids.len()
    {
        if request_ids.len() == 0 {
            return local_updates;
        }

        let tracked mut local_updates_new = local_updates;

        let idx = (request_ids.len() - 1) as nat;

        let tracked local_update = local_updates_new.tracked_remove(idx);
        local_updates_new = self.execute_update_done_multiple(request_ids.subrange(0, request_ids.len() -1), local_updates_new, version_upper_bound);

        let tracked update_done_result = self.unbounded_log_instance.borrow().update_done(request_ids.last(), version_upper_bound,  local_update);

        local_updates_new.tracked_insert(idx, update_done_result);
        return local_updates_new;
    }

    /// Executes a passed in closure (`d`) on all operations starting from a
    /// replica's local tail on the shared log. The replica is identified
    /// through an `idx` passed in as an argument.
    pub(crate) fn execute(&self, replica_token: &ReplicaToken,
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            ghost_data@.execute_pre(replica_token@, old(actual_replica).view(), old(responses)@, self.unbounded_log_instance@, self.cyclic_buffer_instance@)
        ensures
            result@.execute_post(ghost_data@, replica_token@, actual_replica.view(), old(responses)@, responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@)
    {
        let nid = replica_token.id() as usize;

        // somehow can't really do this as a destructor
        let tracked ghost_data = ghost_data.get();
        // let tracked Tracked(ghost_data) = ghost_data;  // XXX: that one here doesn't work?
        let tracked mut local_updates = ghost_data.local_updates.get(); // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
        let tracked mut ghost_replica = ghost_data.ghost_replica.get(); // Tracked<UnboundedLog::replicas>,
        let tracked mut combiner = ghost_data.combiner.get();           // Tracked<UnboundedLog::combiner>,
        let tracked mut cb_combiner = ghost_data.cb_combiner.get();     // Tracked<CyclicBuffer::combiner>,
        let ghost request_ids = ghost_data.request_ids@;            // Ghost<Seq<ReqId>>,

        let ghost mut request_ids_new = request_ids;

        proof {
            // if the combiner in idle, we start it with the trival start transition
            if combiner@.value.is_Ready() {
                combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);
                request_ids_new = Seq::empty();
            }
        }


        // let ltail = self.ltails[idx.0 - 1].load(Ordering::Relaxed);
        let mut local_version = atomic_with_ghost!(
            &self.local_versions[nid].0 => load();
            returning ret;
            ghost g => {
                // this kicks of the state transition in both the cyclic buffer and the unbounded log
                combiner = self.unbounded_log_instance.borrow().exec_load_local_version(nid as nat, &g.0, combiner);
                cb_combiner = self.cyclic_buffer_instance.borrow().reader_start(nid as nat, &g.1, cb_combiner);
            }
        );

        // Check if we have any work to do by comparing our local tail with the log's
        // global tail. If they're equal, then we're done here and can simply return.
        // let gtail = self.tail.load(Ordering::Relaxed);
        let global_tail = atomic_with_ghost!(
            &self.tail.0 => load();
            returning global_tail;
            ghost g => {
                if (local_version == global_tail) {
                    // there has ben no additional updates to be applied, combiner back to idle
                    combiner = self.unbounded_log_instance.borrow().exec_finish_no_change(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_abort(nid as nat, cb_combiner);
                } else {
                    combiner = self.unbounded_log_instance.borrow().exec_load_global_head(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_enter(nid as nat,  &g.1, cb_combiner);
                }
            }
        );

        if local_version == global_tail {
            let tracked ghost_data_ret = NrLogAppendExecDataGhost {
                local_updates : Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                ghost_replica : Tracked(ghost_replica),  // Tracked<UnboundedLog::replicas>,
                combiner      : Tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                cb_combiner   : Tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                request_ids   : Ghost(request_ids),      // Ghost<Seq<ReqId>>,
            };

            // not sure why this one needs to be here?

            assert(ghost_data_ret.common_pred(replica_token@, actual_replica.view(), self.unbounded_log_instance@, self.cyclic_buffer_instance@));

            // assert(ghost_data_ret.cb_combiner@@.value  == ghost_data.cb_combiner@@.value);
            // assert(ghost_data_ret.request_ids == ghost_data.request_ids);
            // assert(ghost_data.combiner@@.value.is_Placed() ==> {
            //     &&& ghost_data_ret.post_exec(ghost_data.request_ids@, responses@)
            // });
            // assert(ghost_data.combiner@@.value.is_Ready() ==> {
            //     &&& ghost_data_ret.combiner@@.value  == ghost_data.combiner@@.value
            //     &&& ghost_data_ret.local_updates == ghost_data.local_updates
            //     &&& responses@ == old(responses)@
            // });

            // assert(ghost_data_ret.execute_post(ghost_data, replica_token@, actual_replica.view(), old(responses)@, responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@));

            return Tracked(ghost_data_ret);
        }

        // Execute all operations from the passed in offset to the shared log's tail.
        // Check if the entry is live first; we could have a replica that has reserved
        // entries, but not filled them into the log yet.
        // for i in ltail..gtail {
        let ghost local_updates_old = local_updates;
        let ghost responses_old = responses@;
        let mut responses_idx : usize = 0;
        while local_version < global_tail
            invariant
                self.wf(),
                ghost_data.combiner@@.value.is_Placed() ==> {
                    &&& ghost_data.combiner@@.value.get_Placed_queued_ops() == request_ids
                    &&& combiner@.value.get_Loop_queued_ops() == request_ids
                },
                ghost_data.combiner@@.value.is_Ready() ==> combiner@.value.get_Loop_queued_ops() == Seq::<ReqId>::empty(),
                combiner@.value.queued_ops() == request_ids_new,
                0 <= local_version <= global_tail,
                0 <= responses_idx as nat <= request_ids_new.len(),
                responses_idx == 0 ==> responses@ == responses_old && local_updates == local_updates_old,
                ghost_data.combiner@@.value.is_Placed() ==> responses.len() == responses_idx,
                request_ids_new.len() <= MAX_REQUESTS,
                ghost_replica@.instance == self.unbounded_log_instance@,
                ghost_replica@.key == nid as nat,
                ghost_replica@.value == actual_replica.view(),

                cb_combiner@.key == nid as nat,
                cb_combiner@.instance == self.cyclic_buffer_instance@,
                cb_combiner@.value.is_Reading(),
                cb_combiner@.value.get_Reading_0().is_Range(),
                cb_combiner@.value.get_Reading_0().get_Range_cur() == local_version,
                cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,

                combiner@.key == nid as nat,
                combiner@.instance == self.unbounded_log_instance@,
                combiner@.value.is_Loop(),
                combiner@.value.get_Loop_queued_ops() == request_ids_new,
                combiner@.value.get_Loop_lversion() == local_version,
                combiner@.value.get_Loop_tail() == global_tail,
                combiner@.value.get_Loop_idx() == responses_idx,

                forall |i| #![trigger local_updates[i]] responses_idx <= i < request_ids_new.len() ==>  {
                    &&& #[trigger ]local_updates.contains_key(i)
                    &&& local_updates[i]@.key == request_ids_new[i as int]
                    &&& local_updates[i]@.value.is_Placed()
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                },

                ghost_data.combiner@@.value.is_Placed() ==> forall |i| #![trigger local_updates[i]]  0 <= i < responses_idx ==> {
                    &&& #[trigger]local_updates.contains_key(i)
                    &&& local_updates[i]@.key == request_ids_new[i as int]
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                    &&& local_updates[i]@.value.is_Applied()
                    &&& local_updates[i]@.value.get_Applied_ret() == responses[i as int]
                    &&& local_updates[i]@.value.get_Applied_idx() < combiner@.value.get_Loop_tail()
                }
        {
            // calculating the actual index and the
            let phys_log_idx = self.index(local_version);
            let is_alive_value = self.is_alive_value(local_version);

            let mut iteration = 1;
            let mut is_alive = false;
            // while unsafe { (*e).alivef.load(Ordering::Acquire) != self.lmasks[idx.0 - 1].get() } {
            while !is_alive
                invariant
                    self.wf(),
                    local_version < global_tail,
                    phys_log_idx < self.slog.len(),
                    phys_log_idx as nat == self.index_spec(local_version as nat),
                    is_alive_value == self.is_alive_value_spec(local_version as int),
                    0 <= iteration <= WARN_THRESHOLD,
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    cb_combiner@.key == nid as nat,
                    cb_combiner@.value.is_Reading(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().is_Range(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_cur() == local_version,
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,
                    is_alive ==> cb_combiner@.value.get_Reading_0().is_Guard(),
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_cur() == local_version,
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_end() == global_tail,
                    self.slog.spec_index(phys_log_idx as int).wf(phys_log_idx as nat, self.cyclic_buffer_instance@)
            {
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }

                let alive_bit = atomic_with_ghost!(
                    &self.slog[phys_log_idx].alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            let tracked (_, Tracked(cb_combiner0)) =
                                self.cyclic_buffer_instance.borrow().reader_guard(nid as nat, &g, cb_combiner);
                            cb_combiner = cb_combiner0;
                        }
                    });

                is_alive = alive_bit == is_alive_value;
                iteration = iteration + 1;
            }

            // dispatch the operation to apply the update to the replica
            // unsafe { d((*e).operation.as_ref().unwrap().clone(),(*e).replica == idx.0,) };
            let tracked stored_entry : &StoredType<DT>;
            proof {
                stored_entry = self.cyclic_buffer_instance.borrow().guard_guards(nid as nat, &cb_combiner);
            }

            // read the entry
            let log_entry = self.slog[phys_log_idx].log_entry.borrow(Tracked(&stored_entry.cell_perms));

            // perform the update
            let res = actual_replica.dispatch_mut(DT::clone_write_op(&log_entry.as_ref().unwrap().op));

            if log_entry.as_ref().unwrap().node_id == nid as u64 {
                // case: local dispatch, store the result in the response vector
                proof {
                    // unwrap the entry
                    if let Option::Some(e) = &stored_entry.log_entry {
                        // appeal to the state machien to get that response_idx < request_ids_new.len()
                        self.unbounded_log_instance.borrow().pre_exec_dispatch_local(nid as nat, e, &combiner);

                        let tracked local_update = local_updates.tracked_remove(responses_idx as nat);

                        let tracked (Tracked(ghost_replica0), Tracked(local_update), Tracked(combiner0)) =
                            self.unbounded_log_instance.borrow()
                                .exec_dispatch_local(nid as nat, e, ghost_replica, local_update, combiner);

                        ghost_replica = ghost_replica0;
                        local_updates.tracked_insert(responses_idx as nat, local_update);
                        combiner = combiner0;
                    } else {
                        assert(false);
                    }
                }

                responses.push(res);
                responses_idx = responses_idx + 1;
            } else {
                // case: remote dispatch
                proof {
                    assert(stored_entry.log_entry.get_Some_0().view().value.node_id != nid);
                    if let Option::Some(e) = &stored_entry.log_entry {
                        assert(e.view().value.node_id != nid);
                        // assert(ghost_replica@.key == nid as nat);
                        // assert(combiner@.value.get_Loop_lversion() < combiner@.value.get_Loop_tail());
                        let tracked exec_dispatch_remote_result =
                            self.unbounded_log_instance.borrow().exec_dispatch_remote(nid as nat, e, ghost_replica, combiner);
                        ghost_replica = exec_dispatch_remote_result.0.get();
                        combiner = exec_dispatch_remote_result.1.get();
                    } else {
                        assert(false) // should not happen
                    }
                }
            }

            proof {
                cb_combiner = self.cyclic_buffer_instance.borrow().reader_unguard(nid as nat, cb_combiner);
            }

            local_version = local_version + 1;
        }

        proof {
            self.unbounded_log_instance.borrow().pre_exec_update_version_upper_bound(nid as nat, &combiner);
        }

        // self.ctail.fetch_max(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.version_upper_bound.0 => fetch_max(global_tail);
            ghost g => {
                combiner = self.unbounded_log_instance.borrow().exec_update_version_upper_bound(nid as nat, &mut g, combiner);

                if ghost_data.combiner@@.value.is_Placed() {
                    local_updates = self.execute_update_done_multiple(request_ids_new,  local_updates, &g);
                }
            });

        // self.ltails[idx.0 - 1].store(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.local_versions[nid].0 => store(global_tail);
            ghost g => {
                let tracked (Tracked(ul_local_versions), Tracked(ul_combiner))
                    = self.unbounded_log_instance.borrow().exec_finish(nid as nat, g.0, combiner);
                let tracked (Tracked(cb_local_versions), Tracked(cb_combiner0))
                    = self.cyclic_buffer_instance.borrow().reader_finish(nid as nat, g.1, cb_combiner);

                combiner = ul_combiner;
                cb_combiner = cb_combiner0;

                g = (ul_local_versions, cb_local_versions);
        });

        let tracked ghost_data_ret = NrLogAppendExecDataGhost {
            local_updates : Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
            ghost_replica: Tracked(ghost_replica),  // Tracked<UnboundedLog::replicas>,
            combiner: Tracked(combiner),       // Tracked<UnboundedLog::combiner>,
            cb_combiner: Tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
            request_ids: Ghost(request_ids),    // Ghost<Seq<ReqId>>,
        };

        // not sure why this one needs to be here?
        assert(ghost_data_ret.execute_post(ghost_data, replica_token@, actual_replica.view(), old(responses)@, responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@));

        Tracked(ghost_data_ret)
    }


    /// Loops over all `local_versions` and finds the replica with the lowest version.
    ///
    /// # Returns
    /// The ID (in `LogToken`) of the replica with the lowest tail and the
    /// corresponding/lowest tail `idx` in the `Log`.
    ///
    ///  - Dafny: part of advance_head
    pub(crate) fn find_min_local_version(&self, cb_combiner: Tracked<CyclicBuffer::combiner<DT>>)
                        -> (result: (u64, Tracked<CyclicBuffer::combiner<DT>>))
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle()
        ensures
            result.0 <= MAX_IDX,
            result.1@@.key == cb_combiner@@.key,
            result.1@@.value.is_AdvancingHead(),
            result.1@@.instance == self.cyclic_buffer_instance@,
            result.1@@.value.get_AdvancingHead_idx() == self.num_replicas,
            result.1@@.value.get_AdvancingHead_min_local_version() == result.0
    {
        // let r = self.next.load(Ordering::Relaxed);
        let num_replicas = self.local_versions.len();

        let tracked mut g_cb_comb_new : CyclicBuffer::combiner<DT> = cb_combiner.get();
        let ghost g_node_id = cb_combiner@@.key;

        // let (mut min_replica_idx, mut min_local_tail) = (0, self.ltails[0].load(Ordering::Relaxed));
        let mut min_local_version = atomic_with_ghost!(
            &self.local_versions[0].0 => load();
            returning ret;
            ghost g => {
                g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                        .advance_head_start(g_node_id, &g.1, g_cb_comb_new);
            });

        // Find the smallest local tail across all replicas.
        // for idx in 1..r {
        //    let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
        //    min_local_tail = min(min_local_tail, cur_local_tail)
        //}
        let mut idx : usize = 1;
        while idx < num_replicas
            invariant
                self.wf(),
                0 <= idx <= num_replicas,
                min_local_version <= MAX_IDX,
                g_cb_comb_new@.instance == self.cyclic_buffer_instance,
                g_cb_comb_new@.value.is_AdvancingHead(),
                g_cb_comb_new@.value.get_AdvancingHead_idx() == idx,
                g_cb_comb_new@.value.get_AdvancingHead_min_local_version() == min_local_version,
                g_cb_comb_new.view().key == g_node_id,
                num_replicas == self.local_versions.len()
        {
            // let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
            let cur_local_tail = atomic_with_ghost!(
                &self.local_versions[idx].0 => load();
                returning ret;
                ghost g => {
                    g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                            .advance_head_next(g_node_id, &g.1, g_cb_comb_new);
                });
            if cur_local_tail < min_local_version {
                min_local_version = cur_local_tail;
            }

            idx = idx + 1;
        }
        (min_local_version, Tracked(g_cb_comb_new))
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost State
////////////////////////////////////////////////////////////////////////////////////////////////////


/// Data structure that is passed between the append and exec functins of the log.
pub tracked struct NrLogAppendExecDataGhost<DT: Dispatch> {
    pub /* REVIEW (crate) */ local_updates  : Tracked::<Map<ReqId, UnboundedLog::local_updates<DT>>>,
    pub /* REVIEW (crate) */ ghost_replica  : Tracked<UnboundedLog::replicas<DT>>,
    pub /* REVIEW (crate) */ combiner       : Tracked<UnboundedLog::combiner<DT>>,
    pub /* REVIEW (crate) */ cb_combiner    : Tracked<CyclicBuffer::combiner<DT>>,
    pub /* REVIEW (crate) */ request_ids    : Ghost<Seq<ReqId>>,
}

impl<DT: Dispatch> NrLogAppendExecDataGhost<DT> {

    /// some common predicate that ties the state to the node and instances
    pub open spec fn common_pred(&self, nid: NodeId, data: DT::View,  inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool
    {
        &&& (forall |i| 0 <= i < self.request_ids@.len() ==> {
            &&& (#[trigger] self.local_updates@.contains_key(i))
            &&& self.local_updates@[i]@.instance == inst
        })
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == inst
        &&& self.ghost_replica@@.value == data
        &&& self.combiner@@.key == nid
        &&& self.combiner@@.instance == inst
        &&& self.cb_combiner@@.key == nid
        &&& self.cb_combiner@@.instance == cb_inst
        &&& self.request_ids@.len() <= MAX_REQUESTS
    }

    pub open spec fn append_pre(&self,  nid: NodeId, data: DT::View, ops: Seq<DT::WriteOperation>, inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& (forall |i| #![trigger self.local_updates@[i]]0 <= i < self.request_ids@.len() ==> {
            &&& #[trigger] self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Init()
            &&& self.local_updates@[i]@.value.get_Init_op() == ops[i as int]
        })
        &&& self.combiner@@.value.is_Ready()
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.request_ids@.len() == ops.len()
    }

    pub open spec fn append_post(&self, pre: Self, nid: NodeId,  data: DT::View, operations: Seq<DT::WriteOperation>, responses: Seq<DT::Response>,  inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Ready() ==> self.post_exec(pre.request_ids@, responses)
        &&& self.combiner@@.value.is_Placed() ==> self.pre_exec(responses)
        &&& self.cb_combiner@@.value == pre.cb_combiner@@.value // other fields in common_pred
        &&& self.request_ids == pre.request_ids
    }

    pub open spec fn execute_pre(&self, nid: NodeId, data: DT::View, responses: Seq<DT::Response>, inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Placed() ==> self.pre_exec(responses)
        &&& self.combiner@@.value.is_Ready() ==> {
            &&& self.request_ids@.len() == responses.len()
        }
    }

    pub open spec fn execute_post(&self, pre: Self, nid: NodeId, data: DT::View, responses_old: Seq<DT::Response>, responses: Seq<DT::Response>, inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& self.cb_combiner@@.value  == pre.cb_combiner@@.value
        &&& self.request_ids == pre.request_ids
        &&& pre.combiner@@.value.is_Placed() ==> {
            &&& self.post_exec(pre.request_ids@, responses)
        }
        &&& pre.combiner@@.value.is_Ready() ==> {
            &&& self.combiner@@.value  == pre.combiner@@.value
            &&& self.local_updates == pre.local_updates
            &&& responses == responses_old
        }
    }

    pub open spec fn advance_head_pre(&self, nid: NodeId, data: DT::View, responses: Seq<DT::Response>, inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& self.pre_exec(responses)
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.combiner@@.value.is_Placed()
    }

    pub open spec fn advance_head_post(&self, pre: Self, nid: NodeId, data: DT::View, responses: Seq<DT::Response>,  inst: UnboundedLog::Instance<DT>, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)

        &&& self.request_ids == pre.request_ids
        &&& self.cb_combiner@@.value == pre.cb_combiner@@.value
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Ready() ==> {
            &&& self.post_exec(self.request_ids@, responses)
        }
        &&& self.combiner@@.value.is_Placed() ==> {
            &&& responses.len() == 0
            &&& self.local_updates == pre.local_updates
            &&& self.combiner@@.value == pre.combiner@@.value
            &&& self.ghost_replica@@.value == pre.ghost_replica@@.value
        }
    }

    // corresponds to Dafny's pre_exec() function
    pub open spec fn pre_exec(&self, responses: Seq<DT::Response>) -> bool {
        &&& responses.len() == 0
        &&& self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.get_Placed_queued_ops() == self.request_ids
        &&& (forall |i| #![trigger self.local_updates@[i]]0 <= i < self.request_ids@.len() ==> {
            &&& self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Placed()
        })
    }

    // corresponds to Dafny's post_exec() function
    pub open spec fn post_exec(&self, request_ids: Seq<ReqId>, responses: Seq<DT::Response>) -> bool {
        &&& request_ids.len() == responses.len()
        &&& self.combiner@@.value.is_Ready()
        &&& (forall |i| #![trigger self.local_updates@[i]] 0 <= i < request_ids.len() ==> {
            &&& self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.value.is_Done()
            &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
            &&& self.local_updates@[i]@.key == request_ids[i as int]
        })
    }
}



struct_with_invariants!{
/// keeps track of the recursive state when applying updates to the unbounded log
tracked struct AppendEntriesGhostState<DT: Dispatch> {
    pub ghost idx               : nat,
    pub ghost old_tail          : nat,
    pub tracked log_entries     : Map<nat, UnboundedLog::log<DT>>,
    pub tracked local_updates   : Map<nat, UnboundedLog::local_updates<DT>>,
    pub tracked combiner        : UnboundedLog::combiner<DT>,
    pub tracked tail            : UnboundedLog::tail<DT>,
    pub ghost request_ids       : Seq<ReqId>,
    pub ghost operations        : Seq<<DT as Dispatch>::WriteOperation>
}

pub open spec fn wf(&self, nid: nat, ridx: nat, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& 0 <= self.idx <= self.request_ids.len()
        &&& ridx < self.request_ids.len()

        &&& self.tail@.value == self.old_tail + self.idx
        &&& self.tail@.instance == inst

        &&& self.combiner@.instance == inst
        &&& self.combiner@.key == nid
        &&& self.combiner@.value.is_Placed()
        &&& self.combiner@.value.get_Placed_queued_ops().len() == self.idx

        &&& (forall |i| 0 <= i < self.idx ==> #[trigger]self.request_ids[i] == self.combiner@.value.get_Placed_queued_ops()[i])

        // we added all the new entries
        &&& (forall |i| 0 <= i < self.idx <==> self.log_entries.contains_key(i))
        &&& (forall |i| 0 <= i < self.request_ids.len() ==> self.local_updates.contains_key(i))

        // processed entries
        &&& (forall |i| #![trigger self.local_updates[i]] 0 <= i < self.idx ==> {
            &&& self.local_updates[i]@.instance == inst
            &&& self.local_updates[i]@.key == self.request_ids[i as int]
            &&& self.local_updates[i]@.value.is_Placed()
            &&& self.local_updates[i]@.value.get_Placed_op() == self.operations[i as int]
        })

        // unprocessed entries
        &&& (forall |i| #![trigger self.local_updates[i]] self.idx <= i < self.request_ids.len() ==> {
            &&& self.local_updates[i]@.instance == inst
            &&& self.local_updates[i]@.key == self.request_ids[i as int]
            &&& self.local_updates[i]@.value.is_Init()
            &&& self.local_updates[i]@.value.get_Init_op() == self.operations[i as int]
        })

        // the log entries
        &&& (forall |i| #![trigger self.log_entries[i]] 0 <= i < self.idx ==> {
            &&& self.log_entries[i]@.instance == inst
            &&& self.log_entries[i]@.key == self.old_tail + i
            &&& self.log_entries[i]@.value.node_id == nid
            &&& self.log_entries[i]@.value.op == self.operations[i as int]
        })
    }
}
} // struct_with_invariants!

struct_with_invariants!{
/// represents the tokens that are created when a new log is being initialized
pub tracked struct NrLogTokens<DT: Dispatch> {
    pub ghost num_replicas: nat,
    pub tracked replicas                : Map<NodeId,UnboundedLog::replicas<DT>>,
    pub tracked combiners               : Map<NodeId,UnboundedLog::combiner<DT>>,
    pub tracked cb_combiners            : Map<NodeId, CyclicBuffer::combiner<DT>>,
    pub tracked unbounded_log_instance  : UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance  : CyclicBuffer::Instance<DT>,
}

pub open spec fn wf(&self, num_replicas: nat) -> bool {
    predicate {
        &&& self.num_replicas == num_replicas
        &&& self.unbounded_log_instance.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance.num_replicas() == self.num_replicas
        &&& (forall |i| #![trigger self.replicas[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.replicas.contains_key(i)
            &&& self.replicas[i]@.instance == self.unbounded_log_instance
            &&& self.replicas[i]@.key == i
            &&& self.replicas[i]@.value == DT::init_spec()
        })

        &&& (forall |i| #![trigger self.combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger]  self.combiners.contains_key(i)
            &&& self.combiners[i]@.instance == self.unbounded_log_instance
            &&& self.combiners[i]@.key == i
            &&& self.combiners[i]@.value.is_Ready()
        })

        &&& (forall |i| #![trigger self.cb_combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.cb_combiners.contains_key(i)
            &&& self.cb_combiners[i]@.instance == self.cyclic_buffer_instance
            &&& self.cb_combiners[i]@.key == i
            &&& self.cb_combiners[i]@.value.is_Idle()
        })
    }
}

} // struct_with_invariants!{


} // verus!

}

pub mod replica{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;


use vstd::{
    prelude::*,
    map::Map,
    cell::{PCell, PointsTo, CellId},
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
};

use crate::constants::{MAX_REPLICAS, MAX_REQUESTS, MAX_THREADS_PER_REPLICA, RESPONSE_CHECK_INTERVAL};

use crate::Dispatch;

// spec import
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::types::{
    ReqId, NodeId,
};
#[cfg(verus_keep_ghost)] use crate::{
    is_readonly_stub, is_readonly_ticket, is_update_stub, is_update_ticket
};

// exec imports
use crate::exec::rwlock::RwLock;
use crate::exec::CachePadded;
use crate::exec::log::{NrLog, NrLogAppendExecDataGhost};
use crate::exec::context::{Context, PendingOperation, ThreadId, ThreadToken, FCClientRequestResponseGhost};
#[cfg(verus_keep_ghost)] use crate::exec::utils::{rids_match, rids_match_pop, rids_match_add_rid, rids_match_add_none};

// use crate::exec::rwlock_unverified::RwLock as RwLockUnverified;

verus! {

#[verus::trusted] #[verifier(external_body)] /* vattr */
fn spin_loop_hint() {
    core::hint::spin_loop();
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replica Types
////////////////////////////////////////////////////////////////////////////////////////////////////


/// Unique identifier for the given replica (relative to the log)
pub type ReplicaId = usize;

/// a token that identifies the replica
///
// #[derive(Copy, Clone, Eq, PartialEq)]
pub struct ReplicaToken {
    pub /* REVIEW: (crate) */ rid: ReplicaId,
}

impl ReplicaToken {
    pub const fn new(rid: ReplicaId) -> (res: ReplicaToken)
        ensures res@ == rid
    {
        ReplicaToken { rid }
    }

    pub const fn clone(&self) -> (res: Self)
        ensures
            res == self
    {
        ReplicaToken { rid: self.rid }
    }

    pub open spec fn wf(&self, max_replicas: nat) -> bool {
        &&& self.rid < max_replicas
    }

    pub const fn id(&self) -> (result: ReplicaId)
        ensures result as nat == self.id_spec()
    {
        self.rid
    }

    pub open spec fn id_spec(&self) -> nat {
        self.rid as nat
    }

    pub open spec fn view(&self) -> nat {
        self.rid as nat
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replicated Data Structure
////////////////////////////////////////////////////////////////////////////////////////////////////

struct_with_invariants!{
/// Represents the data structure that is being replicated, protected by a RWLock
///
///  - Dafny: linear datatype NodeReplica = NodeReplica(
pub struct ReplicatedDataStructure<DT: Dispatch> {
    /// the actual data structure
    ///  - Dafny: linear actual_replica: nrifc.DataStructureType,
    pub data: DT,
    ///  - Dafny: glinear ghost_replica: Replica,
    pub replica: Tracked<UnboundedLog::replicas<DT>>,
    ///  - Dafny: glinear combiner: CombinerToken,
    pub combiner: Tracked<UnboundedLog::combiner<DT>>,
    ///  - Dafny: glinear cb: CBCombinerToken
    pub cb_combiner: Tracked<CyclicBuffer::combiner<DT>>
}

//  - Dafny: predicate WF(nodeId: nat, cb_loc_s: nat) {
pub open spec fn wf(&self, nid: NodeId, inst: UnboundedLog::Instance<DT>, cb: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.combiner@@.instance == inst
        &&& self.replica@@.instance == inst

        &&& self.replica@@.value == self.data.view()
        &&& self.replica@@.key == nid
        &&& self.combiner@@.value.is_Ready()
        &&& self.combiner@@.key == nid
        &&& self.cb_combiner@@.key == nid
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.cb_combiner@@.instance == cb
    }
}} // struct_with_invariants


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replica
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// An instance of a replicated data structure which uses a shared [`Log`] to
/// scale operations on the data structure across cores and processors.
///
///  - Dafny:   linear datatype Node
///  - Rust:    pub struct Replica<D>
#[repr(align(128))]
pub struct Replica<#[verifier::reject_recursive_types] DT: Dispatch> {
    /// An identifier that we got from the Log when the replica was registered
    /// against the shared-log ([`Log::register()`]). Required to pass to the
    /// log when consuming operations from the log.
    ///
    ///  - Dafny: nodeId: uint64,
    ///  - Rust:  log_tkn: LogToken,
    pub replica_token: ReplicaToken,

    /// Stores the index of the thread currently doing flat combining. Field is
    /// zero if there isn't any thread actively performing flat-combining.
    /// Atomic since this acts as the combiner lock.
    ///
    ///  - Dafny: linear combiner_lock: CachePadded<Atomic<uint64, glOption<CombinerLockState>>>,
    ///  - Rust:  combiner: CachePadded<AtomicUsize>,
    pub combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost<DT>>, _>>,

    /// List of per-thread contexts. Threads buffer write operations here when
    /// they cannot perform flat combining (because another thread might already
    /// be doing so).
    ///
    ///  - Dafny: linear contexts: lseq<Context>,
    ///  - Rust:  contexts: Vec<Context<<D as Dispatch>::WriteOperation, <D as Dispatch>::Response>>,
    pub contexts: Vec<Context<DT>>,

    /// A buffer of operations for flat combining.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    ///  - Rust:  buffer: RefCell<Vec<<D as Dispatch>::WriteOperation>>,
    pub collected_operations: PCell<Vec<<DT as Dispatch>::WriteOperation>>,

    /// Number of operations collected by the combiner from each thread at any
    /// we just have one inflight operation per thread
    /// inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,
    pub collected_operations_per_thread: PCell<Vec<usize>>,

    /// A buffer of results collected after flat combining. With the help of
    /// `inflight`, the combiner enqueues these results into the appropriate
    /// thread context.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    ///  - Rust:  result: RefCell<Vec<<D as Dispatch>::Response>>,
    pub responses: PCell<Vec<<DT as Dispatch>::Response>>,

    /// The underlying data structure. This is shared among all threads that are
    /// registered with this replica. Each replica maintains its own copy of
    /// `data`.
    ///
    ///   - Dafny: linear replica: RwLock,
    ///   - Rust:  data: CachePadded<RwLock<D>>,
    pub data: CachePadded<RwLock<ReplicatedDataStructure<DT>>>,
    // pub _data: CachePadded<RwLockUnverified<ReplicatedDataStructure<DT>>>,

    // Thread index that will be handed out to the next thread that registers
    // with the replica when calling [`Replica::register()`].
    pub num_threads: u64, //CachePadded<AtomicU64<_, Tracked<u64>, _>>,

    /// thread token that is handed out to the threads that register
    pub /* REVIEW: (crate) */ thread_tokens: Vec<ThreadToken<DT>>,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        &&& (forall |i: int| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i]).wf(i as nat))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).flat_combiner_instance == self.flat_combiner_instance)
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).unbounded_log_instance == self.unbounded_log_instance)

        &&& self.replica_token.rid < self.unbounded_log_instance@.num_replicas()

        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        &&& self.data.0.max_threads() == self.contexts.len()
        &&& 0 <= self.spec_id() < MAX_REPLICAS
        &&& self.data.0.wf()
        &&& (forall |v: ReplicatedDataStructure<DT>| (#[trigger] self.data.0.inv(v)) == v.wf(self.spec_id(), self.unbounded_log_instance@, self.cyclic_buffer_instance@))

        &&& self.flat_combiner_instance@.num_threads() == MAX_THREADS_PER_REPLICA
        &&& (forall |i| #![trigger self.thread_tokens[i]] 0 <= i < self.thread_tokens.len() ==> {
            self.thread_tokens[i].wf(self)
        })
    }

    invariant on combiner with (flat_combiner_instance, responses, collected_operations, collected_operations_per_thread) specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost<DT>>) {
        // v != 0 means lock is not taken, if it's not taken, the ghost state is Some
        &&& (v == 0) <==> g.is_some()
        //
        &&& (g.is_some() ==> g.get_Some_0().inv(flat_combiner_instance@, responses.id(), collected_operations.id(), collected_operations_per_thread.id()))
    }

    // invariant on num_threads with (flat_combiner_instance) specifically (self.num_threads.0)  is (v: u64, g: Tracked<u64>) {
    //     v == g@
    // }
}

} // struct_with_invariants!




impl<DT: Dispatch> Replica<DT> {
    pub fn new(replica_token: ReplicaToken, num_threads: usize, config: Tracked<ReplicaConfig<DT>>) -> (res: Self)
        requires
            num_threads == MAX_THREADS_PER_REPLICA,
            replica_token.id_spec() < MAX_REPLICAS,
            config@.wf(replica_token.id_spec())
        ensures
            res.wf(),
            res.spec_id() == replica_token.id_spec(),
            res.unbounded_log_instance@ == config@.unbounded_log_instance,
            res.cyclic_buffer_instance@ == config@.cyclic_buffer_instance,
    {
        let tracked ReplicaConfig {
            replica: replica,
            combiner: combiner,
            cb_combiner: cb_combiner,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = config.get();

        //
        // initialize the flat combiner
        //
        let tracked fc_instance:    FlatCombiner::Instance;
        let tracked mut fc_clients: Map<nat, FlatCombiner::clients>;
        let tracked mut fc_slots:   Map<nat, FlatCombiner::slots>;
        let tracked fc_combiner:    FlatCombiner::combiner;

        proof {
            let tracked (
                Tracked(fc_instance0), // FlatCombiner::Instance,
                Tracked(fc_clients0),  // Map<ThreadId, FlatCombiner::clients>,
                Tracked(fc_slots0),    // Map<ThreadId, FlatCombiner::slots>,
                Tracked(fc_combiner0), // FlatCombiner::combiner
            ) = FlatCombiner::Instance::initialize(num_threads as nat);
            fc_instance = fc_instance0;
            fc_clients = fc_clients0;
            fc_slots = fc_slots0;
            fc_combiner = fc_combiner0;
        }

        //
        // create the memory cells for the buffers
        //

        let (responses, responses_token) = PCell::new(Vec::with_capacity(num_threads));
        let (collected_operations, collected_operations_perm) = PCell::new(Vec::with_capacity(num_threads));
        let (collected_operations_per_thread, collected_operations_per_thread_perm) = PCell::new(Vec::with_capacity(num_threads));

        //
        // create the data structure protected by the RW lock
        //

        let replicated_data_structure = ReplicatedDataStructure {
            data: DT::init(),
            replica: Tracked(replica),
            combiner: Tracked(combiner),
            cb_combiner: Tracked(cb_combiner),
        };
        assert(replicated_data_structure.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance));
        // TODO: get the right spec function in there!
        let ghost data_structure_inv = |s: ReplicatedDataStructure<DT>| {
            s.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance)
        };
        let data = CachePadded(RwLock::new(MAX_THREADS_PER_REPLICA, replicated_data_structure, Ghost(data_structure_inv)));

        // let _replicated_data_structure = ReplicatedDataStructure {
            // data: DT::init(),
            // replica: Tracked(replica),
            // combiner: Tracked(combiner),
            // cb_combiner: Tracked(cb_combiner),
        // };
        // let _data = CachePadded(RwLockUnverified::new(_replicated_data_structure));

        //
        // Create the thread contexts
        //
        let mut contexts : Vec<Context<DT>> = Vec::with_capacity(num_threads);
        let mut thread_tokens : Vec<ThreadToken<DT>> = Vec::with_capacity(num_threads);

        let mut idx = 0;
        while idx < num_threads
            invariant
                num_threads <= MAX_THREADS_PER_REPLICA,
                replica_token.id_spec() < unbounded_log_instance.num_replicas(),
                contexts.len() == idx,
                thread_tokens.len() == idx,
                0 <= idx <= num_threads,
                forall |i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall |i: nat| #![trigger fc_slots[i]] idx <= i < num_threads ==> {
                    &&& fc_slots[i]@.value.is_Empty()
                    &&& fc_slots[i]@.key == i
                    &&& fc_slots[i]@.instance == fc_instance
                },
                forall |i: nat| idx <= i < num_threads ==> fc_clients.contains_key(i),
                forall |i: nat| #![trigger fc_clients[i]] idx <= i < num_threads ==> {
                    &&& fc_clients[i]@.instance == fc_instance
                    &&& fc_clients[i]@.key == i
                    &&& fc_clients[i]@.value.is_Idle()
                },
                forall |i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall |i| #![trigger contexts[i]] 0 <= i < contexts.len() ==> {
                    &&& contexts[i].wf(i as nat)
                    &&& contexts[i].flat_combiner_instance == fc_instance
                    &&& contexts[i].unbounded_log_instance == unbounded_log_instance
                },
                forall |i| #![trigger thread_tokens[i]] 0 <= i < thread_tokens.len() ==> {
                    &&& thread_tokens[i].wf2(unbounded_log_instance.num_replicas())
                    &&& thread_tokens[i].thread_id_spec() == i
                    &&& thread_tokens[i].rid@ == replica_token.id_spec()
                    &&& thread_tokens[i].fc_client@@.instance == fc_instance
                    &&& thread_tokens[i].batch_perm@@.pcell == contexts[i].batch.0.id()
                }
        {
            let tracked slot;
            let tracked client;
            proof {
                slot = fc_slots.tracked_remove(idx as nat);
                client = fc_clients.tracked_remove(idx as nat);
            }
            let fc_inst = Tracked(fc_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());

            let (context, batch_perm) = Context::new(idx, Tracked(slot), fc_inst, ul_inst);

            let token = ThreadToken {
                rid: replica_token.clone(),
                tid: idx as u32,
                fc_client: Tracked(client),
                batch_perm
            };

            // assert(token.wf2(unbounded_log_instance.num_replicas()));

            contexts.push(context);
            thread_tokens.push(token);

            idx = idx + 1;
        }

        let tracked context_ghost = CombinerLockStateGhost {
            flat_combiner: Tracked(fc_combiner),
            collected_operations_perm,
            collected_operations_per_thread_perm,
            responses_token,
        };

        let tracked fc_inst = fc_instance.clone();
        let combiner = CachePadded(AtomicU64::new(Ghost((Tracked(fc_inst), responses, collected_operations, collected_operations_per_thread)), 0, Tracked(Option::Some(context_ghost))));
        let num_threads = 0; //AtomicU64::new(Ghost(()), 0, Tracked(0));
        //
        // Assemble the data struture
        //

        Replica {
            replica_token,
            combiner,
            contexts,
            collected_operations,
            collected_operations_per_thread,
            responses,
            data,
            // _data,
            thread_tokens,
            num_threads,
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
            flat_combiner_instance: Tracked(fc_instance),
        }
    }

    pub fn id(&self) -> (res: ReplicaId)
        ensures res as nat == self.spec_id()
    {
        self.replica_token.id()
    }

    /// returns the replica id for this replica
    pub open spec fn spec_id(&self) -> NodeId {
        self.replica_token.id_spec()
    }

    /// Try to become acquire the combiner lock here. If this fails, then return None.
    ///
    ///  - Dafny: part of method try_combine
    #[inline(always)]
    fn acquire_combiner_lock(&self) -> (result: (bool, Tracked<Option<CombinerLockStateGhost<DT>>>))
        requires self.wf()
        ensures
          result.0 ==> result.1@.is_some(),
          result.0 ==> result.1@.get_Some_0().inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
    {
        // OPT: try to check whether the lock is already present
        // for _ in 0..4 {
        //     if self.combiner.load(Ordering::Relaxed) != 0 { return None; }
        // }
        let res = atomic_with_ghost!(
                // upstream is compare_exchange_weak
                &self.combiner.0 => load();
                ghost g => { }
            );
        if res != 0 {
            return  (false, Tracked(Option::None));
        }

        // XXX: we should pass in the replica token here, just setting the tid to 1 should work
        //      as the lock is basically a spinlock anyway
        let tid = 1u64;

        // Step 1: perform cmpxchg to acquire the combiner lock
        // if self.combiner.compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Acquire) != Ok(0) {
        //     None
        // } else {
        //     Some(CombinerLock { replica: self })
        // }

        let tracked lock_g: Option<CombinerLockStateGhost<DT>>;
        let res = atomic_with_ghost!(
            // upstream is compare_exchange_weak
            &self.combiner.0 => compare_exchange(0, tid + 1);
            update prev->next;
            ghost g => {
                if prev == 0 {
                    lock_g = g;    // obtain the protected lock state
                    g = Option::None;       // we took the lock, set the ghost state to None,
                } else {
                    lock_g = Option::None; // the lock was already taken, set it to None
                }
            }
        );

        if let Result::Ok(val) = res {
            (val == 0, Tracked(lock_g))
        } else {
            (false, Tracked(Option::None))
        }
    }

    #[inline(always)]
    fn release_combiner_lock(&self, lock_state: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            lock_state@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                g = Option::Some(lock_state.get());
            });
    }

    /// Appends an operation to the log and attempts to perform flat combining.
    /// Accepts a thread `tid` as an argument. Required to acquire the combiner lock.
    fn try_combine(&self, slog: &NrLog<DT>)
        requires
          self.wf(),
          slog.wf(),
          self.unbounded_log_instance@ == slog.unbounded_log_instance@,
          slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
    {
        // Step 1: try to take the combiner lock to become combiner
        let (acquired, combiner_lock) = self.acquire_combiner_lock();

        // Step 2: if we are the combiner then perform flat combining, else return
        if acquired {
            assert(combiner_lock@.is_some());
            let combiner_lock = Tracked(combiner_lock.get().tracked_unwrap());
            let combiner_lock = self.combine(slog, combiner_lock);
            self.release_combiner_lock(combiner_lock);
        } else {
            // nothing to be done here.
        }
    }

    /// Performs one round of flat combining. Collects, appends and executes operations.
    fn combine(&self, slog: &NrLog<DT>, combiner_lock: Tracked<CombinerLockStateGhost<DT>>)
            -> (result: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            combiner_lock@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
        ensures
            result@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),

    {
        // disassemble the combiner lock
        let tracked combiner_lock = combiner_lock.get();
        let flat_combiner = Tracked(combiner_lock.flat_combiner.get());
        let tracked mut collected_operations_perm = combiner_lock.collected_operations_perm.get();
        let tracked mut collected_operations_per_thread_perm = combiner_lock.collected_operations_per_thread_perm.get();
        let tracked mut responses_token = combiner_lock.responses_token.get();

        // obtain access to the responses, operations and num_ops_per_thread buffers
        let mut responses = self.responses.take(Tracked(&mut responses_token));

        let mut operations = self.collected_operations.take(Tracked(&mut collected_operations_perm));

        // assert(self.collected_operations_per_thread.id() == collected_operations_per_thread_perm@.pcell);
        let mut num_ops_per_thread = self.collected_operations_per_thread.take(Tracked(&mut collected_operations_per_thread_perm));

        // Step 1: collect the operations from the threads
        // self.collect_thread_ops(&mut buffer, operations.as_mut_slice());
        let Tracked(collect_res) = self.collect_thread_ops(&mut operations, &mut num_ops_per_thread, flat_combiner);
        let tracked ThreadOpsData { flat_combiner, local_updates, request_ids, cell_permissions } = collect_res;

        // Step 2: Take the R/W lock on the data structure
        let (replicated_data_structure, write_handle) = self.data.0.acquire_write();
        let mut data = replicated_data_structure.data;
        let ghost_replica = replicated_data_structure.replica;
        let combiner = replicated_data_structure.combiner;
        let cb_combiner = replicated_data_structure.cb_combiner;

        // let mut replicated_data_structure = self._data.0.write(MAX_THREADS_PER_REPLICA);
        // let data = &mut replicated_data_structure.data;

        // Step 3: Append all operations to the log
        let tracked append_exec_ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids};
        let append_exec_ghost_data = slog.append(&self.replica_token, &operations, &mut responses, &mut data, Tracked(append_exec_ghost_data));

        // TODO: release lock here! upstream does release the lock here and the reacquire it!

        // drop(replicated_data_structure);


        // Step 3: Execute all operations
        let append_exec_ghost_data = slog.execute(&self.replica_token, &mut responses, &mut data, append_exec_ghost_data);
        let Tracked(append_exec_ghost_data) = append_exec_ghost_data;
        let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids } = append_exec_ghost_data;
        let tracked ghost_replica = ghost_replica.get();
        let tracked combiner = combiner.get();
        let tracked cb_combiner = cb_combiner.get();

        // Step 4: release the R/W lock on the data structure
        let replicated_data_structure = ReplicatedDataStructure  { data, replica: Tracked(ghost_replica), combiner: Tracked(combiner), cb_combiner: Tracked(cb_combiner) };
        self.data.0.release_write(replicated_data_structure, write_handle);

        // Step 5: collect the results
        let tracked thread_ops_data = ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions };
        let distribute_thread_resps_result = self.distribute_thread_resps(&mut responses, &mut num_ops_per_thread, Tracked(thread_ops_data));
        let tracked ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions } = distribute_thread_resps_result.get();

        // clear the buffers again
        responses.clear();
        operations.clear();
        num_ops_per_thread.clear();

        // // place the responses back into the state
        self.responses.put(Tracked(&mut responses_token), responses);
        self.collected_operations.put(Tracked(&mut collected_operations_perm), operations);
        self.collected_operations_per_thread.put(Tracked(&mut collected_operations_per_thread_perm), num_ops_per_thread);

        // re-assemble the combiner lock
        let tracked combiner_lock =  CombinerLockStateGhost { flat_combiner, collected_operations_perm: Tracked(collected_operations_perm), collected_operations_per_thread_perm: Tracked(collected_operations_per_thread_perm), responses_token: Tracked(responses_token) };
        Tracked(combiner_lock)
    }

    ///
    /// - Dafny: combine_collect()
    #[inline(always)]
    fn collect_thread_ops(&self, operations: &mut Vec<DT::WriteOperation>, num_ops_per_thread: &mut Vec<usize>,
                          flat_combiner:  Tracked<FlatCombiner::combiner>)
                             -> (response: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            old(num_ops_per_thread).len() == 0,
            old(operations).len() == 0,
            flat_combiner@@.instance == self.flat_combiner_instance@,
            flat_combiner@@.value.is_Collecting(),
            flat_combiner@@.value.get_Collecting_0().len() == 0,
        ensures
            operations.len() <= MAX_REQUESTS,
            response@.collect_thread_ops_post(self.flat_combiner_instance, self.unbounded_log_instance@, num_ops_per_thread@, operations@, self.contexts@)
    {
        let mut flat_combiner = flat_combiner;

        let tracked mut updates: Map<nat, UnboundedLog::local_updates<DT>> = Map::tracked_empty();
        let tracked mut cell_permissions: Map<nat, PointsTo<PendingOperation<DT>>> = Map::tracked_empty();
        let ghost mut request_ids = Seq::empty();

        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        let num_registered_threads = MAX_THREADS_PER_REPLICA;

        // Collect operations from each thread registered with this replica.
        // for i in 1..num_registered_threads {
        let mut thread_idx = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                self.wf(),
                operations.len() <= thread_idx,
                operations.len() == request_ids.len(),
                num_ops_per_thread.len() == thread_idx,
                self.contexts.len() == num_registered_threads,
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner@@.value.is_Collecting(),
                flat_combiner@@.value.get_Collecting_0().len() == thread_idx,
                flat_combiner@@.instance == self.flat_combiner_instance@,
                forall |i: nat| i < flat_combiner@@.value.get_Collecting_0().len() ==>
                    (num_ops_per_thread[i as int] > 0) ==
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_some(),
                forall |i: nat| i < flat_combiner@@.value.get_Collecting_0().len() &&
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_some()
                    },
                forall |i| 0 <= i < request_ids.len() <==> updates.contains_key(i),
                forall|i: nat| #![trigger updates[i]] i < request_ids.len() ==> {
                    &&& #[trigger] updates.contains_key(i)
                    &&& updates[i]@.instance == self.unbounded_log_instance
                    &&& updates[i]@.key == request_ids[i as int]
                    &&& updates[i]@.value.is_Init()
                    &&& updates[i]@.value.get_Init_op() == operations[i as int]
                },
                rids_match(flat_combiner@@.value.get_Collecting_0(), request_ids,
                    0, flat_combiner@@.value.get_Collecting_0().len(), 0, request_ids.len())

        {

            let tracked update_req : std::option::Option<UnboundedLog::local_updates<DT>>;
            let tracked batch_perms : std::option::Option<PointsTo<PendingOperation<DT>>>;
            let num_ops = atomic_with_ghost!(
                &self.contexts[thread_idx].atomic.0 => load();
                returning num_ops;
                ghost g // g : ContextGhost
            => {
                if num_ops == 1 {
                    self.flat_combiner_instance.borrow().pre_combiner_collect_request(&g.slots, flat_combiner.borrow());

                    rids_match_add_rid(flat_combiner.view().view().value.get_Collecting_0(), request_ids,
                        0, flat_combiner.view().view().value.get_Collecting_0().len(), 0, request_ids.len(),g.update.get_Some_0().view().key);

                    update_req = g.update;
                    batch_perms = g.batch_perms;

                    g.slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.slots, flat_combiner.borrow_mut());
                    g.update = None;
                    g.batch_perms = None;
                } else {
                    rids_match_add_none(flat_combiner.view().view().value.get_Collecting_0(), request_ids,
                        0, flat_combiner.view().view().value.get_Collecting_0().len(), 0, request_ids.len());

                    self.flat_combiner_instance.borrow().combiner_collect_empty(&g.slots, flat_combiner.borrow_mut());
                    update_req = None;
                    batch_perms = None;
                }
            });

            if num_ops == 1 {
                let tracked batch_token_value = batch_perms.tracked_unwrap();
                let op = DT::clone_write_op(&self.contexts[thread_idx].batch.0.borrow(Tracked(&batch_token_value)).op);

                let tracked update_req = update_req.tracked_unwrap();
                proof {
                    updates.tracked_insert(request_ids.len() as nat, update_req);
                    cell_permissions.tracked_insert(thread_idx as nat, batch_token_value);
                }

                proof {
                    request_ids = request_ids.push(update_req@.key);
                }
                operations.push(op);
            }

            // set the number of active operations per thread
            num_ops_per_thread.push(num_ops as usize);
            thread_idx = thread_idx + 1;
        }

        proof {
            self.flat_combiner_instance.borrow().combiner_responding_start(flat_combiner.borrow_mut());
        }

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner,
            request_ids: Ghost(request_ids),
            local_updates: Tracked(updates),
            cell_permissions: Tracked(cell_permissions)
        };
        Tracked(thread_ops_data)
    }


    /// - Dafny: combine_respond
    fn distribute_thread_resps(&self, responses: &mut Vec<DT::Response>, num_ops_per_thread: &mut Vec<usize>, thread_ops_data: Tracked<ThreadOpsData<DT>>)
        -> (res: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            thread_ops_data@.distribute_thread_resps_pre(self.flat_combiner_instance, self.unbounded_log_instance@, old(num_ops_per_thread)@, old(responses)@, self.contexts@),
            rids_match(thread_ops_data@.flat_combiner@@.value.get_Responding_0(), thread_ops_data@.request_ids@,
                0, thread_ops_data@.flat_combiner@@.value.get_Responding_0().len(), 0, thread_ops_data@.request_ids@.len())
        ensures
            res@.distribute_thread_resps_post(self.flat_combiner_instance)

    {
        let tracked ThreadOpsData {
            flat_combiner: flat_combiner,
            request_ids: request_ids,
            local_updates: local_updates,
            cell_permissions: cell_permissions,
        } = thread_ops_data.get();
        let tracked mut flat_combiner = flat_combiner.get();
        let tracked mut cell_permissions = cell_permissions.get();
        let tracked mut updates = local_updates.get();


        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        let num_registered_threads = MAX_THREADS_PER_REPLICA;

        // let (mut s, mut f) = (0, 0);
        // for i in 1..num_registered_threads {
        let mut thread_idx = 0;
        let mut resp_idx : usize = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                0 <= resp_idx <= responses.len(),
                resp_idx <= thread_idx,
                num_ops_per_thread.len() == num_registered_threads,
                request_ids@.len() == responses.len(),
                num_registered_threads == MAX_THREADS_PER_REPLICA,
                self.wf(),
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner@.instance == self.flat_combiner_instance@,
                flat_combiner@.value.is_Responding(),
                flat_combiner@.value.get_Responding_1() == thread_idx,
                flat_combiner@.value.get_Responding_0().len() == MAX_THREADS_PER_REPLICA,
                forall |i: nat| i < flat_combiner@.value.get_Responding_0().len() ==>
                    (num_ops_per_thread[i as int] > 0) ==
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_some(),
                forall |i: nat| thread_idx <= i < flat_combiner@.value.get_Responding_0().len() &&
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_some()
                    },
                forall|i: nat| resp_idx <= i < request_ids@.len() ==> {
                        &&& updates.contains_key(i)
                },
                forall|i: nat| #![trigger updates[i]] resp_idx <= i < request_ids@.len() ==> {
                    &&& updates.contains_key(i)
                    &&& updates[i]@.key == request_ids@[i as int]
                    &&& updates[i]@.value.is_Done()
                    &&& updates[i]@.instance == self.unbounded_log_instance@
                    &&& updates[i]@.value.get_Done_ret() == responses[i as int]
                },
                rids_match(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len()),

        {

            proof {
                rids_match_pop(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len());
            }

            let num_ops = num_ops_per_thread[thread_idx];

            // assert(flat_combiner@.value.get_Responding_1() < num_registered_threads);

            if num_ops == 0 {
                // if operations[i - 1] == 0 {
                //     continue;
                // };
                proof {
                    self.flat_combiner_instance.borrow().combiner_responding_empty(&mut flat_combiner);
                }

                // assert(forall|i: nat| #![trigger updates[i]] resp_idx <= i < request_ids@.len() ==> {
                //     &&& updates.contains_key(i)
                // });

            } else {
                //     f += operations[i - 1];
                //     self.contexts[i - 1].enqueue_resps(&results[s..f]);
                //     s += operations[i - 1];

                // obtain the element from the operation batch
                let tracked mut permission = cell_permissions.tracked_remove(thread_idx as nat);
                let mut op_resp = self.contexts[thread_idx].batch.0.take(Tracked(&mut permission));

                // update with the response
                let resp: DT::Response = DT::clone_response(&responses[resp_idx]);
                op_resp.resp = Some(resp);

                // place the element back into the batch
                self.contexts[thread_idx].batch.0.put(Tracked(&mut permission), op_resp);

                //     operations[i - 1] = 0;
                atomic_with_ghost!(
                    &self.contexts[thread_idx].atomic.0 => store(0);
                    update prev -> next;
                    ghost g // g : ContextGhost
                    => {
                        // record the pre-states of the transition values
                        g.slots = self.flat_combiner_instance.borrow().combiner_responding_result(g.slots, &mut flat_combiner);
                        g.batch_perms = Some(permission);
                        g.update = Some(updates.tracked_remove(resp_idx as nat));
                    }
                );
                resp_idx = resp_idx + 1;
            }
            thread_idx = thread_idx + 1;
        }

        proof {
            self.flat_combiner_instance.borrow().combiner_responding_done(&mut flat_combiner);
        }

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner: Tracked(flat_combiner),
            request_ids,
            local_updates: Tracked(updates),
            cell_permissions : Tracked(cell_permissions),
        };

        Tracked(thread_ops_data)
    }

    /// Registers a thread with this replica. Returns a [`ReplicaToken`] if the
    /// registration was successfull. None if the registration failed.
    pub fn register(&mut self) -> (res: Option<ThreadToken<DT>>)
        requires old(self).wf()
        ensures self.wf(),
        old(self).replica_token@ == self.replica_token@,
        old(self).unbounded_log_instance@ == self.unbounded_log_instance@,
        old(self).cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
        res.is_Some() ==> res.get_Some_0().wf(self)
    {
        self.thread_tokens.pop()
    }

    #[verifier(external_body)] /* vattr */
    pub fn progress(line: u32) {
        println!("Replica:: progress {line}");
    }

    /// Executes an immutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute(&self, slog: &NrLog<DT>, op: DT::ReadOperation, tkn: ThreadToken<DT>, ticket: Tracked<UnboundedLog::local_reads<DT>>)
        -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            slog.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token@ == tkn.replica_token()@,
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_readonly_ticket(ticket@, op, slog.unbounded_log_instance@)
        ensures
            result.1.wf(&self),
            result.1.batch_perm@@.pcell == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_readonly_stub(result.2@, ticket@@.key, result.0, slog.unbounded_log_instance@)
    {
        // let tracked local_reads : UnboundedLog::local_reads<DT>;
        // proof {
        //     let tracked ticket = self.unbounded_log_instance.borrow().readonly_start(op);
        //     local_reads = ticket.1.get();
        // }
        let ghost rid : nat = ticket@@.key;
        proof {
            rid = ticket@@.key;
        }
        let ghost nid = tkn.replica_id_spec();

        // Step 1: Read the local tail value
        // let ctail = slog.get_ctail();
        let (version_upper_bound, ticket) = slog.get_version_upper_bound(ticket);

        // Step 2: wait until the replica is synced for reads, try to combine in mean time
        // while !slog.is_replica_synced_for_reads(&self.log_tkn, ctail) {
        //     if let Err(e) = self.try_combine(slog) {
        //         return Err((e, op));
        //     }
        //     spin_loop();
        // }
        let (mut is_synced, mut ticket) = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, ticket);
        while !is_synced
            invariant
                self.wf(),
                slog.wf(),
                !is_synced ==> ticket@@.value.is_VersionUpperBound(),
                !is_synced ==> ticket@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound,
                !is_synced ==> ticket@@.value.get_VersionUpperBound_op() == op,
                is_synced ==> ticket@@.value.is_ReadyToRead(),
                is_synced ==> ticket@@.value.get_ReadyToRead_node_id() == self.spec_id(),
                is_synced ==> ticket@@.value.get_ReadyToRead_op() == op,
                ticket@@.instance == self.unbounded_log_instance@,
                ticket@@.key == rid,
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
        {
            self.try_combine(slog);
            spin_loop_hint();
            let res = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, ticket);
            is_synced = res.0;
            ticket = res.1;
        }

        let tracked ticket = ticket.get();

        // Step 3: Take the read-only lock, and read the value
        // let res = self.data.read(idx.tid() - 1).dispatch(op)
        assert(tkn.thread_id_spec() < self.data.0.max_threads());

        // let result = self._data.0.read(tkn.thread_id() as usize).data.dispatch(op);
        let read_handle = self.data.0.acquire_read(tkn.thread_id() as usize);
        let replica = self.data.0.borrow(Tracked(&read_handle));
        let result = replica.data.dispatch(op);
        // assert(replica.wf(self.spec_id(), self.unbounded_log_instance@, self.cyclic_buffer_instance@));
        // assert(replica.replica@.view().instance == self.unbounded_log_instance);
        // assert(replica.replica@.view().key == rid);

        let tracked ticket = self.unbounded_log_instance.borrow().readonly_apply(rid, replica.replica.borrow(), ticket, replica.combiner.borrow());
        self.data.0.release_read(read_handle);

        // // Step 4: Finish the read-only transaction, return result
        // let tracked local_reads = local_reads;
        // proof {
        //     self.unbounded_log_instance.borrow().readonly_finish(rid, op, result, local_reads);
        // }

        // assert(false);
        (result, tkn, Tracked(ticket))
    }

    /// Executes a mutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute_mut(&self, slog: &NrLog<DT>, op: DT::WriteOperation, tkn: ThreadToken<DT>, ticket: Tracked<UnboundedLog::local_updates<DT>>)
            -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>))
        requires
            slog.wf(),
            self.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token == tkn.replica_token(),
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_update_ticket(ticket@, op, slog.unbounded_log_instance@)
        ensures
            result.1.wf(self),
            result.1.batch_perm@@.pcell == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_update_stub(result.2@, ticket@@.key, result.0, slog.unbounded_log_instance@)
    {

        let tracked ticket = ticket.get();

        let ghost req_id : nat = ticket@.key;

        let ThreadToken { rid, tid, fc_client, batch_perm } = tkn;

        // Step 1: Enqueue the operation onto the thread local batch
        // while !self.make_pending(op.clone(), idx.tid()) {}
        // Note: if we have the thread token, this will always succeed.
        let tracked context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perm.get()), cell_id: Ghost(self.contexts[tkn.thread_id_spec() as int].batch.0.id()), local_updates: Some(ticket), fc_clients: fc_client.get() };

        let mk_pending_res = self.make_pending(op, tid, Tracked(context_ghost));
        let context_ghost = mk_pending_res.1;

        // Step 2: Try to do flat combining to appy the update to the data structure
        self.try_combine(slog);

        // Step 3: Obtain the result form the responses
        let response = self.get_response(slog, tid, Ghost(req_id), context_ghost);
        let context_ghost = response.1;

        let tracked FCClientRequestResponseGhost { batch_perms: batch_perms, cell_id, local_updates: ticket, fc_clients: fc_clients } = context_ghost.get();
        let tracked ticket = ticket.tracked_unwrap();


        let tracked batch_perm = batch_perms.tracked_unwrap();

        (
            response.0,
            ThreadToken { rid, tid, fc_client: Tracked(fc_clients), batch_perm: Tracked(batch_perm) },
            Tracked(ticket)
        )
    }

    /// Enqueues an operation inside a thread local context. Returns a boolean
    /// indicating whether the operation was enqueued (true) or not (false).
    #[inline(always)]
    fn make_pending(&self, op: DT::WriteOperation, tid: ThreadId, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
     -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            0 <= tid < self.contexts.len(),
            context_ghost@.enqueue_op_pre(tid as nat, op, self.contexts[tid as int].batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@)
        ensures
            res.1@.enqueue_op_post(context_ghost@)
    {
        let context = &self.contexts[tid as usize];
        context.enqueue_op(op, context_ghost)
    }

    /// Busy waits until a response is available within the thread's context.
    fn get_response(&self, slog: &NrLog<DT>, tid: ThreadId, req_id: Ghost<ReqId>, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (DT::Response, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            0 <= tid < self.contexts.len(),
            context_ghost@.dequeue_resp_pre(self.contexts[tid as int].batch.0.id(), tid as nat, self.flat_combiner_instance@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, Some(res.0), self.unbounded_log_instance@),
    {
        let mut context_ghost_new = context_ghost;
        let context = &self.contexts[tid as usize];

        let mut iter : usize = 0;
        let mut r = None;
        while r.is_none()
            invariant
                slog.wf(),
                self.wf(),
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
                context.wf(tid as nat),
                context.flat_combiner_instance@ == self.flat_combiner_instance@,
                context.unbounded_log_instance@ == self.unbounded_log_instance@,
                0 <= iter <= RESPONSE_CHECK_INTERVAL,
                r.is_None() ==> context_ghost_new@.dequeue_resp_pre(context.batch.0.id(), tid as nat, self.flat_combiner_instance@),
                context_ghost_new@.dequeue_resp_post(context_ghost@, r, self.unbounded_log_instance@)
        {
            if iter == RESPONSE_CHECK_INTERVAL {
                self.try_combine(slog);
                iter = 0;
            }

            let deq_resp_result = context.dequeue_response(context_ghost_new);
            r = deq_resp_result.0;
            context_ghost_new = deq_resp_result.1;

            iter = iter + 1;
        }

        let r = r.unwrap();
        (r, context_ghost_new)
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost Structures
////////////////////////////////////////////////////////////////////////////////////////////////////

/// struct containing arguments for creating a new replica
pub tracked struct ReplicaConfig<DT: Dispatch> {
    pub tracked replica: UnboundedLog::replicas<DT>,
    pub tracked combiner: UnboundedLog::combiner<DT>,
    pub tracked cb_combiner: CyclicBuffer::combiner<DT>,
    pub tracked unbounded_log_instance: UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance: CyclicBuffer::Instance<DT>,
}

impl<DT: Dispatch> ReplicaConfig<DT> {
    pub open spec fn wf(&self, nid: nat) -> bool {
        &&& self.combiner@.instance == self.unbounded_log_instance
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance
        &&& self.cyclic_buffer_instance.unbounded_log_instance() == self.unbounded_log_instance
        &&& self.unbounded_log_instance.num_replicas() == self.cyclic_buffer_instance.num_replicas()
        &&& nid < self.unbounded_log_instance.num_replicas()

        &&& self.replica@.value == DT::init_spec()
        &&& self.replica@.key == nid
        &&& self.replica@.instance == self.unbounded_log_instance
        &&& self.combiner@.value.is_Ready()
        &&& self.combiner@.key == nid
        &&& self.cb_combiner@.key == nid
        &&& self.cb_combiner@.value.is_Idle()
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance
    }
}


struct_with_invariants!{
/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub tracked struct CombinerLockStateGhost<DT: Dispatch> {
    // glinear flatCombiner: FCCombiner,
    pub flat_combiner: Tracked<FlatCombiner::combiner>,

    /// Stores the token to access the collected_operations in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    pub collected_operations_perm: Tracked<PointsTo<Vec<<DT as Dispatch>::WriteOperation>>>,

    /// Stores the token to access the number of collected operations in the replica
    pub collected_operations_per_thread_perm: Tracked<PointsTo<Vec<usize>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    pub responses_token: Tracked<PointsTo<Vec<<DT as Dispatch>::Response>>>,
}

//  - Dafny: predicate CombinerLockInv(v: uint64, g: glOption<CombinerLockState>, fc_loc: nat,
//                                     ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
//                                     responses: LC.LinearCell<seq<nrifc.ReturnType>>)
//
// Note: this predicate only holds when the lock is not taken.
pub open spec fn inv(&self, combiner_instance: FlatCombiner::Instance, responses_id: CellId, op_buffer_id: CellId, thread_ops: CellId) -> bool {
    predicate {
        &&& self.flat_combiner@@.value.is_Collecting()
        &&& self.flat_combiner@@.value.get_Collecting_0().len() == 0
        &&& self.flat_combiner@@.instance == combiner_instance

        &&& self.collected_operations_perm@@.value.is_some()
        &&& self.collected_operations_perm@@.pcell == op_buffer_id
        &&& self.collected_operations_perm@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        &&& self.responses_token@@.value.is_some()
        &&& self.responses_token@@.pcell == responses_id
        &&& self.responses_token@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        &&& self.collected_operations_per_thread_perm@@.value.is_some()
        &&& self.collected_operations_per_thread_perm@@.pcell == thread_ops
        &&& self.collected_operations_per_thread_perm@@.value.get_Some_0().len() == 0
    }
}} // struct_with_invariants!



tracked struct ThreadOpsData<DT: Dispatch> {
    flat_combiner: Tracked<FlatCombiner::combiner>,
    request_ids: Ghost<Seq<ReqId>>,
    local_updates: Tracked<Map<nat, UnboundedLog::local_updates<DT>>>,
    cell_permissions: Tracked<Map<nat, PointsTo<PendingOperation<DT>>>>,
}

impl<DT: Dispatch> ThreadOpsData<DT> {
    spec fn shared_inv(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>, num_ops_per_thread: Seq<usize>,
                       replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.flat_combiner@@.instance == flat_combiner_instance@
        &&& self.flat_combiner@@.value.is_Responding()
        &&& self.flat_combiner@@.value.get_Responding_0().len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& num_ops_per_thread.len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& self.flat_combiner@@.value.get_Responding_1() == 0

        &&& (forall|i: nat|
           #![trigger num_ops_per_thread[i as int]]
           #![trigger self.flat_combiner@@.value.get_Responding_0()[i as int]]
            i < self.flat_combiner@@.value.get_Responding_0().len() ==> {
            &&& (num_ops_per_thread[i as int] > 0) == self.flat_combiner@@.value.get_Responding_0()[i as int].is_some()
            &&& self.flat_combiner@@.value.get_Responding_0()[i as int].is_some() ==> {
                &&& self.cell_permissions@.contains_key(i)
                &&& self.cell_permissions@[i]@.pcell === replica_contexts[i as int].batch.0.id()
                &&& self.cell_permissions@[i]@.value.is_some()
            }
        })

    }

    spec fn distribute_thread_resps_pre(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>,
                                        unbounded_log_instance: UnboundedLog::Instance<DT>,
                                        num_ops_per_thread: Seq<usize>, responses: Seq<DT::Response>,
                                        replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)

        &&& self.request_ids@.len() == responses.len()
        &&& (forall |i| 0 <= i < self.request_ids@.len() ==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat| #![trigger self.local_updates@[i]] i < self.request_ids@.len() ==> {
            &&& self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.instance == unbounded_log_instance
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Done()
            &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
        })

        &&& rids_match(self.flat_combiner@@.value.get_Responding_0(), self.request_ids@,
                 0, self.flat_combiner@@.value.get_Responding_0().len(), 0, self.request_ids@.len())
    }

    spec fn distribute_thread_resps_post(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>) -> bool
    {
        &&& self.flat_combiner@@.instance == flat_combiner_instance@
        &&& self.flat_combiner@@.value.is_Collecting()
        &&& self.flat_combiner@@.value.get_Collecting_0().len() == 0
    }

    spec fn collect_thread_ops_post(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>,
                unbounded_log_instance: UnboundedLog::Instance<DT>, num_ops_per_thread: Seq<usize>,
                operations: Seq<DT::WriteOperation>, replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)
        &&& self.request_ids@.len() == operations.len()
        &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat| #![trigger self.local_updates@[i]] i < self.request_ids@.len() ==> {
            &&& #[trigger] self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.instance == unbounded_log_instance
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Init()
            &&& self.local_updates@[i]@.value.get_Init_op() == operations[i as int]
        })

        &&& rids_match(self.flat_combiner@@.value.get_Responding_0(), self.request_ids@,
                 0, self.flat_combiner@@.value.get_Responding_0().len(), 0, self.request_ids@.len())
    }
}

} // verus!

}

pub mod context{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    prelude::*,
    cell::{PCell, PointsTo, CellId},
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
};

use crate::Dispatch;

// constants
use crate::constants::{MAX_THREADS_PER_REPLICA};

// spec import
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::flat_combiner::FlatCombiner;

// exec imports
use crate::exec::CachePadded;
use crate::exec::Replica;
use crate::exec::replica::{ReplicaToken, ReplicaId};

verus! {


////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Token
////////////////////////////////////////////////////////////////////////////////////////////////////


/// A (monotoically increasing) number that uniquely identifies a thread that's
/// registered with the replica.
pub type ThreadId = u32;


/// the thread token identifies a thread of a given replica
///
///  - Dafny: linear datatype ThreadOwnedContext
pub struct ThreadToken<DT: Dispatch> {
    /// the replica id this thread uses
    pub /* REVIEW: (crate) */ rid: ReplicaToken,
    /// identifies the thread within the replica
    pub /* REVIEW: (crate) */ tid: ThreadId,
    /// the flat combiner client of the thread
    pub fc_client: Tracked<FlatCombiner::clients>,
    /// the permission to access the thread's operation batch
    pub batch_perm: Tracked<PointsTo<PendingOperation<DT>>>,
}

impl<DT: Dispatch> ThreadToken<DT> {
    pub open spec fn wf2(&self, num_replicas: nat) -> bool
    {
        &&& self.rid.wf(num_replicas)
        &&& self.fc_client@@.value.is_Idle()
        &&& (self.tid as nat) < MAX_THREADS_PER_REPLICA
        // &&& self.fc_client@@.instance == fc_inst
        &&& self.batch_perm@@.value.is_None()
        &&& self.fc_client@@.key == self.tid as nat
    }

    pub open spec fn wf(&self,  replica: &Replica<DT>) -> bool {
        &&& self.wf2(replica.spec_id() + 1) // +1 here because ids got < replicas
        &&& self.rid@ == replica.spec_id()
        &&& self.fc_client@@.instance == replica.flat_combiner_instance
        &&& self.batch_perm@@.pcell == replica.contexts[self.thread_id_spec() as int].batch.0.id()
    }

    pub fn thread_id(&self) -> (result: ThreadId)
        ensures result as nat == self.thread_id_spec()
    {
        self.tid
    }

    pub open spec fn thread_id_spec(&self) -> nat {
        self.tid as nat
    }

    pub const fn replica_id(&self) -> (result: ReplicaId)
        ensures result as nat == self.replica_id_spec()
    {
        self.rid.id()
    }

    pub open spec fn replica_token(&self) -> ReplicaToken {
        self.rid
    }

    pub open spec fn replica_id_spec(&self) -> nat {
        self.rid.id_spec()
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Pending Operation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Data for a pending operation.
///
///  - Dafny: datatype OpResponse
///  - Rust:  pub struct PendingOperation<T, R, M> {
///
/// In Dafny those data types are not options, but in Rust they are
pub struct PendingOperation<DT: Dispatch> {
    /// the operation that is being executed
    pub/*REVIEW: (crate)*/ op: DT::WriteOperation,
    /// the response of the operation
    pub/*REVIEW: (crate)*/ resp: Option<DT::Response>,
}

impl<DT: Dispatch> PendingOperation<DT> {
    pub fn new(op: DT::WriteOperation) -> (res: Self)
        ensures res.op == op
    {
        PendingOperation {
            op,
            resp: None,
        }
    }

    pub fn set_result(&mut self, resp: DT::Response) {
        self.resp = Some(resp);
    }

    // pub fn to_result(self) -> DT::Response {
    //     self.resp.get_Some_0()
    // }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Context
////////////////////////////////////////////////////////////////////////////////////////////////////



struct_with_invariants!{
/// Contains state of a particular thread context within NR w.r.g. to outstanding operations.
///
///  - Dafny: linear datatype Context = Context(
///  - Rust:  pub(crate) struct Context<T, R, M>
///
/// Note, in contrast to the Rust version, we just have a single outstanding operation
#[repr(align(128))]
pub struct Context<DT: Dispatch> {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    /// This is protected by the `atomic` field.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    pub/*REVIEW: (crate)*/ batch: CachePadded<PCell<PendingOperation<DT>>>,

    /// The number of operations in this context, (just 0 or 1)
    ///
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    pub/*REVIEW: (crate)*/ atomic: CachePadded<AtomicU64<_, ContextGhost<DT>, _>>,

    /// ghost: identifier of the thread
    pub thread_id_g: Ghost<nat>,

    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
}

pub open spec fn wf(&self, thread_idx: nat) -> bool {
    predicate {
        self.thread_id_g@ == thread_idx
    }
    invariant on atomic with (flat_combiner_instance, unbounded_log_instance, batch, thread_id_g) specifically (self.atomic.0) is (v: u64, g: ContextGhost<DT>) {
        &&& g.inv(v, thread_id_g@, batch.0, flat_combiner_instance@, unbounded_log_instance@)
    }
}} // struct_with_invariants!

impl<DT: Dispatch> Context<DT> {

    pub fn new(thread_id: usize, slot: Tracked<FlatCombiner::slots>, flat_combiner_instance: Tracked<FlatCombiner::Instance>, unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>)
        -> (res: (Context<DT>, Tracked<PointsTo<PendingOperation<DT>>>))
        requires
            slot@@.value.is_Empty(),
            slot@@.instance == flat_combiner_instance,
            slot@@.key == thread_id as nat
        ensures
            res.0.wf(thread_id as nat),
            res.0.batch.0.id() == res.1@@.pcell,
            res.0.flat_combiner_instance == flat_combiner_instance,
            res.0.unbounded_log_instance == unbounded_log_instance,
            res.1@@.value.is_None()
        {
        let ghost mut thread_id_g;
        proof { thread_id_g = thread_id as nat; }

        // create the storage for storing the update operation
        let (batch, batch_perms) = PCell::empty();
        let batch = CachePadded(batch);

        // create the atomic with the ghost context
        let tracked context_ghost = ContextGhost { batch_perms: None, slots: slot.get(), update: Option::None };
        let atomic = CachePadded(AtomicU64::new(Ghost((flat_combiner_instance, unbounded_log_instance, batch, Ghost(thread_id_g))), 0, Tracked(context_ghost)));

        // Assemble the context, return with the permissions
        (Context { batch, atomic, thread_id_g: Ghost(thread_id_g), flat_combiner_instance, unbounded_log_instance }, batch_perms)
    }

    /// Enqueues an operation onto this context's batch of pending operations.
    ///
    /// This is invoked by the thread that want's to execute an operation
    ///
    /// Note, enqueue is a bit a misnomer. We just have one operation per thread
    pub fn enqueue_op(&self, op: DT::WriteOperation, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.enqueue_op_pre(self.thread_id_g@, op, self.batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.enqueue_op_post(context_ghost@),
            res.1@.cell_id == self.batch.0.id(),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost { batch_perms: batch_perms, cell_id, local_updates: local_updates, fc_clients: mut fc_clients } = context_ghost.get();

        let tracked mut batch_perms = batch_perms.tracked_unwrap();
        let tracked local_updates = local_updates.tracked_unwrap();

        // put the operation there, updates the permissions so we can store them in the GhostContext
        self.batch.0.put(Tracked(&mut batch_perms), PendingOperation::new(op));

        let tracked send_request_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => store(1);
            update prev->next;
            ghost g => {
                let ghost tid = fc_clients.view().key;
                let ghost rid = local_updates.view().key;

                self.flat_combiner_instance.borrow().pre_send_request(tid, &fc_clients, &g.slots);
                send_request_result = self.flat_combiner_instance.borrow().send_request(tid, rid, fc_clients, g.slots);
                fc_clients = send_request_result.0.get();

                g.slots = send_request_result.1.get();
                g.batch_perms = Some(batch_perms);
                g.update = Some(local_updates);

                assert(g.inv(1, tid, self.batch.0, self.flat_combiner_instance.view(), self.unbounded_log_instance.view()))
            }
        );

        let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: None, cell_id, local_updates: None, fc_clients };
        (true, Tracked(new_context_ghost))
    }


    /// Returns a single response if available. Otherwise, returns None.
    ///
    /// this is invoked by the thread that has enqueued the operation before
    pub fn dequeue_response(&self, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (Option<DT::Response>, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.dequeue_resp_pre(self.batch.0.id(), self.thread_id_g@, self.flat_combiner_instance@),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, res.0, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost { batch_perms: mut batch_perms, cell_id, local_updates: mut local_updates, fc_clients: mut fc_clients } = context_ghost.get();

        let tracked recv_response_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => load();
            returning res;
            ghost g => {
                if res == 0 {
                    batch_perms = g.batch_perms;
                    local_updates = g.update;

                    let tid = fc_clients.view().key;
                    let rid = fc_clients.view().value.get_Waiting_0();
                    self.flat_combiner_instance.borrow().pre_recv_response(tid, &fc_clients, &g.slots);
                    recv_response_result = self.flat_combiner_instance.borrow().recv_response(tid, rid, fc_clients, g.slots);
                    fc_clients = recv_response_result.0.get();

                    g.slots = recv_response_result.1.get();
                    g.batch_perms = None;
                    g.update = None;
                }
            }
        );

        if res == 0 {
            let tracked mut batch_perms = batch_perms.tracked_unwrap();
            let op = self.batch.0.take(Tracked(&mut batch_perms));
            let resp = op.resp.unwrap();
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perms), cell_id, local_updates, fc_clients };
            (Some(resp), Tracked(new_context_ghost))
        } else {
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms, cell_id, local_updates, fc_clients };
            (None, Tracked(new_context_ghost))
        }
    }


    // /// Enqueues a response onto this context. This is invoked by the combiner
    // /// after it has executed operations (obtained through a call to ops()) against the
    // /// replica this thread is registered against.
    // pub fn enqueue_response(&self, resp: DT::Response) -> bool
    //     requires
    //         self.wf(self.thread_id_g@)
    //         // self.atomic != 0
    // {
    //     // let tracked token : Option<Tracked<PointsTo<PendingOperation>>>;
    //     // let res = atomic_with_ghost!(
    //     //     &self.atomic.0 => load();
    //     //     returning res;
    //     //     ghost g => {
    //     //         if res == 1 {
    //     //             // store the operatin in the cell
    //     //             token =  Some(g.batch_perms);
    //     //         } else {
    //     //             token = None;
    //     //         }
    //     //     }
    //     // );

    //     // if res != 0 {
    //     //     let tracked token = token.get_Some_0();
    //     //     // take the operation from the cell
    //     //     // HERE
    //     //     // let mut prev = self.batch.0.take(&mut token);
    //     //     // prev.set_result(resp);
    //     //     // store the operation in the cell again
    //     //     // self.batch.0.put(&mut token, prev);

    //     //     true
    //     // } else {
    //     //     false
    //     // }

    //     false
    // }


    /// Returns the maximum number of operations that will go pending on this context.
    #[inline(always)]
    pub(crate) fn batch_size() -> usize {
        // MAX_PENDING_OPS
        1
    }

    // /// Given a logical address, returns an index into the batch at which it falls.
    // #[inline(always)]
    // pub(crate) fn index(&self, logical: usize) -> usize {
    //     // logical & (MAX_PENDING_OPS - 1)
    //     0
    // }
}



////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost Context
////////////////////////////////////////////////////////////////////////////////////////////////////

struct_with_invariants!{
/// The ghost context for a thread carying permissions and tracking the state of the update operation
///
///  - Dafny:   glinear datatype ContextGhost = ContextGhost(
pub tracked struct ContextGhost<DT: Dispatch> {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    pub batch_perms: Option<PointsTo<PendingOperation<DT>>>,

    /// The flat combiner slot.
    ///
    ///  - Dafny: glinear fc: FCSlot,
    pub slots: FlatCombiner::slots,

    /// tracks the update operation
    ///
    ///  - Dafny: glinear update: glOption<Update>
    pub update: Option<UnboundedLog::local_updates<DT>>
}

//  - Dafny: predicate inv(v: uint64, i: nat, cell: Cell<OpResponse>, fc_loc_s: nat)
pub open spec fn inv(&self, v: u64, tid: nat, cell: PCell<PendingOperation<DT>>, fc: FlatCombiner::Instance, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& self.slots@.key == tid
        &&& self.slots@.instance == fc

        &&& ((v == 0) || (v == 1))
        &&& (v == 0 ==> self.slots@.value.is_Empty() || self.slots@.value.is_Response())
        &&& (v == 1 ==> self.slots@.value.is_Request() || self.slots@.value.is_InProgress())

        &&& (self.slots@.value.is_Empty() ==> {
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
        })

        &&& (self.slots@.value.is_Request() ==> {
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Init()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().op == self.update.get_Some_0()@.value.get_Init_op()
        })

        &&& (self.slots@.value.is_InProgress() ==> {
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
        })

        &&& (self.slots@.value.is_Response() ==> {
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Done()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.get_Some_0() == self.update.get_Some_0()@.value.get_Done_ret()
        })
    }
}
} // struct_with_invariants! ContextGhost


/// Request Enqueue/Dequeue ghost state
pub tracked struct FCClientRequestResponseGhost<DT: Dispatch> {
    pub tracked batch_perms: Option<PointsTo<PendingOperation<DT>>>,
    pub tracked cell_id: Ghost<CellId>,
    pub tracked local_updates: Option<UnboundedLog::local_updates<DT>>,
    pub tracked fc_clients: FlatCombiner::clients
}

impl<DT: Dispatch> FCClientRequestResponseGhost<DT> {
    pub open spec fn enqueue_op_pre(&self, tid: nat, op: DT::WriteOperation, batch_cell: CellId, fc_inst: FlatCombiner::Instance, inst: UnboundedLog::Instance<DT>) -> bool {
        &&& self.local_updates.is_Some()
        &&& self.local_updates.get_Some_0()@.instance == inst
        &&& self.local_updates.get_Some_0()@.value.is_Init()
        &&& self.local_updates.get_Some_0()@.value.get_Init_op() == op

        &&& self.batch_perms.is_Some()
        &&& self.batch_perms.get_Some_0()@.pcell == self.cell_id
        &&& self.cell_id == batch_cell
        &&& self.batch_perms.get_Some_0()@.value.is_None()

        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.value.is_Idle()
    }

    pub open spec fn enqueue_op_post(&self, pre: FCClientRequestResponseGhost<DT>) -> bool
        recommends pre.local_updates.is_Some()
    {
        &&& self.fc_clients@.value.is_Waiting()
        &&& self.fc_clients@.value.get_Waiting_0() == pre.local_updates.get_Some_0()@.key
        &&& self.fc_clients@.instance == pre.fc_clients@.instance
        &&& self.fc_clients@.key == pre.fc_clients@.key

        &&& self.cell_id == pre.cell_id
        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()
    }

    pub open spec fn dequeue_resp_pre(&self, batch_cell: CellId, tid: nat, fc_inst: FlatCombiner::Instance) -> bool {
        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.value.is_Waiting()

        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()
        &&& self.cell_id == batch_cell
    }

    pub open spec fn dequeue_resp_post(&self, pre: FCClientRequestResponseGhost<DT>, ret: Option<DT::Response>, inst: UnboundedLog::Instance<DT>) -> bool {
        &&& ret.is_Some() ==> {

            &&& self.cell_id == pre.cell_id
            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_None()
            &&& self.batch_perms.get_Some_0()@.pcell == self.cell_id

            &&& self.local_updates.is_Some()
            &&& self.local_updates.get_Some_0()@.instance == inst
            &&& self.local_updates.get_Some_0()@.value.is_Done()
            &&& self.local_updates.get_Some_0()@.key == pre.fc_clients@.value.get_Waiting_0()
            &&& self.local_updates.get_Some_0()@.value.get_Done_ret() == ret.get_Some_0()

            &&& self.fc_clients@.instance == pre.fc_clients@.instance
            &&& self.fc_clients@.key == pre.fc_clients@.key
            &&& self.fc_clients@.value.is_Idle()
        }
        &&& ret.is_None() ==> {
            &&& self == pre
        }
    }
}

} // verus!

}

pub mod utils{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    prelude::*,
    seq::Seq,
};

use crate::spec::types::{ReqId};

verus!{

pub open spec fn rids_match(
    bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat) -> bool
    decreases bools_end - bools_start
        when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{

    if bools_end == bools_start {
        rids_end == rids_start
    } else {
        if bools[bools_end - 1].is_Some() {
        &&& rids_end > rids_start
        &&& rids[rids_end - 1] == bools[bools_end - 1].get_Some_0()
        &&& rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat)
        } else {
        rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end)
        }
    }
}

pub proof fn rids_match_add_none(bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        rids_match(bools.push(Option::None), rids, bools_start, bools_end, rids_start, rids_end)
    decreases bools_end - bools_start
{
    let bools_new = bools.push(Option::None);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_none(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat);
        } else {
            rids_match_add_none(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        }
    }
}

pub proof fn rids_match_add_rid(bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat, rid: ReqId)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        rids_match(bools.push(Option::Some(rid)), rids.push(rid), bools_start, bools_end, rids_start, rids_end)
    decreases bools_end - bools_start
{
    let bools_new = bools.push(Option::Some(rid));
    let rids_new = rids.push(rid);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids_new, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_rid(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat, rid);
        } else {
            rids_match_add_rid(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end, rid);
        }
    }
}

pub proof fn rids_match_pop(
    bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        bools_end == bools_start ==> {
            rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
        },
        bools_end > bools_start ==> {
            &&& bools[bools_start as int].is_Some() ==> {
                &&& rids_start < rids_end
                &&& rids[rids_start as int] == bools[bools_start as int].get_Some_0()
                &&& rids_match(bools, rids, (bools_start + 1) as nat, bools_end, (rids_start + 1) as nat, rids_end)
            }
            &&& bools[bools_start as int].is_None() ==> {
                &&& rids_match(bools, rids, (bools_start + 1) as nat, bools_end, rids_start, rids_end)
            }
        }
    decreases bools_end - bools_start

{
    if bools_end == bools_start {
    } else {
        if bools[bools_end - 1].is_Some() {
        rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat);
        } else {
        rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        }
    }
}

} // verus!
}




verus! {

/// a simpe cache padding for the struct fields
#[verus::trusted]
#[repr(align(128))]
pub struct CachePadded<T>(pub T);


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Public Interface
////////////////////////////////////////////////////////////////////////////////////////////////////


/// The "main" type of NR which users interact with.
///
///  - Dafny: N/A
///  - Rust:  pub struct NodeReplicated<D: Dispatch + Sync>
pub struct NodeReplicated<#[verifier::reject_recursive_types] DT: Dispatch> {
    /// the log of operations
    ///
    ///  - Rust: log: Log<D::WriteOperation>,
    pub /* REVIEW: (crate) */ log: NrLog<DT>,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<DataStructureType, UpdateOp, ReturnType>>>,
    pub /* REVIEW (crate) */ replicas: Vec<Box<Replica<DT>>>,


    // pub /* REVIEW: (crate) */ thread_tokens: Vec<Vec<ThreadToken<DT>>>,

    /// XXX: should that be here, or go into the NrLog / replicas?
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

impl<DT: Dispatch> crate::ThreadTokenT<DT, Replica<DT>> for ThreadToken<DT> {
    open spec fn wf(&self, replica: &Replica<DT>) -> bool {
        ThreadToken::<DT>::wf(self, replica)
    }

    open spec fn replica_id_spec(&self) -> nat {
        ThreadToken::<DT>::replica_id_spec(self)
    }
}

impl<DT: Dispatch + Sync> crate::NR<DT> for NodeReplicated<DT> {
    type Replica = Replica<DT>;
    type ReplicaId = ReplicaId;
    type TT = ThreadToken<DT>;

    /// Wellformedness of the NodeReplicated data structure
    open spec fn wf(&self) -> bool {
        // the log shall be well-formed and the instances match
        &&& self.log.wf()
        &&& self.unbounded_log_instance@ == self.log.unbounded_log_instance@
        &&& self.cyclic_buffer_instance@ == self.log.cyclic_buffer_instance@

        // the number of replicas should be the as configured
        &&& self.replicas.len() <= MAX_REPLICAS

        // the replicas should be well-formed and the instances match
        &&& (forall |i| 0 <= i < self.replicas.len() ==> {
            &&& (#[trigger] self.replicas[i]).wf()
            &&& self.replicas[i].spec_id() == i
            &&& self.replicas[i].replica_token@ == i
            &&& self.replicas[i].unbounded_log_instance@ == self.unbounded_log_instance@
            &&& self.replicas[i].cyclic_buffer_instance@ == self.cyclic_buffer_instance@
        })
    }

    open spec fn replicas(&self) -> Vec<Box<Self::Replica>> {
        self.replicas
    }

    open spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT> {
        self.log.unbounded_log_instance@
    }

    /// Creates a new, replicated data-structure from a single-threaded
    /// data-structure that implements [`Dispatch`]. It uses the [`Default`]
    /// constructor to create a initial data-structure for `D` on all replicas.
    ///
    ///  - Dafny: n/a ?
    ///  - Rust:  pub fn new(num_replicas: NonZeroUsize) -> Result<Self, NodeReplicatedError>
    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res: Self)
        // requires
        //     num_replicas <= MAX_REPLICAS
        // ensures res.wf()
    {
        // switch affinity to the first replica
        chg_mem_affinity.call(0);

        let (log, replica_tokens, nr_log_tokens) = NrLog::new(num_replicas, LOG_SIZE);

        let tracked NrLogTokens {
            num_replicas: _,
            replicas: mut replicas,
            combiners: mut combiners,
            cb_combiners: mut cb_combiners,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = nr_log_tokens.get();

        let mut actual_replicas : Vec<Box<Replica<DT>>> = Vec::new();
        let mut thread_tokens : Vec<Vec<ThreadToken<DT>>> = Vec::new();
        let mut idx = 0;
        while idx < num_replicas
            invariant
                num_replicas <= MAX_REPLICAS,
                unbounded_log_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.unbounded_log_instance() == unbounded_log_instance,
                0 <= idx <= num_replicas,
                replica_tokens.len() == num_replicas,
                forall |i| 0 <= i < num_replicas ==> (#[trigger]replica_tokens[i]).id_spec() == i,
                actual_replicas.len() == idx,
                forall |i| #![trigger actual_replicas[i]] 0 <= i < idx ==> {
                    &&& actual_replicas[i as int].wf()
                    &&& actual_replicas[i as int].spec_id() == i
                    &&& actual_replicas[i as int].unbounded_log_instance@ == unbounded_log_instance
                    &&& actual_replicas[i as int].cyclic_buffer_instance@ == cyclic_buffer_instance
                },
                (forall |i| #![trigger replicas[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger]  replicas.contains_key(i)
                    &&& replicas[i]@.instance == unbounded_log_instance
                    &&& replicas[i]@.key == i
                    &&& replicas[i]@.value == DT::init_spec()
                }),
                (forall |i| #![trigger combiners[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger] combiners.contains_key(i)
                    &&& combiners[i]@.instance == unbounded_log_instance
                    &&& combiners[i]@.key == i
                    &&& combiners[i]@.value.is_Ready()
                }),
                (forall |i| #![trigger cb_combiners[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger]cb_combiners.contains_key(i)
                    &&& cb_combiners[i]@.instance == cyclic_buffer_instance
                    &&& cb_combiners[i]@.key == i
                    &&& cb_combiners[i]@.value.is_Idle()
                })

        {
            let ghost mut idx_ghost; proof { idx_ghost = idx as nat };

            let replica_token = replica_tokens[idx].clone();
            let tracked config = ReplicaConfig {
                replica: replicas.tracked_remove(idx_ghost),
                combiner: combiners.tracked_remove(idx_ghost),
                cb_combiner: cb_combiners.tracked_remove(idx_ghost),
                unbounded_log_instance: unbounded_log_instance.clone(),
                cyclic_buffer_instance: cyclic_buffer_instance.clone()
            };

            // switch the affinity of the replica before we do the allocation
            chg_mem_affinity.call(replica_token.id());

            let replica = Replica::new(replica_token, MAX_THREADS_PER_REPLICA, Tracked(config));
            actual_replicas.push(Box::new(replica));
            idx = idx + 1;
        }

        // change the affinity back
        chg_mem_affinity.call(0);

        let unbounded_log_instance = Tracked(unbounded_log_instance);
        let cyclic_buffer_instance = Tracked(cyclic_buffer_instance);
        NodeReplicated { log, replicas: actual_replicas, unbounded_log_instance, cyclic_buffer_instance }
    }

    /// Registers a thread with a given replica in the [`NodeReplicated`]
    /// data-structure. Returns an Option containing a [`ThreadToken`] if the
    /// registration was successful. None if the registration failed.
    ///
    /// XXX: in the dafny version, we don't have this. Instead, we pre-allocate all
    ///      threads for the replicas etc.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken>
    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<ThreadToken<DT>>)
        // requires old(self).wf()
        // ensures
        //     self.wf(),
        //     result.is_Some() ==> result.get_Some_0().WF(&self.replicas[replica_id as int])
    {
        if (replica_id as usize) < self.replicas.len() {
            let mut replica : Box<Replica<DT>> = self.replicas.remove(replica_id);
            let res : Option<ThreadToken<DT>> = (*replica).register();
            self.replicas.insert(replica_id, replica);
            res
        } else {
            Option::None
        }
    }

    /// Executes a mutable operation against the data-structure.
    ///
    ///  - Dafny:
    ///  - Rust:  pub fn execute_mut(&self, op: <D as Dispatch>::WriteOperation, tkn: ThreadToken)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    fn execute_mut(&self, op: DT::WriteOperation, tkn: ThreadToken<DT>, ticket: Tracked<UnboundedLog::local_updates<DT>>)
        -> (result: Result<(DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>),
                           (ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>) > )
        // requires
        //     self.wf(), // wf global node
        //     tkn.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
        //     is_update_ticket(ticket@, op, self.log.unbounded_log_instance@)
        // ensures
        //     result.is_Ok() ==> is_update_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.log.unbounded_log_instance@) && result.get_Ok_0().1.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
        //     result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            Ok((&self.replicas[replica_id]).execute_mut(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }


    /// Executes a immutable operation against the data-structure.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn execute(&self, op: <D as Dispatch>::ReadOperation<'_>, tkn: ThreadToken,)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    fn execute(&self, op: DT::ReadOperation, tkn: ThreadToken<DT>,  ticket: Tracked<UnboundedLog::local_reads<DT>>)
            -> (result: Result<(DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>), (ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>)>)
        // requires
        //     self.wf(), // wf global node
        //     tkn.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
        //     is_readonly_ticket(ticket@, op, self.log.unbounded_log_instance@)
        // ensures
        //     result.is_Ok() ==> is_readonly_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.log.unbounded_log_instance@) && result.get_Ok_0().1.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
        //     result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            Ok((&self.replicas[replica_id]).execute(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }
}

} // verus!

}

pub mod constants{
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;


verus! {

/// the maximum number of replicas
pub open const MAX_REPLICAS_PER_LOG: usize = 16;

/// the number of replicas we have
// pub open const NUM_REPLICAS: usize = 4;

#[verus::trusted]
pub open const MAX_REPLICAS: usize = 16;

/// the size of the log in bytes
pub open const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

// making the assumption here that the write operation is about 12-16 bytes..
pub open const LOG_SIZE: usize = 512 * 1024; // 4 * 1024 * 1024;

/// maximum number of threads per replica
pub open const MAX_THREADS_PER_REPLICA: usize = 64;

pub open const MAX_PENDING_OPS: usize = 1;

/// the maximum number of requests
pub open const MAX_REQUESTS: usize = MAX_THREADS_PER_REPLICA * MAX_PENDING_OPS;

/// interval when we do a try_combine when checking for responses
pub open const RESPONSE_CHECK_INTERVAL : usize = 0x2000_0000;

/// Constant required for garbage collection. When the tail and the head are these many
/// entries apart on the circular buffer, garbage collection will be performed by one of
/// the replicas registered with the log.
///
/// For the GC algorithm to work, we need to ensure that we can support the largest
/// possible append after deciding to perform GC. This largest possible append is when
/// every thread within a replica has a full batch of writes to be appended to the shared
/// log.
pub open const GC_FROM_HEAD: usize = MAX_PENDING_OPS * MAX_THREADS_PER_REPLICA;


/// Threshold after how many iterations we abort and report the replica we're waiting for
/// as stuck for busy spinning loops.
///
/// Should be a power of two to avoid divisions.
pub open const WARN_THRESHOLD: usize = 0x10000000;


pub open const MAX_IDX : u64 = 0xffff_ffff_f000_0000;

} // verus!

}


use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::simple_log::SimpleLog;


pub use crate::exec::NodeReplicated;
pub use crate::exec::context::ThreadToken;


#[cfg(feature = "counter_dispatch_example")]
mod counter_dispatch_example{
// the verus dependencies

// trustedness: ignore this file

use vstd::prelude::*;

use crate::{Dispatch, NodeReplicated as _};
use crate::constants::NUM_REPLICAS;

// exec imports
use crate::exec::context::ThreadToken;
use crate::exec::NodeReplicated;

verus! {
/// represents a replica state
pub struct DataStructureSpec {
    pub val: u64,
}

impl DataStructureSpec {

    // #[verifier(opaque)]
    pub open spec fn init() -> Self {
        DataStructureSpec { val: 0 }
    }

    /// reads the current state of the replica
    // #[verifier(opaque)]
    pub open spec fn spec_read(&self, op: ReadonlyOp) -> ReturnType {
        ReturnType::Value(self.val)
    }

    // #[verifier(opaque)]
    pub open spec fn spec_update(self, op: UpdateOp) -> (Self, ReturnType) {
        match op {
            UpdateOp::Reset => (DataStructureSpec { val: 0 }, ReturnType::Ok),
            UpdateOp::Inc => (DataStructureSpec { val: if self.val < 0xffff_ffff_ffff_ffff { (self.val + 1) as u64 } else { 0 } }, ReturnType::Ok)
        }
    }
}

#[verifier(external_body)] /* vattr */
fn print_update_op(op: &UpdateOp, val: u64) {
    match op {
        UpdateOp::Reset => println!("Update::Reset {val} -> 0"),
        UpdateOp::Inc => println!("Update::increment {val} -> {}", val + 1),
    }
}

#[verifier(external_body)] /* vattr */
fn print_readonly_op(op: &ReadonlyOp) {
    println!("Read::Get")
}

// use vstd::prelude::*;

pub struct DataStructureType {
    pub val: u64,
}

impl DataStructureType {
    pub fn init() -> (result: Self)
        ensures result.interp() == DataStructureSpec::init()
    {
        DataStructureType { val: 0 }
    }

    pub open spec fn interp(&self) -> DataStructureSpec {
        DataStructureSpec { val: self.val }
    }

    pub fn update(&mut self, op: UpdateOp) -> (result: ReturnType)
        ensures old(self).interp().spec_update(op) == (self.interp(), result)
    {
        // print_update_op(&op, self.val);
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = if self.val < 0xffff_ffff_ffff_ffff { self.val + 1 } else { 0 }
        }
        ReturnType::Ok
    }

    pub fn read(&self, op: ReadonlyOp) -> (result: ReturnType)
        ensures self.interp().spec_read(op) == result
    {
        // print_readonly_op(&op);
        ReturnType::Value(self.val)
    }
}

impl Dispatch for DataStructureType {
    type ReadOperation = ReadonlyOp;

    type WriteOperation = UpdateOp;

    type Response = ReturnType;

    type View = DataStructureSpec;

    open spec fn view(&self) -> Self::View {
        DataStructureSpec { val: self.val }
    }

    fn init() -> (res: Self)
    {
        DataStructureType { val: 0 }
    }

    // partial eq also add an exec operation
    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation) {
        op.clone()
    }

    fn clone_response(op: &Self::Response) -> (res: Self::Response) {
        op.clone()
    }

    /// Method on the data structure that allows a read-only operation to be
    /// executed against it.
    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response) {
        match op {
            ReadonlyOp::Get => {
                ReturnType::Value(self.val)
            }
        }
    }

    /// Method on the data structure that allows a write operation to be
    /// executed against it.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response) {
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = if self.val < 0xffff_ffff_ffff_ffff { self.val + 1 } else { 0 }
        }
        ReturnType::Ok
    }

    open spec fn init_spec() -> Self::View {
        DataStructureSpec { val: 0 }
    }

    open spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response {
        match op {
            ReadonlyOp::Get => {
                ReturnType::Value(ds.val)
            }
        }
    }

    open spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (Self::View, Self::Response) {
        match op {
            UpdateOp::Reset => (DataStructureSpec { val: 0 }, ReturnType::Ok),
            UpdateOp::Inc => (DataStructureSpec { val: if ds.val < 0xffff_ffff_ffff_ffff { (ds.val + 1) as u64 } else { 0 } }, ReturnType::Ok)
        }
    }
}


// #[spec]
// #[verifier(opaque)]
// pub fn read(state: DataStructureSpec, op: ReadonlyOp) -> ReturnType {
//     ReturnType { u: 0 }
// }

// #[spec]
// #[verifier(opaque)]
// pub fn update_state(state: DataStructureSpec, op: UpdateOp) -> (DataStructureSpec, ReturnType) {
//     (state, ReturnType { u: 0 })
// }


/// represents a update operation on the replica, in NR this is handled by `dispatch_mut`
pub enum UpdateOp {
    Reset,
    Inc,
}

impl UpdateOp {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        match self {
            UpdateOp::Reset => UpdateOp::Reset,
            UpdateOp::Inc => UpdateOp::Inc,
        }
    }
}

/// Represents a read-only operation on the replica, in NR this is handled by `dispatch`
pub enum ReadonlyOp {
    Get,
}

/// the operations enum
pub enum Request {
    Update(UpdateOp),
    Readonly(ReadonlyOp),
}

/// Represents the return type of the read-only operation
#[derive(PartialEq, Eq)]
pub enum ReturnType {
    Value(u64),
    Ok,
}

impl Structural for ReturnType {}

impl ReturnType {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        match self {
            ReturnType::Value(v) => ReturnType::Value(*v),
            ReturnType::Ok => ReturnType::Ok,
        }
    }
}
}


use  std::sync::Arc;

struct NrCounter(Arc<NodeReplicated<DataStructureType>>, ThreadToken<DataStructureType>);

const NUM_OPS_PER_THREAD: usize = 1_000_000;
const NUM_THREADS_PER_REPLICA: usize = 4;
const NUM_THREADS: usize = NUM_THREADS_PER_REPLICA*NUM_REPLICAS;

// #[verifier(external_body)] /* vattr */
#[verifier::external_body] /* vattr */
pub fn example_main() {

    println!("Creating Replicated Data Structure...");

    let mut nr_counter = NodeReplicated::new(NUM_REPLICAS);

    println!("Obtaining Thread tokens for {NUM_THREADS} threads...");

    let mut thread_tokens = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS+2*NUM_REPLICAS {
        if let Option::Some(tkn) = nr_counter.register(idx % NUM_REPLICAS) {
            println!(" - thread: {}.{}", tkn.replica_id(), tkn.thread_id());
            thread_tokens.push(tkn);
        } else {
            panic!("could not register with replica!");
        }
    }

    let nr_counter = Arc::new(nr_counter);

    // The replica executes a Modify or Access operations by calling
    // `execute_mut` and `execute`. Eventually they end up in the `Dispatch` trait.
    let thread_loop = |counter: NrCounter| {
        let NrCounter(counter, mut tkn) = counter;
        let tid = (tkn.replica_id(), tkn.thread_id());
        println!("Thread #{tid:?} start. executing {NUM_OPS_PER_THREAD} operations");
        let mut num_updates = 0;
        for i in 0..NUM_OPS_PER_THREAD {
            match (tid.1 as usize + i) % 2 {
                0 => {
                    // println!(" - Thread #{tid:?}  executing Update operation {i}");
                    num_updates += 1;
                    match counter.execute_mut(UpdateOp::Inc, tkn, Tracked::assume_new()) {
                        Result::Ok((ret, t, _)) => {
                            tkn = t;
                        },
                        Result::Err((t, _)) => {
                            tkn = t;
                        }
                    }
                }
                _ => {
                    // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
                    match  counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                        Result::Ok((ret, t, _)) => {
                            tkn = t;
                        },
                        Result::Err((t, _)) => {
                            tkn = t;
                        }
                    }
                }
            };

            // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
            match  counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                Result::Ok((ret, t, _)) => {
                    tkn = t;
                },
                Result::Err((t, _)) => {
                    tkn = t;
                }
            }
        }

        // make sure to make progress on all replicas
        for _ in 0..NUM_OPS_PER_THREAD*2  {
            std::thread::yield_now();
            match counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                Result::Ok((ret, t, _)) => {
                    tkn = t;
                },
                Result::Err((t, _)) => {
                    tkn = t;
                }
            }
        }
        println!("Thread #{tid:?} done. executed {num_updates} update operations");
    };

    println!("Creating {NUM_THREADS} threads...");

    let mut threads = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS {
        let counter = nr_counter.clone();
        let tkn = thread_tokens.pop().unwrap();
        threads.push(std::thread::spawn(move || {
            thread_loop(NrCounter(counter, tkn));
        }));
    }

    println!("Waiting for threads to finish...");

    // Wait for all the threads to finish
    for idx in 0..NUM_THREADS {
        let thread = threads.pop().unwrap();
        thread.join().unwrap();
    }

    println!("Obtain final result...");

    for idx in 0..NUM_REPLICAS {
        let tkn = thread_tokens.pop().unwrap();
        match nr_counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
            Result::Ok((ret, t, _)) => {
                match ret {
                    ReturnType::Value(v) => {
                        println!("Replica {idx} - Final Result: {v} expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
                    }
                    ReturnType::Ok => {
                        println!("Replica {idx} - Final Result: OK? expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
                    }
                }
            },
            Result::Err(t) => {
                println!("Replica {idx} - Final Result: Err");
            }
        }
    }

    println!("Done!");
}

}


verus! {

pub type ReplicaId = usize; // $line_count$Trusted$

global size_of usize == 8;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nr State and its operations
////////////////////////////////////////////////////////////////////////////////////////////////////

// the following types are currently arbitrary, the depend on the the actual data structure that
// each replica wraps. The NR crate has this basically as a trait that the data structure must
// implement.

/// type of the node / replica id
pub type NodeId = nat; // $line_count$Trusted$

/// the log index
pub type LogIdx = nat; // $line_count$Trusted$

/// the request id
pub type ReqId = nat; // $line_count$Trusted$

/// the id of a thread on a replica node
pub type ThreadId = nat; // $line_count$Trusted$

#[verus::trusted]
pub trait Dispatch: Sized {
    /// A read-only operation. When executed against the data structure, an
    /// operation of this type must not mutate the data structure in any way.
    /// Otherwise, the assumptions made by NR no longer hold.
    type ReadOperation: Sized;

    /// A write operation. When executed against the data structure, an
    /// operation of this type is allowed to mutate state. The library ensures
    /// that this is done so in a thread-safe manner.
    type WriteOperation: Sized + Send;

    /// The type on the value returned by the data structure when a
    /// `ReadOperation` or a `WriteOperation` successfully executes against it.
    type Response: Sized;

    // Self is the concrete type

    ///
    type View;

    spec fn view(&self) -> Self::View;

    fn init() -> (res: Self)
        ensures res@ == Self::init_spec();

    // partial eq also add an exec operation
    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation)
        ensures op == res;

    fn clone_response(op: &Self::Response) -> (res: Self::Response)
        ensures op == res;

    /// Method on the data structure that allows a read-only operation to be
    /// executed against it.
    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response)
        ensures Self::dispatch_spec(self@, op) == result
        ;

    /// Method on the data structure that allows a write operation to be
    /// executed against it.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response)
        ensures Self::dispatch_mut_spec(old(self)@, op) == (self@, result);

    spec fn init_spec() -> Self::View;

    spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response;

    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (Self::View, Self::Response);
}




#[verus::trusted]
pub open spec fn is_readonly_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_reads<DT>,
    op: DT::ReadOperation,
    log: UnboundedLog::Instance<DT>) -> bool
{
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value.is_Init() && ticket@.value.get_Init_op() == op
    // requires ticket.loc == TicketStubSingletonLoc.loc()
    &&& ticket@.instance == log
}

#[verus::trusted]
pub open spec fn is_readonly_stub<DT: Dispatch>(
    stub: UnboundedLog::local_reads<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists ctail, op, nodeid :: stub == ReadOp(rid, ReadonlyDone(op, output, nodeid, ctail)))
    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}

#[verus::trusted]
pub open spec fn is_update_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_updates<DT>,
    op: DT::WriteOperation,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value.is_Init() && ticket@.value.get_Init_op() == op
    // requires ticket.loc == TicketStubSingletonLoc.loc()
    &&& ticket@.instance == log
}

#[verus::trusted]
pub open spec fn is_update_stub<DT: Dispatch>(
    stub: UnboundedLog::local_updates<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists log_idx :: stub == UpdateOp(rid, UpdateDone(output, log_idx)))
    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}

#[verus::trusted]
pub trait ThreadTokenT<DT: Dispatch, Replica> {
    spec fn wf(&self, replica: &Replica) -> bool;

    spec fn replica_id_spec(&self) -> nat;
}

#[verifier(external_body)] /* vattr */
#[verus::trusted]
pub struct AffinityFn {
    f: Box<dyn Fn(ReplicaId)>
}

#[verus::trusted]
impl AffinityFn {
    #[verifier(external_body)] /* vattr */
    pub fn new(f: impl Fn(ReplicaId) + 'static) -> Self {
        Self{ f: Box::new(f)}
    }
    #[verifier(external_body)] /* vattr */
    pub fn call(&self, rid: ReplicaId) {
        (self.f)(rid)
    }
}

#[verus::trusted]
pub trait NR<DT: Dispatch + Sync>: Sized {
    type Replica;
    type ReplicaId;
    type TT: ThreadTokenT<DT, Self::Replica>;

    spec fn wf(&self) -> bool;

    spec fn replicas(&self) -> Vec<Box<Self::Replica>>;

    spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT>;

    // TODO this does not properly ensures initialization I think
    // I think it needs to return the correct initialization token
    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res: Self)
        requires
            0 < num_replicas && num_replicas <= crate::constants::MAX_REPLICAS
        ensures
            res.wf(),
            res.replicas().len() == num_replicas;

    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<Self::TT>)
        requires old(self).wf(),
        ensures
            self.wf(),
            result.is_Some() ==> result.get_Some_0().wf(&self.replicas()[replica_id as int]);

    fn execute_mut(&self, op: DT::WriteOperation, tkn: Self::TT, ticket: Tracked<UnboundedLog::local_updates<DT>>)
        -> (result: Result<(DT::Response, Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
                           (Self::TT, Tracked<UnboundedLog::local_updates<DT>>) > )
        requires
            self.wf(), // wf global node
            tkn.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            is_update_ticket(ticket@, op, self.unbounded_log_instance())
        ensures
            result.is_Ok() ==> is_update_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.unbounded_log_instance()) && result.get_Ok_0().1.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn;

    fn execute(&self, op: DT::ReadOperation, tkn: Self::TT,  ticket: Tracked<UnboundedLog::local_reads<DT>>)
            -> (result: Result<(DT::Response, Self::TT, Tracked<UnboundedLog::local_reads<DT>>), (Self::TT, Tracked<UnboundedLog::local_reads<DT>>)>)
        requires
            self.wf(), // wf global node
            tkn.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            is_readonly_ticket(ticket@, op, self.unbounded_log_instance())
        ensures
            result.is_Ok() ==> is_readonly_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.unbounded_log_instance()) && result.get_Ok_0().1.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn;
}

#[verus::trusted]
spec fn implements_NodeReplicated<DT: Dispatch + Sync, N: NR<DT>>() -> bool { true }

#[verus::trusted]
proof fn theorem_1<DT: Dispatch + Sync>()
    ensures implements_NodeReplicated::<DT, NodeReplicated<DT>>(),
{ }


#[verus::trusted]
pub open spec fn add_ticket<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    input: InputOperation<DT>,
    rid: ReqId) -> bool
{
    !pre.local_reads.dom().contains(rid)
    && !pre.local_updates.dom().contains(rid)
    && (match input {
        InputOperation::Read(read_op) => {
            && post == UnboundedLog::State::<DT> {
                local_reads: pre.local_reads.insert(rid, crate::spec::unbounded_log::ReadonlyState::Init { op: read_op }),
                .. pre
            }
        }
        InputOperation::Write(write_op) => {
            && post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(rid, crate::spec::unbounded_log::UpdateState::Init { op: write_op }),
                .. pre
            }
        }
    })
}

#[verus::trusted]
pub open spec fn consume_stub<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    output: OutputOperation<DT>,
    rid: ReqId) -> bool
{
    match output {
        OutputOperation::Read(response) => {
            pre.local_reads.dom().contains(rid)
            && pre.local_reads[rid].is_Done()
            && pre.local_reads[rid].get_Done_ret() == response
            && post == UnboundedLog::State::<DT> {
              local_reads: pre.local_reads.remove(rid),
              .. pre
            }
        }
        OutputOperation::Write(response) => {
            pre.local_updates.dom().contains(rid)
            && pre.local_updates[rid].is_Done()
            && pre.local_updates[rid].get_Done_ret() == response
            && post == UnboundedLog::State::<DT> {
              local_updates: pre.local_updates.remove(rid),
              .. pre
            }
        }
    }
}

#[verus::trusted]
trait UnboundedLogRefinesSimpleLog<DT: Dispatch> {
    spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT>;

    // Prove that it is always possible to add a new ticket
    spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId;

    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>)
        requires pre.invariant(),
        ensures
            !pre.local_reads.dom().contains(Self::get_fresh_rid(pre)),
            !pre.local_updates.dom().contains(Self::get_fresh_rid(pre));

    proof fn refinement_inv(vars: UnboundedLog::State<DT>)
        requires vars.invariant(),
        ensures Self::interp(vars).invariant();

    proof fn refinement_init(post: UnboundedLog::State<DT>)
        requires
            post.invariant(),
            UnboundedLog::State::init(post)
        ensures
            SimpleLog::State::init(Self::interp(post));

    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
            post.invariant(),
            UnboundedLog::State::next_strong(pre, post),
        ensures
            SimpleLog::State::next(Self::interp(pre), Self::interp(post), AsyncLabel::Internal);

    proof fn refinement_add_ticket(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: InputOperation<DT>,
    )
        requires
            pre.invariant(),
            add_ticket(pre, post, input, Self::get_fresh_rid(pre)),
        ensures
            post.invariant(),
            SimpleLog::State::next(Self::interp(pre), Self::interp(post), AsyncLabel::Start(Self::get_fresh_rid(pre), input));

    proof fn refinement_consume_stub(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: ReqId
    )
        requires
            pre.invariant(),
            consume_stub(pre, post, output, rid),
        ensures
            post.invariant(),
            SimpleLog::State::next(Self::interp(pre), Self::interp(post), AsyncLabel::End(rid, output));
}

#[verus::trusted]
spec fn implements_UnboundedLogRefinesSimpleLog<DT: Dispatch, RP: UnboundedLogRefinesSimpleLog<DT>>() -> bool { true }

#[verus::trusted]
proof fn theorem_2<DT: Dispatch + Sync>()
    ensures implements_UnboundedLogRefinesSimpleLog::<DT, crate::spec::unbounded_log_refines_simplelog::RefinementProof<DT>>(),
{ }



#[is_variant]
#[verus::trusted]
pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation),
    Write(DT::WriteOperation),
}

#[is_variant]
#[verus::trusted]
pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}

#[is_variant]
#[verus::trusted]
pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(ReqId, InputOperation<DT>),
    End(ReqId, OutputOperation<DT>),
}


state_machine!{ AsynchronousSingleton<DT: Dispatch> {           // $line_count$Trusted$
    fields {                                                    // $line_count$Trusted$
        pub state: DT::View,                                    // $line_count$Trusted$
        pub reqs: Map<ReqId, InputOperation<DT>>,               // $line_count$Trusted$
        pub resps: Map<ReqId, OutputOperation<DT>>,             // $line_count$Trusted$
    }                                                           // $line_count$Trusted$

    pub type Label<DT> = AsyncLabel<DT>;                        // $line_count$Trusted$

    init!{                                                      // $line_count$Trusted$
        initialize() {                                          // $line_count$Trusted$
            init state = DT::init_spec();                       // $line_count$Trusted$
            init reqs = Map::empty();                           // $line_count$Trusted$
            init resps = Map::empty();                          // $line_count$Trusted$
        }                                                       // $line_count$Trusted$
    }

    transition!{                                                // $line_count$Trusted$
        internal_next(label: Label<DT>, rid: ReqId, input: InputOperation<DT>, output: OutputOperation<DT>) {   // $line_count$Trusted$
            require label.is_Internal();                     // $line_count$Trusted$
            require pre.reqs.dom().contains(rid);            // $line_count$Trusted$
            require pre.reqs[rid] == input;                  // $line_count$Trusted$
            update reqs = pre.reqs.remove(rid);              // $line_count$Trusted$
            update resps = pre.resps.insert(rid, output);    // $line_count$Trusted$

            match input {                                    // $line_count$Trusted$
                InputOperation::Read(read_op) => {           // $line_count$Trusted$
                    require output === OutputOperation::Read(DT::dispatch_spec(pre.state, read_op));  // $line_count$Trusted$
                }                                                                           // $line_count$Trusted$
                InputOperation::Write(write_op) => {                                        // $line_count$Trusted$
                    let (next_state, out) = DT::dispatch_mut_spec(pre.state, write_op);     // $line_count$Trusted$
                    require output === OutputOperation::Write(out);                         // $line_count$Trusted$
                    update state = next_state;                                              // $line_count$Trusted$
                }                                                                           // $line_count$Trusted$
            }                                                                               // $line_count$Trusted$
        }                                                                                   // $line_count$Trusted$
    }                                                                                       // $line_count$Trusted$

    transition!{                                        // $line_count$Trusted$
        no_op(label: Label<DT>) {                       // $line_count$Trusted$
            require label.is_Internal();                // $line_count$Trusted$
            /* stutter step */                          // $line_count$Trusted$
        }                                               // $line_count$Trusted$
    }                                                   // $line_count$Trusted$

    transition!{                                                            // $line_count$Trusted$
        start(label: Label<DT>, rid: ReqId, input: InputOperation<DT>) {    // $line_count$Trusted$
            require label == AsyncLabel::<DT>::Start(rid, input);           // $line_count$Trusted$
            require !pre.reqs.dom().contains(rid);                          // $line_count$Trusted$
            update reqs = pre.reqs.insert(rid, input);                      // $line_count$Trusted$
        }                                                                   // $line_count$Trusted$
    }                                                                       // $line_count$Trusted$

    transition!{                                                            // $line_count$Trusted$
        end(label: Label<DT>, rid: ReqId, output: OutputOperation<DT>) {    // $line_count$Trusted$
            require label == AsyncLabel::<DT>::End(rid, output);            // $line_count$Trusted$
            require pre.resps.dom().contains(rid);                          // $line_count$Trusted$
            require pre.resps[rid] == output;                               // $line_count$Trusted$
            update resps = pre.resps.remove(rid);                           // $line_count$Trusted$
        }                                                                   // $line_count$Trusted$
    }                                                                       // $line_count$Trusted$
}}                                                                          // $line_count$Trusted$

#[is_variant]
#[verus::trusted]
pub enum SimpleLogBehavior<DT: Dispatch> {
    Stepped(SimpleLog::State<DT>, AsyncLabel<DT>, Box<SimpleLogBehavior<DT>>),
    Inited(SimpleLog::State<DT>),
}

#[verus::trusted]
impl<DT: Dispatch> SimpleLogBehavior<DT> {
    pub open spec fn get_last(self) -> SimpleLog::State<DT> {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => post,
            SimpleLogBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => {
                tail.wf() && SimpleLog::State::next(tail.get_last(), post, op)
            }
            SimpleLogBehavior::Inited(post) => {
                SimpleLog::State::init(post)
            }
        }
    }
}

#[is_variant]
#[verus::trusted]
pub enum AsynchronousSingletonBehavior<DT: Dispatch> {
    Stepped(AsynchronousSingleton::State<DT>, AsyncLabel<DT>, Box<AsynchronousSingletonBehavior<DT>>),
    Inited(AsynchronousSingleton::State<DT>),
}

#[verus::trusted]
impl<DT: Dispatch> AsynchronousSingletonBehavior<DT> {
    pub open spec fn get_last(self) -> AsynchronousSingleton::State<DT> {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => post,
            AsynchronousSingletonBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => {
                tail.wf() && AsynchronousSingleton::State::next(tail.get_last(), post, op)
            }
            AsynchronousSingletonBehavior::Inited(post) => {
                AsynchronousSingleton::State::init(post)
            }
        }
    }
}

#[verus::trusted]
pub open spec fn behavior_equiv<DT: Dispatch>(a: SimpleLogBehavior<DT>, b: AsynchronousSingletonBehavior<DT>) -> bool
    decreases a, b
{
    // (a.Inited? && b.Inited?)
    ||| (a.is_Inited() && b.is_Inited())
    // || (a.Stepped? && a.op.InternalOp? && equiv(a.tail, b))
    ||| (a.is_Stepped() && a.get_Stepped_1().is_Internal() && behavior_equiv(*a.get_Stepped_2(), b))
    // || (b.Stepped? && b.op.InternalOp? && equiv(a, b.tail))
    ||| (b.is_Stepped() && b.get_Stepped_1().is_Internal() && behavior_equiv(a, *b.get_Stepped_2()))
    // || (a.Stepped? && b.Stepped? && a.op == b.op && equiv(a.tail, b.tail))
    ||| (a.is_Stepped() && b.is_Stepped() && a.get_Stepped_1() == b.get_Stepped_1() && behavior_equiv(*a.get_Stepped_2(), *b.get_Stepped_2()))
}

#[verus::trusted]
trait SimpleLogRefinesAsynchronousSingleton<DT: Dispatch> {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<DT>)
        requires a.wf(),
        ensures b.wf() && behavior_equiv(a, b);
}

#[verus::trusted]
spec fn implements_SimpleLogRefinesAsynchronousSingleton<DT: Dispatch, RP: SimpleLogRefinesAsynchronousSingleton<DT>>() -> bool { true }

#[verus::trusted]
proof fn theorem_3<DT: Dispatch + Sync>()
    ensures implements_SimpleLogRefinesAsynchronousSingleton::<DT, crate::spec::linearization::RefinementProof>(),
{ }


} // verus!
