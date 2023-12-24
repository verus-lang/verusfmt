use vstd::prelude::*;

verus! {

/*
spec fn test_rec2(x: int, y: int) -> int
    decreases x, y,
{
    3
}
*/

spec fn add0(a: nat, b: nat) -> nat
    recommends
        a > 0,
    via add0_recommends,
{
    a
}

#[via_fn]
proof fn add0_recommends(a: nat, b: nat) {
    // proof
}

/*
spec fn rids_match(bools_start: nat) -> bool
    decreases bools_start,
    when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{
    true
}
*/

fn main() {}

} // verus!

/*
pub type ReplicaId = usize; // $line_count$Trusted$
*/
