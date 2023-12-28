/*

  This file models the abstraction of an infinite log that our log
  implementation is supposed to implement.

*/
use vstd::set::*;

verus! {

pub struct AbstractInfiniteLogState {
    pub head: int,
}

} // verus!
