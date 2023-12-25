verus! {

fn local_direct_update(loc1: Local, loc2: Local, i: int, j: int, pq: int) -> bool {
    &&& loc2 == Local { heap: loc2.heap, ..loc1 }
}

} // verus!
