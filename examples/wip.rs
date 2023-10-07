verus! {

fn test_ghost_unwrap(x: u32, Ghost(y): Ghost<u32>)  // unwrap so that y has typ u32, not Ghost<u32>
{
    x
}

} // verus!
