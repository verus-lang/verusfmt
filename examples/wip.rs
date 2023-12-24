verus! {

fn test() {
    loop
        invariant
            false,
        invariant_ensures
            true,
        ensures
            next_idx + count <= 512,
    {
        x
    }
}

} // verus!
