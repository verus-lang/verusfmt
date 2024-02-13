verus! {

fn test1()
    requires
        true,
    ensures
        true,
    opens_invariants none
{
    5
}

fn test2()
    requires
        true,
    ensures
        true,
    opens_invariants any
{
    5
}

} // verus!
