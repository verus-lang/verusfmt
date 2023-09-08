verus! {

pub fn test_function(x: bool, y: bool) -> u32
    requires
        x,
        y,
    ensures
        x,
{
    5
}

} // verus!
