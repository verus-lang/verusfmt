verus! {

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
    requires
        x,
        y,
    recommends
        x,
    decreases x, y,
    ensures
        x,
{
    5
}
spec fn dec0(a: int) -> int
    decreases a,
    when a
    via dec0_decreases
{
    5
}

} // verus!
