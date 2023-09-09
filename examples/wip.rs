verus! {

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
{
    assert(x) by (nonlinear_arith)
        requires
            x,
            z,
    {
        assert(y);
    };
    5
}

} // verus!
