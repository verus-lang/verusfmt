verus! {

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
{
    assert(f1(3)) by {
        reveal(f1);
    };
    assert(x) by (nonlinear_arith)
        requires
            x,
            z,
    {
        assert(y);
    };
    assert(forall|x: int, y: int| x) by {
        reveal(f1);
    };
    5
}

} // verus!
