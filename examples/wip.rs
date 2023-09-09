verus! {

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
{
    assert(x) by (bit_vector);
    5
}

} // verus!
