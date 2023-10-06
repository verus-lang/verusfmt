/// External comment 1
/// External comment 2
verus! {

/// Comment 1
/// Comment 2
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // Line comment 1
    // Line comment 2
    proof {
        let u = my_spec_fun(x as int, y as int);  // inline comment 1
        my_proof_fun(u / 2, y as int);  // inline comment 2
    }
}

} // verus!
