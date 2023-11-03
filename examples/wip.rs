verus! {
fn my_proof_fun(x: int, y: int)
    requires
        x < 100,  // Very important!
        y < 100,  // So, so
    ensures
        sum < 200,  // Definitely want this
        x < 200,  // And this
{
}

} // verus!
