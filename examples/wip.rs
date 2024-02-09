verus! {

fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // my_proof_fun(x, y); // not allowed in exec code
    // let u = my_spec_fun(x, y); // not allowed exec code
    proof {
        let u = my_spec_fun(x as int, y as int);  // allowed in proof code
        my_proof_fun(u / 2, y as int);  // allowed in proof code
    }
}


} // verus!
