verus! {

#[verifier(external_body)]  // inline comment
pub exec fn foo()
    requires
        a > 5,
{
}

} // verus!
