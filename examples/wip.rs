verus! {

/*
spec fn simple_conjuncts() {
    &&& x
    &&& y
}
*/

fn test_disjunects() 
    ensures ({ 
        ||| x
        ||| y
    }),
{
}

} // verus!
