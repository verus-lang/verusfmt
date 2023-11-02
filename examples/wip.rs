verus! {

/*
spec fn simple_conjuncts() {
    &&& x
    &&& y
}
*/

fn test_disjuncts() 
    ensures ({ very_very_very_very_very_very_very_very_x  + very_very_very_very_very_very_very_very_y == z }),
{}

fn test_disjuncts() 
    ensures ({ 
        ||| x
        ||| y
    }),
{
}

} // verus!
