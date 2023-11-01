verus! {

spec fn simple_conjuncts(x: int, y: int) -> bool {
    &&& 1 < x
    &&& y > 9 ==> x + y < 50
    &&& x < 100
    &&& y < 100
}

fn test_disjunects() 
    ensures ({ 
        ||| 1 > 2
        ||| 3 > 5
        ||| 42 > 0
    }),
{
}

} // verus!
