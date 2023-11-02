verus! {

spec fn simple_conjuncts(x: int, y: int) -> bool {
    &&& 1 < x
    &&& y > 9 ==> x + y < 50
    &&& x < 100
    &&& y < 100
}

spec fn complex_conjuncts(x: int, y: int) -> bool {
    let b = x < y;
    &&& b
    &&& if false {
        &&& b ==> b
        &&& !b ==> !b
    } else {
        ||| b ==> b
        ||| !b
    }
    &&& false ==> true
}

} // verus!
