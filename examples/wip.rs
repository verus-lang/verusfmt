verus! {

spec fn map(f: spec_fn(A) -> B) {
    1
}

spec fn adder(x: int) -> spec_fn(int) -> int {
    |y: int| x + y
}

} // verus!
