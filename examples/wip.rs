verus! {

fn commutative() {
    forall|x, y| #[trigger] r(x, y) == #[trigger] r(y, x)
}

} // verus!
