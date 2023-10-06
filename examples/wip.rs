verus! {

fn assert_by_test() {
    assert(f1(3) > 3) by {
        reveal(f1);
    }
    assert(f1(3) > 3);
}

} // verus!
