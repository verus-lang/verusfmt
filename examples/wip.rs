verus! {

fn test() {
    assert(forall|x: int| x < 10 implies 11) by {
        reveal(f1);
    };
}

} // verus!
