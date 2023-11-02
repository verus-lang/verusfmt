verus! {

fn test() {
    assume(forall|x: int| #![auto] f1(x) < 100);
}

} // verus!
