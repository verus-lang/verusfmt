verus! {

impl<F: FnOnce<Output=OType>> Foo for FnWithRequiresEnsures {
    fn ensures() {
        1
    }
}

} // verus!
