verus! {

fn test_single_trigger2() {
    assume(forall|x: int, y: int|
        #[trigger]
        f1(x) < 100 && #[trigger]
        f1(y) < 100 ==> my_spec_fun(x, y) >= x);
}

} // verus!
