
verus! {

exec static LAZY_X: Lazy<X> ensures LAZY_X.wf() { Lazy::<X>::new() }

} // verus!
