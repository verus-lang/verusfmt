verus! {

impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
    spec fn view(&self) -> Seq<T>;

}

} // verus!
