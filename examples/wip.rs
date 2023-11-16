verus! {

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;  // this is way too restrictive; it kind of demands Copy. But we don't have a View trait yet. :v(

}

} // verus!
