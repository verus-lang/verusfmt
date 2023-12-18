verus! {

impl AffinityFn {
    pub fn new(f: impl Fn(ReplicaId) + 'static) -> Self {
        Self{ f: Box::new(f)}
    }
    pub fn call(&self, rid: ReplicaId) {
        (self.f)(rid)
    }
}

} // verus!

/*
pub type ReplicaId = usize; // $line_count$Trusted$
*/
