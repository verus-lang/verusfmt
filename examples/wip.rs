verus! {

struct StrictlyOrderedVec<K: KeyTrait> {
    a: int,
}

struct DelegationMap<
    #[verifier(maybe_negative)]
    K: KeyTrait + VerusClone,
> {
    b: int,
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    fn view() -> Map<K, AbstractEndPoint> {
        c
    }
}

} // verus!
