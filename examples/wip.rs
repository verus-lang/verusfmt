verus! {

impl OwlSpecSerialize for owlSpec_t {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_t(self)
    }
}

} // verus!
