verus! {

// We add a trailing comma that Verus (and Rust) doesn't like
spec fn host_ignoring_unparseable(pre: AbstractHostState, post: AbstractHostState) -> bool {
    post == AbstractHostState { received_packet: None, another_long_field_name: 12345, yet_another_long_field_name: 12345, ..pre }
}

// We add a comma after the ensures, which Verus doesn't like
fn is_marshalable() -> (res: bool)
    ensures res == self.is_marshalable();

fn test() {
    // Adds a comma that `reveal` doesn't like
    reveal(crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size);
}

// We add an extra star in front of the const
#[verifier(external)]
pub unsafe fn unflatten_args(
    num_args: i32,
    arg_lengths: *const i32,
) -> bool 
{
    true
}


} // verus!
