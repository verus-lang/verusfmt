verus! {


/*    
// We add a comma after the ensures, which Verus doesn't like
fn is_marshalable() -> (res: bool)
    ensures res == self.is_marshalable();

fn test() {
    // Adds a comma that `reveal` doesn't like
    reveal(crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size);
}
*/

// We add an extra star in front of the const
#[verifier(external)]
fn unflatten_args(
    arg_lengths: *const i32,
) -> bool 
{
    true
}


} // verus!
