verus! {

pub fn owl_bob_main() -> (res: Result<(
        (), abcd), OwlError>) {
}

/*
pub fn owl_bob_main(&self, Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>, mut_state: &mut state_bob) -> (res: Result<( ()
, Tracked<ITreeToken<((), state_bob), Endpoint>> ), OwlError>)
requires itree@ == bob_main_spec(*self, *old(mut_state))
ensures  res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in(((), *mut_state))
 {
 }
*/
} // verus!
