verus! {

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
    requires
        x,
        y,
    recommends
        x,
    decreases x, y,
    ensures
        x,
        res.is_Some() ==> really_really_really_really_really_really_really_really_long.get_Some_0().foobar,
{
    let h = |x, y, z: int| {
        let w = y;
        let u = w;
        u
    };
    let i = |x| unsafe {
        let y = x;
        y
    };
    assume(x);
    assert(x);
    assert(c is Seq);
    assert(c has 3 == c has 3);
    assume(forall|x: int, y: int|
        #![trigger long_long_long_long_long_long_f1(x)]
        #![trigger long_long_long_long_long_long_g1(x)]
        long_long_long_long_long_long_f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);
    5
}

spec fn dec0(a: int) -> int
    decreases a,
    when a
    via dec0_decreases
{
    5
}

fn test_views() {
    proof {
        let s: Seq<u8> = v@;
        assert(s[0] == 10);
        assert(s[1] == 20);
    }
}

fn test_ghost_unwrap(
    x: u32,
    Ghost(y): Ghost<u32>,
)  // unwrap so that y has typ u32, not Ghost<u32>
{
    x
}

pub fn alice_addr() -> u32
    ensures
        t@ == ie.0@,
        a == b
{
    0
}

pub const fn bob_addr() -> (a: StrSlice<'static>) {
    5
}

fn test_my_funs3(a: u32) {
    test_my_funs3(a + a + a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a+ a);
}

pub fn owl_bob_main(&self, Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>, mut_state: &mut state_bob) -> (res: Result<( ()
, Tracked<ITreeToken<((), state_bob), Endpoint>> ), OwlError>)
requires itree@ == bob_main_spec(*self, *old(mut_state))
ensures  res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in(((), *mut_state))
 {
 }


} // verus!
