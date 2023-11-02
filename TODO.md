X Syntax.rs updates
X - 2-space inline comments
X - Various "bonus" commas

# Features
  XX - Spacing and hardlines for &&& and |||
  - Add more tests for while loops with invariants

# Won't Fix
  - No plans to sort `use` declarations the way rustfmt does

# Future Work
  - Special handling for commonly used macros, like `println!`, `state_machine!`

# Bugs:

- Parser rejects programs with /* */ comments at the end of the Verus macro

X- Don't allow breaks for function calls with no arguments:
X    pub exec fn parse_owl_t(arg: &[u8]) -> (res: Option<owl_t>)
X        ensures
X            res.is_Some() ==> res.get_Some_0().owl__x.view() == parse_owlSpec_t(arg.view()).get_Some_0(
X            ).owlSpec__x,
X    {
X    }
X 
X - Improve spacing of items inside an impl block:
X     impl cfg_alice {
X       #[verifier(external_body)]
X       pub fn func1() {
X       }
X 
X       pub fn func2() {
X       }#[verifier(external_body)]
X       pub fn func3() {}
X 
X - Don't put extra line breaks after use declarations
X     use foo::bar;
X     use bar::foo;
X     use baz::bar;

- Ugly line breaks:
        pub fn owl_bob_main(
            &self,
            Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>,
            mut_state: &mut state_bob,
        ) -> (res: Result<( ()
    , Tracked<ITreeToken<((), state_bob), Endpoint>> ), OwlError>)


X - "assert(f1(3) > 3);" is being parsed as "as" "ert(...)", yielding "as sert(f1(3) > 3);"
X
X- Handling of multiline comments
X    /* TODO
X    pub open(crate) spec fn my_pub_spec_fun2(x: u32, y: u32) -> u32 {
X        // function visible to all, body visible to crate
X        x / 2 + y / 2
X    }
X    */
X    // TODO(main_new) pub(crate) is not being handled correctly
X    // pub(crate) open spec fn my_pub_spec_fun3(x: int, y: int) -> int {
X    //     // function and body visible to crate
X    //     x / 2 + y / 2
X    // }
X
X- Are we being too aggressive in one-lining if-else?
X    -    if y > 0 {
X    -        1 + test_rec2(x, y - 1)
X    -    } else if x > 0 {
X    -        2 + test_rec2(x - 1, 100)
X    -    } else {
X    -        3
X    -    }
X    +    if y > 0 { 1 + test_rec2(x, y - 1) } else if x > 0 { 2 + test_rec2(x - 1, 100) } else { 3 }
X
X- The `implies` keyword needs a preceding space
X    -    assert(forall|x: int| x < 10 implies f1(x) < 11) by {
X    +    assert(forall|x: int| x < 10implies f1(x) < 11)
X
X - Remove space before `choose`?
X       -        let x_witness = choose|x: int| f1(x) == 10;
X       +        let x_witness = choose |x: int| f1(x) == 10;
X   - Should be consistent with forall and exists
X 

- Ugly line break here:
    -    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger] my_spec_fun(x, y) >= x);
    +    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger]
    +    my_spec_fun(x, y) >= x);

X- And here:
X    -    assume(forall|x: int, y: int|
X    -        #![trigger my_spec_fun(x, y)]
X    -        #![trigger f1(x), f1(y)]
X    -        f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x
X    -    );
X    +    assume(forall|x: int, y: int| #![trigger my_spec_fun(x, y)]
X    +    #![trigger f1(x), f1(y)]
X    +    f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);
X
X- Spurious comma added here:
X    -fn test_ghost_unwrap(x: u32, Ghost(y): Ghost<u32>) // unwrap so that y has typ u32, not Ghost<u32>
X    +fn test_ghost_unwrap(
X    +    x: u32,
X    +    Ghost(y): Ghost<u32>,  )// unwrap so that y has typ u32, not Ghost<u32>
X
X
X   and here:
X      -struct Collection { }
X      +struct Collection {
X      +    ,
X      +}
X
X    and here: <-- Actually, this one is expected; once you go multi-line Rust adds commas to everything
X        proof fn test_tracked(
X            tracked w: int,
X            tracked x: int,
X            tracked y: int,
X            z: int          <---
X        ) -> tracked TrackedAndGhost<(int, int), int> {
X            consume(w);
X            let tracked tag: TrackedAndGhost<(int, int), int> = TrackedAndGhost((x, y), z);
X            let tracked TrackedAndGhost((a, b), c) = tag;
X            TrackedAndGhost((a, b), c)
X        }
X
X - Collapsed struct definition okay?
X     - This seems to match rustfmt's output (if we remove the tracked/ghost)
X         -tracked struct TrackedAndGhost<T, G>(
X         -    tracked T,
X         -    ghost G,
X         -);
X         +tracked struct TrackedAndGhost<T, G>(tracked T, ghost G);
