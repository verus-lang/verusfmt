X Syntax.rs updates
X - 2-space inline comments
X - Various "bonus" commas


Bugs:

X - "assert(f1(3) > 3);" is being parsed as "as" "ert(...)", yielding "as sert(f1(3) > 3);"

- Handling of multiline comments
    /* TODO
    pub open(crate) spec fn my_pub_spec_fun2(x: u32, y: u32) -> u32 {
        // function visible to all, body visible to crate
        x / 2 + y / 2
    }
    */
    // TODO(main_new) pub(crate) is not being handled correctly
    // pub(crate) open spec fn my_pub_spec_fun3(x: int, y: int) -> int {
    //     // function and body visible to crate
    //     x / 2 + y / 2
    // }

- Are we being too aggressive in one-lining if-else?
    -    if y > 0 {
    -        1 + test_rec2(x, y - 1)
    -    } else if x > 0 {
    -        2 + test_rec2(x - 1, 100)
    -    } else {
    -        3
    -    }
    +    if y > 0 { 1 + test_rec2(x, y - 1) } else if x > 0 { 2 + test_rec2(x - 1, 100) } else { 3 }

- The `implies` keyword needs a preceding space
    -    assert(forall|x: int| x < 10 implies f1(x) < 11) by {
    +    assert(forall|x: int| x < 10implies f1(x) < 11)

- Remove space before `choose`?
      -        let x_witness = choose|x: int| f1(x) == 10;
      +        let x_witness = choose |x: int| f1(x) == 10;
  - Should be consistent with forall and exists


- Ugly line break here:
    -    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger] my_spec_fun(x, y) >= x);
    +    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger]
    +    my_spec_fun(x, y) >= x);

- And here:
    -    assume(forall|x: int, y: int|
    -        #![trigger my_spec_fun(x, y)]
    -        #![trigger f1(x), f1(y)]
    -        f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x
    -    );
    +    assume(forall|x: int, y: int| #![trigger my_spec_fun(x, y)]
    +    #![trigger f1(x), f1(y)]
    +    f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);

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


- Collapsed struct definition okay?
        -tracked struct TrackedAndGhost<T, G>(
        -    tracked T,
        -    ghost G,
        -);
        +tracked struct TrackedAndGhost<T, G>(tracked T, ghost G);
