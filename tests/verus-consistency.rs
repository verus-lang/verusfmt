use insta::assert_snapshot;

/// Tests of Verus-specific formatting

// We use insta tests (http://insta.rs) to manage the correct answers.
// See README.md for details on how to run and update these tests.

fn parse_and_format(s: &str) -> miette::Result<String> {
    verusfmt::run(
        s,
        verusfmt::RunOptions {
            file_name: None,
            run_rustfmt: true,
            rustfmt_config: Default::default(),
        },
    )
}

#[test]
fn verus_functions() {
    let file = r#"
verus! {

// Verus treats constants like functions
pub open const MAX_REPLICAS_PER_LOG: usize = 16;

pub spec const MASK_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);

pub exec const MASK_L1_PG_ADDR: u64 ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1)
}

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
    assert(forall|x, y| #[trigger] r(x, y) == #[trigger] r(y, x));
    assume(forall|x: int, y: int|
        #![trigger long_long_long_long_long_long_f1(x)]
        #![trigger long_long_long_long_long_long_g1(x)]
        long_long_long_long_long_long_f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);
    5
}

fn count_size_overflow()
    ensures !x.1 ==> x.0 == count * size
{
    true
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

proof fn unbounded_log_append_entries() -> (tracked ret: int) {
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

fn test1()
    requires
        true,
    ensures
        true,
    opens_invariants none
{
    5
}

fn test2()
    requires
        true,
    ensures
        true,
    opens_invariants any
{
    5
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    // Verus treats constants like functions
    pub open const MAX_REPLICAS_PER_LOG: usize = 16;

    pub spec const MASK_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);

    pub exec const MASK_L1_PG_ADDR: u64
        ensures
            MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC,
    {
        axiom_max_phyaddr_width_facts();
        bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1)
    }

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
            res.is_Some()
                ==> really_really_really_really_really_really_really_really_long.get_Some_0().foobar,
    {
        let h = |x, y, z: int|
            {
                let w = y;
                let u = w;
                u
            };
        let i = |x|
            unsafe {
                let y = x;
                y
            };
        assume(x);
        assert(x);
        assert(c is Seq);
        assert(c has 3 == c has 3);
        assert(forall|x, y| #[trigger] r(x, y) == #[trigger] r(y, x));
        assume(forall|x: int, y: int|
            #![trigger long_long_long_long_long_long_f1(x)]
            #![trigger long_long_long_long_long_long_g1(x)]
            long_long_long_long_long_long_f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);
        5
    }

    fn count_size_overflow()
        ensures
            !x.1 ==> x.0 == count * size,
    {
        true
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

    proof fn unbounded_log_append_entries() -> (tracked ret: int) {
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
            a == b,
    {
        0
    }

    pub const fn bob_addr() -> (a: StrSlice<'static>) {
        5
    }

    fn test_my_funs3(a: u32) {
        test_my_funs3(
            a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a
                + a + a + a + a + a + a,
        );
    }

    pub fn owl_bob_main(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>,
        mut_state: &mut state_bob,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_bob), Endpoint>>), OwlError>)
        requires
            itree@ == bob_main_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in(((), *mut_state)),
    {
    }

    fn test1()
        requires
            true,
        ensures
            true,
        opens_invariants none
    {
        5
    }

    fn test2()
        requires
            true,
        ensures
            true,
        opens_invariants any
    {
        5
    }

    } // verus!
    "###);
}

#[test]
fn verus_modules() {
    let file = r#"
verus! {

pub mod PT {
    const bar: nat = 5;

    pub open spec fn test() -> int { 5 }

    pub open spec fn test2() -> int { 5 }

}

} // verus!    
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub mod PT {
        const bar: nat = 5;

        pub open spec fn test() -> int {
            5
        }

        pub open spec fn test2() -> int {
            5
        }

    }

    } // verus!
    "###);
}

#[test]
fn verus_global() {
    let file = r#"
verus! {

global size_of usize == 4;

global size_of S == 8;

global size_of S<u64> == 8;

global size_of S<U> == 8;

global layout S is size == 8, align == 8;

global layout S<u64> is size == 16, align == 8;

global layout S<u32> is size == 8, align == 4;

} // verus!    
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    global size_of usize == 4;

    global size_of S == 8;

    global size_of S<u64> == 8;

    global size_of S<U> == 8;

    global layout S is size == 8, align == 8;

    global layout S<u64> is size == 16, align == 8;

    global layout S<u32> is size == 8, align == 4;

    } // verus!
    "###);
}

#[test]
fn verus_let() {
    let file = r#"
verus!{
pub fn test() {
    let Some((key, val)) = cur else { 
        panic!() /* covered by while condition */ 
    };
    
    let Some((key, val)) = cur else { panic!() };
}
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub fn test() {
        let Some((key, val)) = cur else { panic!()  /* covered by while condition */  };

        let Some((key, val)) = cur else { panic!() };
    }

    } // verus!
    "###);
}

#[test]
fn verus_assert_by() {
    let file = r#"
verus!{

pub fn test_function(x: bool, y: bool) -> u32
    by (nonlinear_arith)
{
    assert(x) by (bit_vector);
    assert(f1(3)) by {
        reveal(f1);
    };
    assert(x) by (nonlinear_arith)
        requires
            x,
            z,
    {
        assert(y);
    };
    assert(forall|x: int, y: int| x) by {
        reveal(f1);
    };
    let x_witness = choose|x: int| f1(x) == 10;
    5
}

fn assert_by_test() {
    assert(f1(3) > 3) by {
        reveal(f1);  // reveal f1's definition just inside this block
    };
    assert(f1(3) > 3);
    assert forall|x: int| x < 10 implies x < 11 by {
        reveal(f1);
    };
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub fn test_function(x: bool, y: bool) -> u32
        by (nonlinear_arith) {
        assert(x) by (bit_vector);
        assert(f1(3)) by {
            reveal(f1);
        };
        assert(x) by (nonlinear_arith)
            requires
                x,
                z,
        {
            assert(y);
        };
        assert(forall|x: int, y: int| x) by {
            reveal(f1);
        };
        let x_witness = choose|x: int| f1(x) == 10;
        5
    }

    fn assert_by_test() {
        assert(f1(3) > 3) by {
            reveal(f1);  // reveal f1's definition just inside this block
        };
        assert(f1(3) > 3);
        assert forall|x: int| x < 10 implies x < 11 by {
            reveal(f1);
        };
    }

    } // verus!
    "###);
}

#[test]
fn verus_macro_calls() {
    let file = r#"
verus!{

    println!("{} {} {}", 
        very_very_very_very_very_very_long_e1 + 42, 
        very_very_very_very_very_very_long_e2, 
        very_very_very_very_very_very_long_e3
    );
    unknown_macro1!("{} {} {}", very_very_very_very_very_very_long_e1, very_very_very_very_very_very_long_e2, very_very_very_very_very_very_long_e3);
    unknown_macro2!("
        intro h1;
        simpl;
        cong;
        done;
    ");
    fn foo(x: usize) {
        match x {
            inj_ord_choice_pat!((_,x), *, *) => (),
            inj_ord_choice_pat!(*, (_,x), *) => (),
            inj_ord_choice_pat!(*, *, _) => (),
        };
    }
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    println!("{} {} {}",
            very_very_very_very_very_very_long_e1 + 42,
            very_very_very_very_very_very_long_e2,
            very_very_very_very_very_very_long_e3
        );

    unknown_macro1!("{} {} {}", very_very_very_very_very_very_long_e1, very_very_very_very_very_very_long_e2, very_very_very_very_very_very_long_e3);

    unknown_macro2!("
            intro h1;
            simpl;
            cong;
            done;
        ");

    fn foo(x: usize) {
        match x {
            inj_ord_choice_pat!((_,x), *, *) => (),
            inj_ord_choice_pat!(*, (_,x), *) => (),
            inj_ord_choice_pat!(*, *, _) => (),
        };
    }

    } // verus!
    "###);
}

#[test]
fn verus_macro_statements() {
    let file = r#"
verus! {

// Notice that the semicolon is optional
proof fn foo() {
    calc! {
        (==)
        1int; {}
        (0int + 1int);
    };
    calc! {
        (==)
        1int; {}
        (0int + 1int);
    }
    calc! {
        (==)
        1int; {}
        (0int + 1int);
    }
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    // Notice that the semicolon is optional
    proof fn foo() {
        calc! {
            (==)
            1int; {}
            (0int + 1int);
        };
        calc! {
            (==)
            1int; {}
            (0int + 1int);
        }
        calc! {
            (==)
            1int; {}
            (0int + 1int);
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_impl() {
    let file = r#"
verus! {

#[verifier(external_body)]
pub fn func1() {
}

pub fn func2() {
}

#[verifier(external_body)]
pub fn func3() {
}

impl cfg_alice {
    #[verifier(external_body)]
    pub fn func1() {
    }
    
    pub fn func2() {
    }
    
    #[verifier(external_body)]
    pub fn func3() {
    }
}

impl<F: FnOnce<Output=OType>> Foo for FnWithRequiresEnsures {
    fn ensures() {
        1
    }
}

impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
    spec fn view(&self) -> Seq<T>;
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    #[verifier(external_body)]
    pub fn func1() {
    }

    pub fn func2() {
    }

    #[verifier(external_body)]
    pub fn func3() {
    }

    impl cfg_alice {
        #[verifier(external_body)]
        pub fn func1() {
        }

        pub fn func2() {
        }

        #[verifier(external_body)]
        pub fn func3() {
        }
    }

    impl<F: FnOnce<Output = OType>> Foo for FnWithRequiresEnsures {
        fn ensures() {
            1
        }
    }

    impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
        spec fn view(&self) -> Seq<T>;
    }

    } // verus!
    "###);
}

#[test]
fn verus_structs() {
    let file = r#"
verus! {

spec fn host_ignoring_unparseable(pre: AbstractHostState, post: AbstractHostState) -> bool {
    post == AbstractHostState { received_packet: None, ..pre }
}

fn local_direct_update(loc1: Local, pq: int) -> bool {
    &&& loc2 == Local { heap: loc2.heap, ..loc1 }
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    spec fn host_ignoring_unparseable(pre: AbstractHostState, post: AbstractHostState) -> bool {
        post == AbstractHostState { received_packet: None, ..pre }
    }

    fn local_direct_update(loc1: Local, pq: int) -> bool {
        &&& loc2 == Local { heap: loc2.heap, ..loc1 }
    }

    } // verus!
    "###);
}

// We deviate from rustfmt here, so use our own snapshot to check for self-consistency
#[test]
fn verus_expr() {
    let file = r#"
verus! {

pub fn test_function(x: int, y: int) -> u32 {
    let very_very_very_very_very_very_long = very_very_very_very_very_very_x 
        + very_very_very_very_y + very_very_very_very_z;
    assert(a === b);
    assume(forall|x: int| #![auto] f1(x) < 100);
    let ghost (g1, g2) = g;
    5
}

fn bits_of_int() {
    seq![0].add(a) 
}

fn has_new_pointsto() {
    (forall |addr: int| mem_protect == MemProtect { read: true })
}

fn foo()
    ensures forall|x:int| x == x
{
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub fn test_function(x: int, y: int) -> u32 {
        let very_very_very_very_very_very_long = very_very_very_very_very_very_x + very_very_very_very_y
            + very_very_very_very_z;
        assert(a === b);
        assume(forall|x: int| #![auto] f1(x) < 100);
        let ghost (g1, g2) = g;
        5
    }

    fn bits_of_int() {
        seq![0].add(a)
    }

    fn has_new_pointsto() {
        (forall|addr: int| mem_protect == MemProtect { read: true })
    }

    fn foo()
        ensures
            forall|x: int| x == x,
    {
    }

    } // verus!
    "###);
}

// We deviate from rustfmt here, so use our own snapshot to check for self-consistency
#[test]
fn verus_match() {
    let file = r#"
verus! {

fn len<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
        List::Cons(_, tl) => {
            let t = 1 + len(*tl);
            t
        },
    }
    fn clone_up_to_view() {
        match self {
            GetLongDestructorNameGetRequest { k } => { GetLongConstructorNameGetRequest{ k: 5 } },
            SetLongDestructorNameSetRequest { k, v } => { SetLongConstructorNameSetRequest { k: k.clone(), v: CMessage::clone_value(v) } },
        }
    }
    match foo {
        foo => bar,
        a_pattern | another_pattern | yet_another_pattern | a_fourth_pattern => { x },
        a_very_very_very_very_very_very_pattern
        | another_very_very_very_very_very_pattern
        | yet_another_very_very_very_pattern
        | a_fourth_very_very_very_pattern => { x },
        a_very_very_very_very_very_very_pattern
        | another_very_very_very_very_very_pattern
        | yet_another_very_very_very_pattern
        | a_fourth_very_very_very_pattern => {
            let x = something_long_and_complicated();
            x
        },
    }
    fn test() {
        match m {
            CMessage::LongConstructorNameGetRequest{..} => old_self.long_function_next_get_request_preconditions(),
        }
        match popped {
            SegmentCreating(sid) if sid == page_id.segment_id => true,
            _ => false,
        }
    }
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn len<T>(l: List<T>) -> nat {
        match l {
            List::Nil => 0,
            List::Cons(_, tl) => 1 + len(*tl),
            List::Cons(_, tl) => {
                let t = 1 + len(*tl);
                t
            },
        }
        fn clone_up_to_view() {
            match self {
                GetLongDestructorNameGetRequest { k } => { GetLongConstructorNameGetRequest { k: 5 } },
                SetLongDestructorNameSetRequest { k, v } => {
                    SetLongConstructorNameSetRequest { k: k.clone(), v: CMessage::clone_value(v) }
                },
            }
        }
        match foo {
            foo => bar,
            a_pattern | another_pattern | yet_another_pattern | a_fourth_pattern => { x },
            a_very_very_very_very_very_very_pattern
            | another_very_very_very_very_very_pattern
            | yet_another_very_very_very_pattern
            | a_fourth_very_very_very_pattern => { x },
            a_very_very_very_very_very_very_pattern
            | another_very_very_very_very_very_pattern
            | yet_another_very_very_very_pattern
            | a_fourth_very_very_very_pattern => {
                let x = something_long_and_complicated();
                x
            },
        }
        fn test() {
            match m {
                CMessage::LongConstructorNameGetRequest {
                    ..
                } => old_self.long_function_next_get_request_preconditions(),
            }
            match popped {
                SegmentCreating(sid) if sid == page_id.segment_id => true,
                _ => false,
            }
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_trait() {
    let file = r#"
verus! {

trait T {
    proof fn my_uninterpreted_fun2(&self, i: int, j: int) -> (r: int)
        requires
            0 <= i < 10,
            0 <= j < 10,
        ensures
            i <= r,
            j <= r,
    ;
}

trait KeyTrait: Sized {
    fn zero_spec() -> Self where Self: std::marker::Sized;
}

spec fn map(f: spec_fn(A) -> B) {
    1
}

spec fn adder(x: int) -> spec_fn(int) -> int {
    |y: int| x + y
}

fn borrow_join<'a>(tracked &'a self) {
    2
}

fn borrow_join2<'a>(tracked &'a self, x: u32) {
    2
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    trait T {
        proof fn my_uninterpreted_fun2(&self, i: int, j: int) -> (r: int)
            requires
                0 <= i < 10,
                0 <= j < 10,
            ensures
                i <= r,
                j <= r,
        ;
    }

    trait KeyTrait: Sized {
        fn zero_spec() -> Self where Self: std::marker::Sized;
    }

    spec fn map(f: spec_fn(A) -> B) {
        1
    }

    spec fn adder(x: int) -> spec_fn(int) -> int {
        |y: int| x + y
    }

    fn borrow_join<'a>(tracked &'a self) {
        2
    }

    fn borrow_join2<'a>(tracked &'a self, x: u32) {
        2
    }

    } // verus!
    "###);
}

#[test]
fn verus_comments() {
    let file = r#"
// External comment 1
/// External comment 2
verus! {

// This comment should stay with the function definition, even though it's parsed as a "prefix" comment
fn clone_value() -> (out: u8) {
}

spec fn my_spec_fun() -> int {
    2
}

enum ReaderState {
    Starting {
        /// Test
        start: LogIdx,
    },
}

/// exec code cannot directly call proof functions or spec functions.
/// However, exec code can contain proof blocks (proof { ... }),
/// which contain proof code.
/// This proof code can call proof functions and spec functions.
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // my_proof_fun(x, y); // not allowed in exec code
    // let u = my_spec_fun(x, y); // not allowed exec code
    proof {
        let u = my_spec_fun(x as int, y as int);  // allowed in proof code
        my_proof_fun(u / 2, y as int);  // allowed in proof code
    }
}

/// Comment 1
/// Comment 2
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // Line comment 1
    // Line comment 2
    proof {
        let u = my_spec_fun(x as int, y as int);  // inline comment 1
        my_proof_fun(u / 2, y as int);  // inline comment 2
    }
}

fn test_ghost_unwrap(x: int)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        y < 100,
{
}

fn test_ghost_unwrap(
    x: u32,
    y: very_very_very_very_very_long_type,
)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        x < 100,
{
}

fn heap_malloc()  // $line_count$Trusted$ 1
-> (t: nat) // $line_count$Trusted$ 2
    requires
        true,
{
    a
}

fn test_my_funs2(
    a: u32, // long comment1 
    b: u32, // long comment2 
) {
}

pub struct SHTKey {
    pub // workaround
        ukey: u64,
}

fn test_my_funs3(
    // exec variable
    a: u32,
    // exec variable
    b: u32,
) {
}

fn my_proof_fun(x: int, y: int)
    requires
        x < 100,  // Very important!
        y < 100,  // This gets parsed as a top-level comment, hence extra newline
    ensures
        sum < 200,  // Definitely want this
        x < 200,  // And this
{
}

#[verifier(external_body)]  // inline comment
pub exec fn foo()
    requires
        a > 5,
{
}


impl AbstractEndPoint {
    fn abstractable() {
        0
    }
    
    // Multiline comment
    // that should stay together
    fn valid_ipv4() {
        true
    }
}

const y: int = 5;

// Comment
const x: int = 5;

impl a {
    // My favorite function
    fn b()
    //
    ;
}

fn try_parse() -> (u: u32)
  //    1
  //    2
  //    3
{
    8
}

pub fn test() {
    if false {
    }// No space between the one character indicating non-inline and the comment
}

fn test() {
    let x = 1;/* inline multi-line comment stays inline */
    let y = 1; /* Long
                  dangling 
                  comment doesn't */
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    // External comment 1
    /// External comment 2
    verus! {

    // This comment should stay with the function definition, even though it's parsed as a "prefix" comment
    fn clone_value() -> (out: u8) {
    }

    spec fn my_spec_fun() -> int {
        2
    }

    enum ReaderState {
        Starting {
            /// Test
            start: LogIdx,
        },
    }

    /// exec code cannot directly call proof functions or spec functions.
    /// However, exec code can contain proof blocks (proof { ... }),
    /// which contain proof code.
    /// This proof code can call proof functions and spec functions.
    fn test_my_funs(x: u32, y: u32)
        requires
            x < 100,
            y < 100,
    {
        // my_proof_fun(x, y); // not allowed in exec code
        // let u = my_spec_fun(x, y); // not allowed exec code
        proof {
            let u = my_spec_fun(x as int, y as int);  // allowed in proof code
            my_proof_fun(u / 2, y as int);  // allowed in proof code
        }
    }

    /// Comment 1
    /// Comment 2
    fn test_my_funs(x: u32, y: u32)
        requires
            x < 100,
            y < 100,
    {
        // Line comment 1
        // Line comment 2
        proof {
            let u = my_spec_fun(x as int, y as int);  // inline comment 1
            my_proof_fun(u / 2, y as int);  // inline comment 2
        }
    }

    fn test_ghost_unwrap(x: int)  // unwrap so that y has typ u32, not Ghost<u32>
        requires
            y < 100,
    {
    }

    fn test_ghost_unwrap(
        x: u32,
        y: very_very_very_very_very_long_type,
    )  // unwrap so that y has typ u32, not Ghost<u32>
        requires
            x < 100,
    {
    }

    fn heap_malloc()  // $line_count$Trusted$ 1
     -> (t: nat)  // $line_count$Trusted$ 2
        requires
            true,
    {
        a
    }

    fn test_my_funs2(
        a: u32,  // long comment1
        b: u32,  // long comment2
    ) {
    }

    pub struct SHTKey {
        pub  // workaround
         ukey: u64,
    }

    fn test_my_funs3(
        // exec variable
        a: u32,
        // exec variable
        b: u32,
    ) {
    }

    fn my_proof_fun(x: int, y: int)
        requires
            x < 100,  // Very important!
            y < 100,  // This gets parsed as a top-level comment, hence extra newline

        ensures
            sum < 200,  // Definitely want this
            x < 200,  // And this
    {
    }

    #[verifier(external_body)]  // inline comment
    pub exec fn foo()
        requires
            a > 5,
    {
    }

    impl AbstractEndPoint {
        fn abstractable() {
            0
        }

        // Multiline comment
        // that should stay together
        fn valid_ipv4() {
            true
        }
    }

    const y: int = 5;

    // Comment
    const x: int = 5;

    impl a {
        // My favorite function
        fn b()
        //
        ;
    }

    fn try_parse() -> (u: u32)
    //    1
    //    2
    //    3
    {
        8
    }

    pub fn test() {
        if false {
        }  // No space between the one character indicating non-inline and the comment

    }

    fn test() {
        let x = 1;  /* inline multi-line comment stays inline */
        let y = 1;
        /* Long
                      dangling
                      comment doesn't */
    }

    } // verus!
    "###);
}

#[test]
fn verus_comment_prefix_suffix() {
    let file = r#"
verus! {
/*
 This comment shouldn't absorbs he newline that separates it from the struct
 */
struct Constants {
    b: int,
}
/*
 This comment should have some space between it and the struct
 */
} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    /*
     This comment shouldn't absorbs he newline that separates it from the struct
     */
    struct Constants {
        b: int,
    }

    /*
     This comment should have some space between it and the struct
     */
    } // verus!
    "###);
}

#[test]
fn verus_keyword_prefixed_identifier_parsing() {
    let file = r#"
verus! {
pub exec fn foo(mut_state: &mut Blah, selfie_stick: SelfieStick) {
    let a = { b(&mut_state.c) };
    bar(selfie_stick);
}
} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub exec fn foo(mut_state: &mut Blah, selfie_stick: SelfieStick) {
        let a = { b(&mut_state.c) };
        bar(selfie_stick);
    }

    } // verus!
    "###);
}

#[test]
fn verus_impl_bounds() {
    let file = r#"
verus! {
struct StrictlyOrderedVec<K: KeyTrait> {
    a: int
}

struct DelegationMap<#[verifier(maybe_negative)] K: KeyTrait + VerusClone> {
    b: int
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    fn view() -> Map<K,AbstractEndPoint> {
        c
    }
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
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
    "###);
}

#[test]
fn verus_closures() {
    let file = r#"
verus! {

fn test() {
    let lambda = |key| -> (b: bool) { true };
    let lambda = |key| -> (b: bool) ensures b == true { true };
    let op = |x: i32| -> (y: i32) requires x < 100000 ensures y > x { x + 1 };
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let lambda = |key| -> (b: bool) { true };
        let lambda = |key| -> (b: bool)
            ensures
                b == true,
            { true };
        let op = |x: i32| -> (y: i32)
            requires
                x < 100000,
            ensures
                y > x,
            { x + 1 };
    }

    } // verus!
    "###);
}

#[test]
fn verus_loops() {
    let file = r#"
verus! {

pub fn clone_vec_u8() {
    let i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            i == out.len(),
            forall |j| #![auto] 0 <= j < i  ==> out@[j] == v@[j],
        ensures
            i > 0,
        decreases
            72,
    {
        i = i + 1;
    }
}

fn test() {
    loop
        invariant
            x > 0,
    {
        x += 1;
    }
}

fn test() {
    loop
        invariant
            false,
        invariant_ensures
            true,
        ensures
            next_idx + count <= 512,
    {
        x
    }
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub fn clone_vec_u8() {
        let i = 0;
        while i < v.len()
            invariant
                i <= v.len(),
                i == out.len(),
                forall|j| #![auto] 0 <= j < i ==> out@[j] == v@[j],
            ensures
                i > 0,
            decreases 72,
        {
            i = i + 1;
        }
    }

    fn test() {
        loop
            invariant
                x > 0,
        {
            x += 1;
        }
    }

    fn test() {
        loop
            invariant
                false,
            invariant_ensures
                true,
            ensures
                next_idx + count <= 512,
        {
            x
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_lifetimes() {
    let file = r#"
verus! {

fn get<'a>(&'a self, k: &K) -> (o: Option<&'a V>) {
    a
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn get<'a>(&'a self, k: &K) -> (o: Option<&'a V>) {
        a
    }

    } // verus!
    "###);
}

#[test]
fn verus_statements() {
    let file = r#"
verus! {

fn test(thread_token: &mut bool) {
    thread_token = _thread_token;
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test(thread_token: &mut bool) {
        thread_token = _thread_token;
    }

    } // verus!
    "###);
}

#[test]
fn verus_statics() {
    let file = r#"
verus! {

exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

exec static LAZY_X: Lazy<X> ensures LAZY_X.wf() { Lazy::<X>::new() }

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

    exec static LAZY_X: Lazy<X>
        ensures
            LAZY_X.wf(),
    {
        Lazy::<X>::new()
    }

    } // verus!
    "###);
}

#[test]
fn verus_requires_clauses_confusable_with_generics() {
    // Regression test for https://github.com/jaybosamiya/verusfmt/issues/19
    let file = r#"
verus! {

fn test()
    requires i < 0, len > 0,
{
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test()
        requires
            i < 0,
            len > 0,
    {
    }

    } // verus!
    "###);
}

#[test]
fn verus_quantifier_and_bulleted_expr_precedence() {
    // Regression test for https://github.com/jaybosamiya/verusfmt/issues/25
    let file = r#"  verus! { spec fn foo() { &&& forall|x:int| f &&& g } }  "#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    spec fn foo() {
        &&& forall|x: int| f
        &&& g
    }

    } // verus!
    "###);
}

#[test]
fn verus_bulleted_expr_comment_handling() {
    let file = r#"
verus! {
fn foo() {
    // these should stay together
    &&& x
    &&& y
    // xy
    &&& xy
    // zzz
    &&& z
}
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn foo() {
        // these should stay together
        &&& x
        &&& y
        // xy
        &&& xy
        // zzz
        &&& z
    }

    } // verus!
    "###);
}

#[test]
fn verus_skip_leaves_code_unchanged() {
    let file = r#"  verus! { spec fn foo() { 1 + 2 } #[verusfmt::skip]  spec fn bar() { 1 + 2 }

fn baz() {
    #[verusfmt::skip]
    let x = {
        a &&
        b ||
            c
    };
    let y = {
        a &&
        b ||
            c
    };
}

 }  "#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    spec fn foo() {
        1 + 2
    }

    #[verusfmt::skip]
    spec fn bar() { 1 + 2 }

    fn baz() {
        #[verusfmt::skip]
        let x = {
            a &&
            b ||
                c
        };
        let y = { a && b || c };
    }

    } // verus!
    "###);
}

#[test]
fn verus_arrow_expr() {
    let file = r#"
verus! {

proof fn uses_arrow_matches_1(t: ThisOrThat)
    requires
        t is That ==> t->v == 3,
        t is This ==> t->0 == 4,
{
}

}

"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn uses_arrow_matches_1(t: ThisOrThat)
        requires
            t is That ==> t->v == 3,
            t is This ==> t->0 == 4,
    {
    }

    } // verus!
    "###);
}

#[test]
fn verus_matches_expr() {
    let file = r#"
verus! {

proof fn uses_arrow_matches_1(t: ThisOrThat) { assert(t matches ThisOrThat::This(k) ==> k == 4);
    assert(t matches ThisOrThat::That { v } ==> v == 3); assert({ &&& t matches ThisOrThat::This(k)
    &&& baz }); }

}

"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn uses_arrow_matches_1(t: ThisOrThat) {
        assert(t matches ThisOrThat::This(k) ==> k == 4);
        assert(t matches ThisOrThat::That { v } ==> v == 3);
        assert({
            &&& t matches ThisOrThat::This(k)
            &&& baz
        });
    }

    } // verus!
    "###);
}

#[test]
fn verus_range_operator() {
    let file = r#"
verus! {

fn foo() { for i in 0..(10 + 5) {

} }

}

"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn foo() {
        for i in 0..(10 + 5) {
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_for_loops() {
    let file = r#"
verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let ghost v1 = v@;
    for n in 0..(length / 2)
        invariant
            length == v.len(),
            forall|i: int| 0 <= i < n ==> v[i] == v1[length - i - 1],
            forall|i: int| 0 <= i < n ==> v1[i] == v[length - i - 1],
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i] == v1[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
    }
}

fn test() {
    for x in iter: 0..end
        invariant
            end == 10,
    {
        n += 3;
    }
    let x = 2;
    for x in iter: vec_iter_copy(v)
        invariant
            b <==> (forall|i: int| 0 <= i < iter.cur ==> v[i] > 0),
    {
        b = b && x > 0;
    }
    let y = 3;
    for x in iter: 0..({
        let z = end;
        non_spec();
        z
    })
        invariant
            n == iter.cur * 3,
            end == 10,
    {
        n += 3;
        end = end + 0;  // causes end to be non-constant
    }
}

}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn reverse(v: &mut Vec<u64>)
        ensures
            v.len() == old(v).len(),
            forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
    {
        let length = v.len();
        let ghost v1 = v@;
        for n in 0..(length / 2)
            invariant
                length == v.len(),
                forall|i: int| 0 <= i < n ==> v[i] == v1[length - i - 1],
                forall|i: int| 0 <= i < n ==> v1[i] == v[length - i - 1],
                forall|i: int| n <= i && i + n < length ==> #[trigger] v[i] == v1[i],
        {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);
        }
    }

    fn test() {
        for x in iter: 0..end
            invariant
                end == 10,
        {
            n += 3;
        }
        let x = 2;
        for x in iter: vec_iter_copy(v)
            invariant
                b <==> (forall|i: int| 0 <= i < iter.cur ==> v[i] > 0),
        {
            b = b && x > 0;
        }
        let y = 3;
        for x in iter: 0..({
            let z = end;
            non_spec();
            z
        })
            invariant
                n == iter.cur * 3,
                end == 10,
        {
            n += 3;
            end = end + 0;  // causes end to be non-constant
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_invariant_except_break() {
    let file = r#"
verus!{
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let mut i: i8 = 0;
        loop
            invariant
                i <= 9,
            invariant_ensures
                0 <= i <= 10,
            invariant_except_break
                i <= 9,
            invariant
                0 <= i <= 10,
            ensures
                1 <= i,
        {
            assert(i <= 9);
            i = i + 1;
            if i == 10 {
                break ;
            }
        }
        assert(1 <= i <= 10);
    }

    } // verus!
    "###);
}

#[test]
fn verus_broadcast_proof() {
    let file = r#"
verus!{
    broadcast proof fn property() { }
    pub broadcast proof fn property() { }
} // verus!
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    broadcast proof fn property() {
    }

    pub broadcast proof fn property() {
    }

    } // verus!
    "###);
}

#[test]
fn verus_broadcast_use() {
    let file = r#"
verus! {
mod ring {
    use builtin::*;

    pub struct Ring {
        pub i: u64,
    }

    impl Ring {
        pub closed spec fn inv(&self) -> bool {
            self.i < 10
        }

        pub closed spec fn spec_succ(&self) -> Ring {
            Ring { i: if self.i == 9 { 0 } else { (self.i + 1) as u64 } }
        }

        pub closed spec fn spec_prev(&self) -> Ring {
            Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as u64 } }
        }

        pub broadcast proof fn spec_succ_ensures(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.spec_succ()).spec_prev() == p
        { }

        pub broadcast proof fn spec_prev_ensures(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.spec_prev()).spec_succ() == p
        { }

        pub    broadcast    group    properties {
        Ring::spec_succ_ensures,
                Ring::spec_prev_ensures,
        }
    }

    #[verifier::prune_unless_this_module_is_used]
    pub    broadcast    group    properties {
    Ring::spec_succ_ensures,
            Ring::spec_prev_ensures,
    }
}

mod m2 {
    use builtin::*;
    use crate::ring::*;

    fn t2(p: Ring) requires p.inv() {
           broadcast    use     Ring::properties;
        assert(p.spec_succ().spec_prev() == p);
        assert(p.spec_prev().spec_succ() == p);
    }
}

mod m3 {
    use builtin::*;
    use crate::ring::*;

        broadcast   use    Ring::properties;
        
        fn a() { }
}

mod m4 {
    use builtin::*;
    use crate::ring::*;

        broadcast   use    
                    Ring::spec_succ_ensures,
            Ring::spec_prev_ensures;
}

mod m5 {
broadcast use
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms,
;
broadcast use
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms;
broadcast use super::raw_ptr::group_raw_ptr_axioms;
broadcast use super::set_lib::group_set_lib_axioms;
broadcast use super::set::group_set_axioms;
broadcast use {
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms};
broadcast use {
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms,};
broadcast use {super::set::group_set_axioms};
broadcast use {super::set::group_set_axioms,};
}

} // verus!
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    mod ring {
        use builtin::*;

        pub struct Ring {
            pub i: u64,
        }

        impl Ring {
            pub closed spec fn inv(&self) -> bool {
                self.i < 10
            }

            pub closed spec fn spec_succ(&self) -> Ring {
                Ring {
                    i: if self.i == 9 {
                        0
                    } else {
                        (self.i + 1) as u64
                    },
                }
            }

            pub closed spec fn spec_prev(&self) -> Ring {
                Ring {
                    i: if self.i == 0 {
                        9
                    } else {
                        (self.i - 1) as u64
                    },
                }
            }

            pub broadcast proof fn spec_succ_ensures(p: Ring)
                requires
                    p.inv(),
                ensures
                    p.inv() && (#[trigger] p.spec_succ()).spec_prev() == p,
            {
            }

            pub broadcast proof fn spec_prev_ensures(p: Ring)
                requires
                    p.inv(),
                ensures
                    p.inv() && (#[trigger] p.spec_prev()).spec_succ() == p,
            {
            }

            pub broadcast group properties {
                Ring::spec_succ_ensures,
                Ring::spec_prev_ensures,
            }
        }

        #[verifier::prune_unless_this_module_is_used]
        pub broadcast group properties {
            Ring::spec_succ_ensures,
            Ring::spec_prev_ensures,
        }

    }

    mod m2 {
        use builtin::*;
        use crate::ring::*;

        fn t2(p: Ring)
            requires
                p.inv(),
        {
            broadcast use Ring::properties;

            assert(p.spec_succ().spec_prev() == p);
            assert(p.spec_prev().spec_succ() == p);
        }

    }

    mod m3 {
        use builtin::*;
        use crate::ring::*;

        broadcast use Ring::properties;

        fn a() {
        }

    }

    mod m4 {
        use builtin::*;
        use crate::ring::*;

        broadcast use Ring::spec_succ_ensures, Ring::spec_prev_ensures;

    }

    mod m5 {
        broadcast use
            super::raw_ptr::group_raw_ptr_axioms,
            super::set_lib::group_set_lib_axioms,
            super::set::group_set_axioms,
        ;
        broadcast use
            super::raw_ptr::group_raw_ptr_axioms,
            super::set_lib::group_set_lib_axioms,
            super::set::group_set_axioms,
        ;
        broadcast use super::raw_ptr::group_raw_ptr_axioms;
        broadcast use super::set_lib::group_set_lib_axioms;
        broadcast use super::set::group_set_axioms;
        broadcast use {
            super::raw_ptr::group_raw_ptr_axioms,
            super::set_lib::group_set_lib_axioms,
            super::set::group_set_axioms,
        };
        broadcast use {
            super::raw_ptr::group_raw_ptr_axioms,
            super::set_lib::group_set_lib_axioms,
            super::set::group_set_axioms,
        };
        broadcast use super::set::group_set_axioms;
        broadcast use super::set::group_set_axioms;

    }

    } // verus!
    ");
}

#[test]
fn verus_broadcast_uses_trailing_newline() {
    let file = r###"
verus! {
proof fn to_multiset_build<A>(s: Seq<A>, a: A)
    ensures
        s.push(a).to_multiset() =~= s.to_multiset().insert(a),
    decreases s.len(),
{
    broadcast use crate::multiset::multiset_axioms;
    /* xx */
    broadcast use crate::multiset::multiset_stuffs;
    // xx
    broadcast use crate::useful;
    broadcast use crate::moreuseful;
    if s.len() == 0 {
    }
}
} // verus!
"###;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn to_multiset_build<A>(s: Seq<A>, a: A)
        ensures
            s.push(a).to_multiset() =~= s.to_multiset().insert(a),
        decreases s.len(),
    {
        broadcast use crate::multiset::multiset_axioms;
        /* xx */
        broadcast use crate::multiset::multiset_stuffs;
        // xx
        broadcast use crate::useful;
        broadcast use crate::moreuseful;

        if s.len() == 0 {
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_unwind() {
    let file = r###"
verus! {
proof fn a()
    no_unwind
{
}

proof fn b()
    no_unwind when x >= 0
{
}

proof fn c()
    ensures true, no_unwind when true
{
}
} // verus!
"###;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn a()
        no_unwind
    {
    }

    proof fn b()
        no_unwind when x >= 0
    {
    }

    proof fn c()
        ensures
            true,
        no_unwind when true
    {
    }

    } // verus!
    "###);
}

#[test]
fn verus_generic_arg_binding() {
    let file = r###"
verus! {
pub trait Foo<T>: View<V = Seq<T>> {
}
} // verus!
"###;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub trait Foo<T>: View<V = Seq<T>> {

    }

    } // verus!
    "###);
}

#[test]
fn verus_calc_formatting() {
    let file = r###"
verus! {
fn foo() {
    calc! {
        (==)
        x; {}
        y; {}
        a; (==) {
            assert(foo == bar);
        }
        b;
    }
}
fn bar() {
    calc! {
        (<=)
        x; /* x*/ {}
        y; { /*y*/ }
// t
        a; (==) {
// u
            assert(foo == bar);
        }
        b;
// v
    }
}
}
"###;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn foo() {
        calc! {
            (==)
            x; {}
            y; {}
            a; (==) {
                assert(foo == bar);
            }
            b;
        }
    }

    fn bar() {
        calc! {
            (<=)
            x;   /* x*/
            {}
            y; {  /*y*/
            }
            // t
            a; (==) {
                // u
                assert(foo == bar);
            }
            b;
            // v
        }
    }

    } // verus!
    "###);
}

#[test]
fn verus_const_arg() {
    let file = r#"
verus! {

fn foo(arg: ConstBytes<2>) -> (res: ConstBytes<4>) {
    let x: ConstBytes<3> = bar();
    baz();
}
    
}

"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn foo(arg: ConstBytes<2>) -> (res: ConstBytes<4>) {
        let x: ConstBytes<3> = bar();
        baz();
    }

    } // verus!
    "###);
}

#[test]
fn verus_seq_macro() {
    let file = r#"
verus! {
proof fn f() {
    let s = seq![
        0x00,        0x00,        0x00,        0x00,        0x00,        0x00,
        0x00,        0x00,        0x00,        0x00,
        0x00,        0x00,        0x00,
        0x00,        0x00,        0x00,
    ];
    let s = seq![
        0x00,       0x00,
        0x00, 0x00,
    ];
}
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn f() {
        let s = seq![
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
        ];
        let s = seq![0x00, 0x00, 0x00, 0x00];
    }

    } // verus!
    "###);
}

#[test]
fn verus_empty_fn_quanlifier_expr() {
    let file = r#"
verus! {
    fn test0()
        requires
            i = 0
        ensures
    {}
    fn test1()
        requires
            i = 0
        ensures
        recommends
    {}
    fn test2()
        requires
        ensures
            i = 0
    {}
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test0()
        requires
            i = 0,
        ensures
    {
    }

    fn test1()
        requires
            i = 0,
        ensures
        recommends
    {
    }

    fn test2()
        requires
        ensures
            i = 0,
    {
    }

    } // verus!
    "###);
}

#[test]
fn verus_broadcast_group_with_attributes() {
    let file = r#"
verus! {
#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_hash_axioms { axiom_hash_map_contains_deref_key,
  #[cfg(feature = "alloc")]
    axiom_hash_map_contains_box,
    axiom_hash_map_maps_deref_key_to_value,
  #[cfg(feature = "alloc")]
    #[some_other_attribute]
    axiom_hash_map_maps_box_key_to_value,
   axiom_primitive_types_have_deterministic_hash,
       axiom_random_state_conforms_to_build_hasher_model,
     axiom_spec_hash_map_len,
}
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    #[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
    pub broadcast group group_hash_axioms {
        axiom_hash_map_contains_deref_key,
        #[cfg(feature = "alloc")]
        axiom_hash_map_contains_box,
        axiom_hash_map_maps_deref_key_to_value,
        #[cfg(feature = "alloc")]
        #[some_other_attribute]
        axiom_hash_map_maps_box_key_to_value,
        axiom_primitive_types_have_deterministic_hash,
        axiom_random_state_conforms_to_build_hasher_model,
        axiom_spec_hash_map_len,
    }

    } // verus!
    "###);
}

#[test]
fn verus_support_separating_logical_blocks() {
    let file = r#"
verus! {

fn fff() {
    reveal(f1);  // reveal f1's definition just inside this block


    reveal(f1);  // reveal f1's definition just inside this block

    foo;

    bar;
    baz;
}

pub fn foo() {
    // this should stay stuck to the `a`
    assert(a) by {
        // whatever
    }
    // this should also stay stuck to the `a`
    // and so should this line

    // but this line
    // and this line should stick to the `b`
    b;
    // and this comment should also stick to the `b`

    // similarly `c`
    c;
    // `c` again

    // and an empty comment stands alone

    // similarly `d`
    d;
    // `d` again

    // and finally, `d`
    assert(d) by {
        // whatever
    }
    // well, now done with `d`
}

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn fff() {
        reveal(f1);  // reveal f1's definition just inside this block

        reveal(f1);  // reveal f1's definition just inside this block

        foo;

        bar;
        baz;
    }

    pub fn foo() {
        // this should stay stuck to the `a`
        assert(a) by {
            // whatever
        }
        // this should also stay stuck to the `a`
        // and so should this line

        // but this line
        // and this line should stick to the `b`
        b;
        // and this comment should also stick to the `b`

        // similarly `c`
        c;
        // `c` again

        // and an empty comment stands alone

        // similarly `d`
        d;
        // `d` again

        // and finally, `d`
        assert(d) by {
            // whatever
        }
        // well, now done with `d`
    }

    } // verus!
    "###);
}

#[test]
fn verus_const_generics() {
    // Regression test for https://github.com/verus-lang/verusfmt/issues/90
    let file = r#"
verus! {
       pub fn f<const N: u64>() -> u64 { N }
       pub fn g<const N: u64, const O: u64>() -> u64 { N }
 fn main() { f::<123>(); g::<123, 456>(); }
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub fn f<const N: u64>() -> u64 {
        N
    }

    pub fn g<const N: u64, const O: u64>() -> u64 {
        N
    }

    fn main() {
        f::<123>();
        g::<123, 456>();
    }

    } // verus!
    "###);
}

#[test]
fn verus_support_opens_invariants() {
    // Regression test for https://github.com/verus-lang/verusfmt/issues/91
    let file = r#"
verus! {
    proof fn a() opens_invariants none {}
    proof fn f() opens_invariants [ 123u8 ] {}
    proof fn g() opens_invariants [ 123u8, 456u8 ] {}
    proof fn z() opens_invariants any {}
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    proof fn a()
        opens_invariants none
    {
    }

    proof fn f()
        opens_invariants [123u8]
    {
    }

    proof fn g()
        opens_invariants [123u8, 456u8]
    {
    }

    proof fn z()
        opens_invariants any
    {
    }

    } // verus!
    "###)
}

#[test]
fn verus_handling_of_docstrings() {
    // Regression test for https://github.com/verus-lang/verusfmt/issues/102
    let file = r#"
verus! {

some_macro!{
}

/// abc
fn foo() {
}

} // verus!
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    some_macro!{
    }

    /// abc
    fn foo() {
    }

    } // verus!
    "###)
}

#[test]
fn verus_assume_specification() {
    let file = r#"
verus! {

pub assume_specification<T, const N: usize> [ <[T; N]>::as_slice ](ar: &[T; N]) -> (out: &[T])
    ensures
        ar@ == out@;

pub assume_specification<Key, Value, S>[HashMap::<Key, Value, S>::insert](
    m: &mut HashMap<Key, Value, S>,
    k: Key,
    v: Value,
) -> (result: Option<Value>) where Key: Eq + Hash, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& m@ == old(m)@.insert(k, v)
            &&& match result {
                Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
                None => !old(m)@.contains_key(k),
            }
        };

assume_specification[char::REPLACEMENT_CHARACTER] -> (c: char)
    ensures
        c != '7',
;

assume_specification[C] -> u8
    returns
        7u8,
;
} // verus!
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub assume_specification<T, const N: usize>[ <[T; N]>::as_slice ](ar: &[T; N]) -> (out: &[T])
        ensures
            ar@ == out@,
    ;

    pub assume_specification<Key, Value, S>[ HashMap::<Key, Value, S>::insert ](
        m: &mut HashMap<Key, Value, S>,
        k: Key,
        v: Value,
    ) -> (result: Option<Value>) where Key: Eq + Hash, S: BuildHasher
        ensures
            obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
                &&& m@ == old(m)@.insert(k, v)
                &&& match result {
                    Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
                    None => !old(m)@.contains_key(k),
                }
            },
    ;

    assume_specification[ char::REPLACEMENT_CHARACTER ] -> (c: char)
        ensures
            c != '7',
    ;

    assume_specification[ C ] -> u8
        returns
            7u8,
    ;

    } // verus!
    "###)
}

#[test]
fn verus_support_returns_clause() {
    let file = r#"
verus!{
    fn test(b: bool) -> (c: bool)
        requires x,
        ensures c == !b,
        returns !b,
    {
    }

    fn test2(b: bool) -> (c: bool)
        requires x,
        ensures c == !b,
        returns !b
    {
    }

    fn test3(b: bool) -> (c: bool)
        requires x,
        ensures c == !b,
        returns !b
        opens_invariants any
    {
    }

    fn test4(b: bool) -> (c: bool)
        requires x,
        ensures c == !b,
        returns !b,
        opens_invariants any
    {
    }
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    fn test(b: bool) -> (c: bool)
        requires
            x,
        ensures
            c == !b,
        returns
            !b,
    {
    }

    fn test2(b: bool) -> (c: bool)
        requires
            x,
        ensures
            c == !b,
        returns
            !b,
    {
    }

    fn test3(b: bool) -> (c: bool)
        requires
            x,
        ensures
            c == !b,
        returns
            !b,
        opens_invariants any
    {
    }

    fn test4(b: bool) -> (c: bool)
        requires
            x,
        ensures
            c == !b,
        returns
            !b,
        opens_invariants any
    {
    }

    } // verus!
    ")
}

#[test]
fn verus_support_is_has_notis_nothas() {
    let file = r#"
verus!{
proof fn uses_spec_has(s: Set<int>)
    requires
        s has 3,
        s !has 4,
{
}
proof fn uses_spec_is(t: ThisOrThat)
    requires
        t is This,
        t !is That
{
}
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    proof fn uses_spec_has(s: Set<int>)
        requires
            s has 3,
            s !has 4,
    {
    }

    proof fn uses_spec_is(t: ThisOrThat)
        requires
            t is This,
            t !is That,
    {
    }

    } // verus!
    ")
}

#[test]
fn verus_uninterp_spec_functions() {
    let file = r#"
verus! { pub uninterp   spec fn bar() -> bool   ; }
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    pub uninterp spec fn bar() -> bool;

    } // verus!
    ")
}

#[test]
fn verus_axiom_functions() {
    let file = r#"
verus! { pub axiom fn foo(x: u8) requires x == 5; }
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    pub axiom fn foo(x: u8)
        requires
            x == 5,
    ;

    } // verus!
    ")
}

#[test]
fn verus_visibility_qualifiers_for_open() {
    let file = r#"
verus! {
pub open  (crate) spec fn test() {}
pub open  (   in   foo  ) spec fn test2() {}
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    pub open(crate) spec fn test() {
    }

    pub open(in foo) spec fn test2() {
    }

    } // verus!
    ")
}

#[test]
fn verus_opens_invariants_set() {
    let file = r#"
verus! {
    proof fn foo1() opens_invariants bar();
    proof fn foo2() opens_invariants baz;
    proof fn foo3() opens_invariants bar() {}
    proof fn foo4() opens_invariants baz {}
    proof fn foo5() opens_invariants Set::<int>::empty() {}
    proof fn foo6() opens_invariants { let a = Set::<int>::empty(); let b = a.insert(c); b } {}
}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    proof fn foo1()
        opens_invariants bar()
    ;

    proof fn foo2()
        opens_invariants baz
    ;

    proof fn foo3()
        opens_invariants bar()
    {
    }

    proof fn foo4()
        opens_invariants baz
    {
    }

    proof fn foo5()
        opens_invariants Set::<int>::empty()
    {
    }

    proof fn foo6()
        opens_invariants {
            let a = Set::<int>::empty();
            let b = a.insert(c);
            b
        }
    {
    }

    } // verus!
    ")
}

#[test]
fn verus_proof_closures() {
    let file = r#"
verus! {

proof fn testfn() { let tracked f = proof_fn |y: u64| -> (z: u64) requires y == 2, ensures z == 2, { y }; assert(f.requires((2,))); assert(!f.ensures((2,), 3)); let t = f(2); assert(t == 2); }

proof fn helper(tracked f: proof_fn(y: u64) -> u64) requires f.requires((2,)), forall|z: u64| f.ensures((2,), z) ==> z == 2, { let t = f(2); assert(t == 2); }

proof fn testfn() { let tracked f = proof_fn |y: u64| -> (z: u64) requires y == 2, ensures z == 2, { y }; helper(f); }

proof fn test() { let tracked f = proof_fn[Mut, Copy, Send, ReqEns<foo>, Sync]|y: u64| -> (z: u64){ y }; }

proof fn foo(x: proof_fn(a: u32) -> u64, y: proof_fn[Send](a: u32) -> u64) {}

}
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    proof fn testfn() {
        let tracked f = proof_fn |y: u64| -> (z: u64)
            requires
                y == 2,
            ensures
                z == 2,
            { y };
        assert(f.requires((2,)));
        assert(!f.ensures((2,), 3));
        let t = f(2);
        assert(t == 2);
    }

    proof fn helper(tracked f: proof_fn(y: u64) -> u64)
        requires
            f.requires((2,)),
            forall|z: u64| f.ensures((2,), z) ==> z == 2,
    {
        let t = f(2);
        assert(t == 2);
    }

    proof fn testfn() {
        let tracked f = proof_fn |y: u64| -> (z: u64)
            requires
                y == 2,
            ensures
                z == 2,
            { y };
        helper(f);
    }

    proof fn test() {
        let tracked f = proof_fn[Mut, Copy, Send, ReqEns<foo>, Sync] |y: u64| -> (z: u64) { y };
    }

    proof fn foo(x: proof_fn(a: u32) -> u64, y: proof_fn[Send](a: u32) -> u64) {
    }

    } // verus!
    ")
}

#[test]
fn at_patterns() {
    // Regression test for https://github.com/verus-lang/verusfmt/issues/137
    let file = r#"
verus!{ fn foo(e: E) -> u64 { match e { v@E::C1{x}=>x } } }
"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    fn foo(e: E) -> u64 {
        match e {
            v @ E::C1 { x } => x,
        }
    }

    } // verus!
    ")
}

#[test]
fn verus_default_ensures() {
    let file = r#"verus!{
fn foo(i: u32) -> (r: u32) requires 0 <= i < 10 ensures i <= r default_ensures i == r { }
fn bar(i: u32) -> (r: u32) default_ensures i == r requires 0 <= i < 10 ensures i <= r;
fn baz(i: bool) default_ensures i {}
}"#;
    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    verus! {

    fn foo(i: u32) -> (r: u32)
        requires
            0 <= i < 10,
        ensures
            i <= r,
        default_ensures
            i == r,
    {
    }

    fn bar(i: u32) -> (r: u32)
        default_ensures
            i == r,
        requires
            0 <= i < 10,
        ensures
            i <= r,
    ;

    fn baz(i: bool)
        default_ensures
            i,
    {
    }

    } // verus!
    ")
}

#[test]
fn verus_macro_inside_comment() {
    // Regression test for https://github.com/verus-lang/verusfmt/issues/146
    let file = r#"
fn main() {}

// verus!{
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r"
    fn main() {}

    // verus!{
    ");
}

#[test]
fn verus_compound_assignment_operators() {
    let file = r#"
verus! {

fn test() {
    let mut x = 0;
    x |= 5;
    x &= 3;
    x ^= 7;
}

fn test_array() {
    let mut words = [0u64; 4];
    words[0] |= 5;
    words[1] &= 3;
    words[2] ^= 7;
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let mut x = 0;
        x |= 5;
        x &= 3;
        x ^= 7;
    }

    fn test_array() {
        let mut words = [0u64;4];
        words[0] |= 5;
        words[1] &= 3;
        words[2] ^= 7;
    }

    } // verus!
    "###);
}

#[test]
fn verus_binary_and_octal_literals() {
    let file = r#"
verus! {

fn test() {
    let a = 0x7F;
    let b = 0o177;
    let c = 127;
    let d = 0b0111_1111;
    let mut s = [0u8; 32];
    s[31] &= 0b0111_1111;
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let a = 0x7F;
        let b = 0o177;
        let c = 127;
        let d = 0b0111_1111;
        let mut s = [0u8;32];
        s[31] &= 0b0111_1111;
    }

    } // verus!
    "###);
}

#[test]
fn verus_numeric_literals_with_underscores() {
    let file = r#"
verus! {

fn test() {
    let a = 1_usize;
    let b = 100_000u64;
    let c = 1_000_000_u32;
    let d = 42_;
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let a = 1_usize;
        let b = 100_000u64;
        let c = 1_000_000_u32;
        let d = 42_;
    }

    } // verus!
    "###);
}

#[test]
fn verus_underscore_digit_identifiers_with_dot_access() {
    let file = r#"
verus! {

fn test() {
    let _1 = MyStruct{};
    let _10 = _1.method();
    let _123 = _10.field;
    let x = _123.another_method();
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    fn test() {
        let _1 = MyStruct {  };
        let _10 = _1.method();
        let _123 = _10.field;
        let x = _123.another_method();
    }

    } // verus!
    "###);
}

#[test]
fn real_literals() {
    let file = r#"
use vstd::prelude::*;

verus! {
  proof fn hi(){
    let car: real = 0.5;
    assert(0real <= car && car < 1real);
  }
  
  proof fn test_real_literals(){
    // Integer-style real literals
    let a: real = 0real;
    let b: real = 123real;
    let c: real = 0xFFreal;
    let d: real = 0o77real;
    let e: real = 0b1010real;
    
    // Decimal-style real literals
    let f: real = 0.5real;
    let g: real = 123.456real;
    let h: real = 0.0real;
    
    // Exponential-style real literals (integer base)
    let i: real = 1e2real;
    let j: real = 2E-3real;
    
    // Use in expressions
    assert(0real <= a && a < 1real);
    assert(0.5real < 1.0real);
  }
}

fn main() {}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    use vstd::prelude::*;

    verus! {

    proof fn hi() {
        let car: real = 0.5;
        assert(0real <= car && car < 1real);
    }

    proof fn test_real_literals() {
        // Integer-style real literals
        let a: real = 0real;
        let b: real = 123real;
        let c: real = 0xFFreal;
        let d: real = 0o77real;
        let e: real = 0b1010real;

        // Decimal-style real literals
        let f: real = 0.5real;
        let g: real = 123.456real;
        let h: real = 0.0real;

        // Exponential-style real literals (integer base)
        let i: real = 1e2real;
        let j: real = 2E-3real;

        // Use in expressions
        assert(0real <= a && a < 1real);
        assert(0.5real < 1.0real);
    }

    } // verus!
    fn main() {}
    "###);
}

#[test]
fn raw_identifiers() {
    let file = r#"
verus! {

pub struct FooImpl {
    pub r#type: u64,
}

pub assume_specification[FooImpl::r#type](x: &FooImpl) -> (res: u64)
    ensures res@ == x.r#type
;

pub fn test_raw_identifiers() {
    let r#type = 42;
    let r#match = true;
    let foo = FooImpl { r#type: 10 };
    assert(foo.r#type == 10);
}

}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    pub struct FooImpl {
        pub r#type: u64,
    }

    pub assume_specification[ FooImpl::r#type ](x: &FooImpl) -> (res: u64)
        ensures
            res@ == x.r#type,
    ;

    pub fn test_raw_identifiers() {
        let r#type = 42;
        let r#match = true;
        let foo = FooImpl { r#type: 10 };
        assert(foo.r#type == 10);
    }

    } // verus!
    "###);
}
