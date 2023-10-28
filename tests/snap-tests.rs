use verusfmt::parse_and_format;
use insta::assert_snapshot;

/// Tests of Verus-specific formatting

// We use insta tests (http://insta.rs) to manage the correct answers.
// See README.md for details on how to run and update these tests.

#[test]
fn verus_functions() {
    let file = r#"
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

"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
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

    "###);
}

#[test]
fn verus_assert_by() {
    let file = r#"
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
    assert(forall|x: int| x < 10 implies x < 11) by {
        reveal(f1);
    };
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
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
        assert(forall|x: int| x < 10 implies x < 11) by {
            reveal(f1);
        };
    }
    "###);
}

// We deviate from rustfmt here, so use our own snapshot to check for self-consistency
#[test]
fn verus_expr() {
    let file = r#"
pub fn test_function(x: int, y: int) -> u32 {
    let very_very_very_very_very_very_long = very_very_very_very_very_very_x 
        + very_very_very_very_y + very_very_very_very_z;
    assert(a === b);
    5
}    
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    pub fn test_function(x: int, y: int) -> u32 {
        let very_very_very_very_very_very_long = very_very_very_very_very_very_x 
            + very_very_very_very_y + very_very_very_very_z;
        assert(a === b);
        5
    }    
    "###);
}


// We deviate from rustfmt here, so use our own snapshot to check for self-consistency
#[test]
fn verus_match() {
    let file = r#"
fn len<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
        List::Cons(_, tl) => {
            let t = 1 + len(*tl);
            t
        },
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
}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    fn len<T>(l: List<T>) -> nat {
        match l {
            List::Nil => 0,
            List::Cons(_, tl) => 1 + len(*tl),
            List::Cons(_, tl) => {
                let t = 1 + len(*tl);
                t
            },
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
    }
    "###);
}

#[test]
fn verus_trait() {
    let file = r#"
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
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
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
    "###);
}

#[test]
fn verus_comments() {
    let file = r#"
// External comment 1
/// External comment 2
verus! {

spec fn my_spec_fun() -> int {
    2
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

} // verus!
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    // External comment 1
    /// External comment 2
    verus! {

    spec fn my_spec_fun() -> int {
        2
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

    } // verus!
    "###);
}

