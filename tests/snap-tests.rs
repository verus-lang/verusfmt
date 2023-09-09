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
    assume(x);
    assert(x) by (bit_vector);
    5
}
spec fn dec0(a: int) -> int
    decreases a,
    when a
    via dec0_decreases
{
    5
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
        assume(x);
        assert(x) by (bit_vector);
        5
    }
    spec fn dec0(a: int) -> int
        decreases a,
        when a
        via dec0_decreases
    {
        5
    }
    "###);
}

