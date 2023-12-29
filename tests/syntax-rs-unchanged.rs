//! Testing ../examples/syntax.rs

use verusfmt::parse_and_format;

/// Just an automatic test to make sure that ../examples/syntax.rs is left unchanged by verusfmt.
///
/// This is essentially intended to be a snapshot test, like ./snap-tests.rs, but only as a quick
/// indicator for whether `syntax.rs` has been modified by any change, in order to ensure that
/// `syntax.rs` always in sync with the output that would show up from verusfmt.
#[test]
fn syntax_rs_unchanged() {
    let syntax_rs = include_str!("../examples/syntax.rs").to_owned();
    assert_eq!(parse_and_format(&syntax_rs).unwrap(), syntax_rs);
}
