//! Testing ../examples/syntax.rs

/// Just an automatic test to make sure that ../examples/syntax.rs is left unchanged by verusfmt.
///
/// This is essentially intended to be a snapshot test, like ./snap-tests.rs, but only as a quick
/// indicator for whether `syntax.rs` has been modified by any change, in order to ensure that
/// `syntax.rs` always in sync with the output that would show up from verusfmt.
#[test]
fn syntax_rs_unchanged() {
    let original = include_str!("../examples/syntax.rs").to_owned();
    let formatted = verusfmt::parse_and_format(&original).unwrap();
    if original != formatted {
        let diff = similar::udiff::unified_diff(
            similar::Algorithm::Patience,
            &original,
            &formatted,
            3,
            Some(("original", "formatted")),
        );
        println!("{diff}");
        panic!("Formatted output does not match");
    }
}
