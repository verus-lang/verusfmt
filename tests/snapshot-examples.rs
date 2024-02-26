//! Automatic tests for various files in ../examples/
//!
//! This is essentially intended to be a snapshot test, like ./verus-consistency.rs, but only as a
//! quick indicator for whether files in `../examples/` (such as `../examples/syntax.rs`) have been
//! modified by any change.

fn check_snapshot(original: &str) {
    let formatted = verusfmt::rustfmt(&verusfmt::parse_and_format(&original).unwrap()).unwrap();
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

#[test]
fn syntax_rs_unchanged() {
    check_snapshot(include_str!("../examples/syntax.rs"));
}

#[test]
fn ironfleet_rs_unchanged() {
    check_snapshot(include_str!("../examples/ironfleet.rs"));
}

#[test]
#[ignore] // Due to "fatal runtime error: stack overflow" during `cargo test`, and comment failure during regular execution
fn mimalloc_rs_unchanged() {
    check_snapshot(include_str!("../examples/mimalloc.rs"));
}

#[test]
#[ignore] // Due to a version of https://github.com/verus-lang/verusfmt/issues/33 on the `state_machine` macro
fn nr_rs_unchanged() {
    check_snapshot(include_str!("../examples/nr.rs"));
}

#[test]
fn owl_output_rs_unchanged() {
    check_snapshot(include_str!("../examples/owl-output.rs"));
}

#[test]
fn pagetable_rs_unchanged() {
    check_snapshot(include_str!("../examples/pagetable.rs"));
}
