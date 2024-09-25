//! Automatic tests for various files in ../examples/
//!
//! This is essentially intended to be a snapshot test, like ./verus-consistency.rs, but only as a
//! quick indicator for whether files in `../examples/` (such as `../examples/syntax.rs`) have been
//! modified by any change.

fn verusfmt_run_with_extra_stack(s: &str, opts: verusfmt::RunOptions) -> miette::Result<String> {
    #[allow(non_upper_case_globals)]
    const MiB: usize = 1024 * 1024;
    const STACK_SIZE: usize = 8 * MiB;
    stacker::grow(STACK_SIZE, || verusfmt::run(s, opts))
}

fn check_snapshot(original: &str) {
    check_snapshot_with_config(original, Default::default())
}

fn check_snapshot_with_config(original: &str, config: verusfmt::RunOptions) {
    let formatted = verusfmt_run_with_extra_stack(original, config).unwrap();
    if original != formatted {
        let diff = similar::udiff::unified_diff(
            similar::Algorithm::Patience,
            original,
            &formatted,
            3,
            Some(("original", "formatted")),
        );
        println!("{diff}");
        panic!("Formatted output does not match");
    }
}

#[test]
fn atomic_rs_unchanged() {
    check_snapshot(include_str!("../examples/atomic.rs"));
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

#[glob_macro::glob("./examples/verus-snapshot/**/*.rs")]
#[test]
fn verus_snapshot_unchanged(path: &std::path::Path) {
    check_snapshot_with_config(
        &std::fs::read_to_string(path).unwrap(),
        verusfmt::RunOptions {
            file_name: None,
            run_rustfmt: true,
            rustfmt_config: verusfmt::RustFmtConfig {
                rustfmt_toml: Some(
                    std::fs::read_to_string("./examples/verus-snapshot/source/rustfmt.toml")
                        .unwrap(),
                ),
            },
        },
    );
}
