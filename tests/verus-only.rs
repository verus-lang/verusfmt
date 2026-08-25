use insta::assert_snapshot;

/// Tests of verusfmt behavior in `--verus-only` mode.

// We use insta tests (http://insta.rs) to manage the correct answers.
// See README.md for details on how to run and update these tests.

fn parse_and_format(s: &str) -> miette::Result<String> {
    verusfmt::run(
        s,
        verusfmt::RunOptions {
            file_name: None,
            run_rustfmt: false,
            rustfmt_config: Default::default(),
        },
    )
}

#[test]
fn preserves_whitespace_outside_verus_macro() {
    let file = r#"
// A comment.

//! A module comment.

pub fn some_fn() {}
"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @"

    // A comment.

    //! A module comment.

    pub fn some_fn() {}
    ");
}
