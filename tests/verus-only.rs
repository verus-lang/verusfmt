//! Tests of verusfmt behavior in `--verus-only` mode.

use insta::assert_snapshot;

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
fn ignores_verus_tokens_inside_other_macros() {
    let file = "quote_vstd! { vstd =>\n    #vstd::prelude::verus! { #(#ts)* }\n}\n\
quote_vstd!(vstd => [verus! { #(#ts)* }]);\n\
verus! { fn f(){ } }\n";
    assert_snapshot!(parse_and_format(file).unwrap(), @"
    quote_vstd! { vstd =>
        #vstd::prelude::verus! { #(#ts)* }
    }
    quote_vstd!(vstd => [verus! { #(#ts)* }]);
    verus! {

    fn f() {
    }

    } // verus!
    ");
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
