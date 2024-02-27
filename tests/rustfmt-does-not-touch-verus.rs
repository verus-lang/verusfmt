#[test]
/// Regression test for https://github.com/verus-lang/verusfmt/issues/33
fn mod_macro_item_idempotent() {
    let file = r#"
  mod foo {
    verus! {

        bar! {
            baz
        }

    }
  }
"#;
    let formatted1 = verusfmt::rustfmt(&verusfmt::parse_and_format(file).unwrap()).unwrap();
    let formatted2 = verusfmt::rustfmt(&verusfmt::parse_and_format(&formatted1).unwrap()).unwrap();
    assert_eq!(formatted1, formatted2);
}
