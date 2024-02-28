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
    let formatted1 = verusfmt::run(file, Default::default()).unwrap();
    let formatted2 = verusfmt::run(&formatted1, Default::default()).unwrap();
    assert_eq!(formatted1, formatted2);
}

#[test]
/// Regression test for https://github.com/verus-lang/verusfmt/issues/36
fn macro_rules_idempotent() {
    let file = r#"
macro_rules! a {
    () => {
        verus! {
        }
    }
}
"#;
    let formatted1 = verusfmt::run(file, Default::default()).unwrap();
    let formatted2 = verusfmt::run(&formatted1, Default::default()).unwrap();
    assert_eq!(formatted1, formatted2);
}
