use verusfmt::parse_and_format;
use insta::assert_snapshot;

/// Tests of Verus-specific formatting


// This is an example of an insta test.
// Since we don't currently support verus-specific features, it only uses Rust features
// but in the future, it should be a Verus-specific test
#[test]
fn verus_constants() {
    let file = r#"
verus! {
#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST1 : some_very_very_very_very_very_very_very_very_very_very_very_very_long_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST2 : some_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
#[verifier=abcd] pub(in self::super::crate) default const MY_CONST3: some_type = 5;
}"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    #[verifier=abcd]
    #[verifier=efgh]
    pub(in self::super::crate) default const MY_CONST1:
        some_very_very_very_very_very_very_very_very_very_very_very_very_long_type =
        "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
    #[verifier=abcd]
    #[verifier=efgh]
    pub(in self::super::crate) default const MY_CONST2: some_type =
        "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
    #[verifier=abcd]
    pub(in self::super::crate) default const MY_CONST3: some_type = 5;

    } // verus!
    "###);
}

