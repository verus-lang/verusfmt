use verusfmt::parse_and_format;
use insta::assert_snapshot;

/// Tests of Verus-specific formatting

#[test]
fn constants() {
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

#[test]
fn enums() {
    let file = r#"
verus! {
enum SimpleEnumSingleBriefGenerics<A,B,C,D,E> { Constructor1 }
enum SimpleEnumSingleLongGenerics<ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ> { Constructor1 }
enum SimpleEnumConstructors<A,B,C,D,E> { ConsIdentifier, ConsTupleStruct1(u32,bool,u8), ConsStruct1{x:u8}, ConsStruct2{a:u32, b:bool} }
}"#;

    assert_snapshot!(parse_and_format(file).unwrap(), @r###"
    verus! {

    enum SimpleEnumSingleBriefGenerics<A, B, C, D, E> {
        Constructor1,
    }
    enum SimpleEnumSingleLongGenerics<
        ABCDEFGHIJKLMNOPQRSTUVWXYZ,
        ABCDEFGHIJKLMNOPQRSTUVWXYZ,
        ABCDEFGHIJKLMNOPQRSTUVWXYZ,
        ABCDEFGHIJKLMNOPQRSTUVWXYZ,
    > {
        Constructor1,
    }
    enum SimpleEnumConstructors<A, B, C, D, E> {
        ConsIdentifier,
        ConsTupleStruct1(u32, bool, u8),
        ConsStruct1 { 
            x: u8,
        },
        ConsStruct2 { 
            a: u32,
            b: bool,
        },
    }

    } // verus!
    "###);
}


