use verusfmt::{VERUS_PREFIX, VERUS_SUFFIX, parse_and_format, rustfmt};

/// Tests to check that when formatting standard Rust syntax,
/// we match rustfmt


fn compare(file: &str) {
    let verus_file = format!("{}{}{}", VERUS_PREFIX, file, VERUS_SUFFIX);
    let verus_fmt = parse_and_format(&verus_file).unwrap();
    let start = VERUS_PREFIX.len();
    let end = verus_fmt.len() - VERUS_SUFFIX.len();
    let verus_inner = &verus_fmt[start..end];
    let rust_fmt = rustfmt(file).unwrap();
    println!("{}", rust_fmt);

    let diff = similar::udiff::unified_diff(
        similar::Algorithm::Patience,
        &rust_fmt,
        &verus_inner,
        3,
        Some(("rust", "verus")),
    );
    assert_eq!(rust_fmt, verus_inner, "{diff}");
}

#[test]
fn rust_attributes() {
    let file = r#"
#![allow(unused_variables)]
#[verifier(external_type_specification)]
#[verifier(external_body)]
const x: int = 5;
"#;
    compare(file);
}

#[test]
fn rust_constants() {
    let file = r#"
#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST1 : some_very_very_very_very_very_very_very_very_very_very_very_very_long_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";

#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST2 : some_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";

#[verifier=abcd] pub(in self::super::crate) default const MY_CONST3: some_type = 5;

const y: int = 5;

/* TODO
pub open(crate) spec fn my_pub_spec_fun2(x: u32, y: u32) -> u32 {
    // function visible to all, body visible to crate
    x / 2 + y / 2
}
*/
// TODO(main_new) pub(crate) is not being handled correctly
// TODO(main_new) pub(crate) is not being handled correctly
const x: int = 5;
        
"#;
    compare(file);
}

#[test]
fn rust_enums() {
    let file = r#"
enum SimpleEnumSingleBriefGenerics<A,B,C,D,E> { Constructor1 }

enum SimpleEnumSingleLongGenerics<ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ,ABCDEFGHIJKLMNOPQRSTUVWXYZ> { Constructor1 }

enum SimpleEnumConstructors<A,B,C,D,E> { ConsIdentifier, ConsTupleStruct1(u32,bool,u8), ConsStruct1{x:u8}, ConsStruct2{a:u32, b:bool} }

enum Enum {
    ConsIdentifier,
    ConsTupleStruct1(u32, bool, u8),
    ConsStruct2 {
        a_very_very_very_very_very_very_long_name:
            a_very_very_very_very_very_very_very_very_very_very_very_very_long_type,
        b: bool,
    },
}
"#;
    compare(file);
}

#[test]
fn rust_structs() {
    let file = r#"
struct Foo { a: A, b: B }

struct Collection {}

struct Struct2 {
    a_very_very__very_very_very_very_very_very_long_name:
        a_very_very_very_very_very_very_very_very_very_very_very_very_long_type,
    b: bool,
    c: u32,
}

struct TrackedAndGhost<T, G>(
    T,
    G,
);

pub struct Bar(String, u8);

struct Unit();
"#;
    compare(file);
}

#[test]
fn rust_functions() {
    let file = r#"
#[verifier=abcd]
pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32;    

pub fn test_function<A, B, C>(long_var_name_1: LongLongLongTypeName, long_var_name_2: LongLongLongTypeName, long_var_name_3: LongLongLongTypeName) -> u32;    

pub fn test_function1<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 { let x = a; let mut z = b; c }

pub fn test_function2<A, B, C>(a: u32) -> u32 { a }

pub fn test_function3<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let x = a;
    let serialized = serialize_msg(&msg);
    todo!();
    c
}

"#;
    compare(file);
}

#[test]
fn rust_let_stmt() {
    let file = r#"
#[verifier=abcd]
pub fn test_function3<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let long_long_long_long_long_long_long_long_name: LongLongLongLongLongLongLongLongType = long_long_function_name(a);
    let x = a;
    let mut z = b;
    let long_long_long_long_long_long_long_long_name: LongLongLongLongLongLongLongLongLongLongType = long_long_function_name(a);
    let x = (
        a_long_long_long_long_long_long_long_long_long_long_long_long_expr,
        another_very_long_expr,
        c,
    );
    let _addr = listener.unwrap();
    let coins = owl_sample::<int,bool>();
    let f = Foo { field1, field2: 0 };
    let f = Foo {
        very_long_very_long_very_long_expression1,
        very_long_field_name: very_long_very_long_very_long_expression2,
    };
    c
}
"#;
    compare(file);
}


#[test]
fn rust_blocks() {
    let file = r#"
pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let _ = { a_call() };
    let _ = unsafe { a_call() };
    let _ = {
        a_call();
        b
    };
    unsafe {
        a_call();
    };
    let x = 5;
    a
}

pub fn test() -> bool {
    let z = {
        let k = 5;
        k
    };
}

pub fn test() -> bool {
    {
        let y = 7;
        b
    }
}

pub fn test() -> bool {
    unsafe {
        let x = 5;
        x
    }
}
"#;
    compare(file);
}

#[test]
fn rust_closures() {
    let file = r#"
pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let f = || true;
    let g = |x, y| x;
}
"#;
    compare(file);
}

#[test]
fn rust_match_expr() {
    let file = r#"
fn len<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
    }
}
"#;
    compare(file);
}

// TODO: We can't handle this test and the block_exprs consistently at the same time
#[test]
#[ignore]
fn rust_bin_expr() {
    let file = r#"
pub fn test_function(x: int, y: int) -> u32 {
    let z = x + y;
    let very_very_very_very_very_very_long = 
        very_very_very_very_very_very_x + very_very_very_very_y;
    5
}
"#;
    compare(file);
}

#[test]
fn rust_if() {
    let file = r#"
fn test_function() {
    if arg.len() < 12 {
        return 5;
    }
    extend_vec_u8();
    if y {
        1
    } else if x {
        2
    } else {
        3
    }
}

fn test_rec2(x: int, y: int) -> int
{
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else if x > 0 {
        2 + test_rec2(x - 1, 100)
    } else {
        3
    }
}

pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    if y > 0 { 1 + test_rec2(x, y - 1) } else if x > 0 { 2 + test_rec2(x - 1, 100) } else { 3 }
}
"#;
    compare(file);
}


// TODO: Need to differentiate if-expressions in different contexts
#[test]
#[ignore]
fn rust_if_contexts() {
    let file = r#"
pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let x = if b { 5 } else { 10 };
    if b {
        5
    } else {
        10
    }
}
"#;
    compare(file);
}

// Rust removes the semicolon after the while loop;
// for simplicity we keep it
#[test]
#[ignore]
fn rust_while() {
    let file = r#"
pub fn test_function() -> u32 {
    if b {
        a;
    } else {
        c;
    };
    while b {
        let x = a;
        a;
    };
    5
}
"#;
    compare(file);
}
