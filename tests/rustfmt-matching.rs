use verusfmt::{rustfmt, VERUS_PREFIX, VERUS_SUFFIX};

/// Tests to check that when formatting standard Rust syntax,
/// we match rustfmt

fn compare(file: &str) {
    let verus_file = format!("{}{}{}", VERUS_PREFIX, file, VERUS_SUFFIX);
    let verus_fmt = verusfmt::run(
        &verus_file,
        verusfmt::RunOptions {
            file_name: None,
            run_rustfmt: false,
            rustfmt_config: Default::default(),
        },
    )
    .unwrap();
    let start = VERUS_PREFIX.len();
    let end = verus_fmt.len() - VERUS_SUFFIX.len();
    let verus_inner = &verus_fmt[start..end];
    let rust_fmt = rustfmt(file).unwrap();
    println!("{}", rust_fmt);

    let diff = similar::udiff::unified_diff(
        similar::Algorithm::Patience,
        &rust_fmt,
        verus_inner,
        3,
        Some(("rust", "verus")),
    );
    assert_eq!(rust_fmt, verus_inner, "\n{diff}");
}

#[test]
fn rust_literals() {
    let file = r#"
fn test() {
    let a = 123.0f64;
    let a = 0.1f64;
    let a = 0.1f32;
    let a = 12E+99_f64;
    let x: f64 = 2.;
    let x = (1,);
    let t = 'x';
    let t = '\\';
    let t = '\t';
    let t = '\x0C';
    let t = '\x41';
    let t = '\x00';
    let t = '\x7f';
    let t = '\u{00e9}';
}
"#;
    compare(file);
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

// Comment
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
    let temp_owl__x23 = { let x: Vec<u8> = mk_vec_u8!(); x };
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

fn uses_is(t: ThisOrThat) {
     match t {
        ThisOrThat::This(..) => assert(t),
        ThisOrThat::That{..} => assert(t),
     }
}

"#;
    compare(file);
}

#[test]
fn rust_use_decls() {
    let file = r#"
pub use extraction_lib::*;
pub use std::collections::HashMap;
pub use std::env;
pub use std::fs;
pub use std::io::{self, BufRead, Write};
pub use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};

fn syntactic_eq(&self, other: &Self) -> bool {
    use BndX::*;
    use TypX::*;
    match self {
        A => b,
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
    if !b {
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
    if let Result::Ok(x) = y {
        x
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

#[test]
fn rust_exprs() {
    let file = r#"
fn test_function() {
    let shifted = (w >> (b - 2) as u64) as u8;
    let mut points_to = points_to_raw.into_typed::<Page>(pt as u64);
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

#[test]
fn rust_type_alias() {
    let file = r#"
impl View for owl_t {
    type V = owlSpec_t;
}

type LongLongLongLongLongLongLongLongLongLongType = LongerLongLongLongLongLongLongLongLongLongLongType;

type NoSpaceTypeA=NoSpaceTypeB;
"#;
    compare(file);
}

#[test]
fn rust_rename() {
    let file = r#"
use crate::parse_serialize::View as _;
use LongLongLongLongLongLongLongLongLongLongType as LongerLongLongLongLongLongLongLongLongLongLongType;
"#;
    compare(file);
}

#[test]
fn rust_wildcard_type_annotation() {
    let file = r#"
fn foo() {
    let x: _ = bar();
}

fn blah() {
let (temp_owl__x607, Tracked(itree)): ( _
, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>> ) = { baz(); };
}
"#;
    compare(file);
}

#[test]
fn rust_loops() {
    let file = r#"
fn test() {
    for CKeyKV in v {
        res.insert(k, v);
    }
}

fn test() {
    for CKeyKV { k, v } in v {
        res.insert(k, v);
    }
}

"#;
    compare(file);
}

#[test]
fn rust_verus_bang_in_string() {
    let file = r#"
fn test() {
    println!("verus!{{{}}}", "Hello");
}
"#;
    compare(file);
}
