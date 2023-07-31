use std::process::{Command,Stdio};
use std::str::from_utf8;
use std::io::Write;
use verusfmt::{VERUS_PREFIX, VERUS_SUFFIX,parse_and_format};

/// Tests to check that when formatting standard Rust syntax,
/// we match rustfmt


/// Run rustfmt
fn rustfmt(value: &str) -> Option<String> {
    if let Ok(mut proc) = Command::new("rustfmt")
        .arg("--emit=stdout")
        .arg("--edition=2021")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        {
            let stdin = proc.stdin.as_mut().unwrap();
            stdin.write_all(value.as_bytes()).unwrap();
        }
        if let Ok(output) = proc.wait_with_output() {
            if output.status.success() {
                return Some(from_utf8(&output.stdout)
                    .unwrap()
                    .into());
            } else {
                eprintln!("rustfmt failed! {}", from_utf8(&output.stderr).unwrap());
            }
        }
    }
    None
}

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
fn rust_constants() {
    let file = r#"
#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST1 : some_very_very_very_very_very_very_very_very_very_very_very_very_long_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
#[verifier=abcd] #[verifier=efgh] pub(in self::super::crate) default const MY_CONST2 : some_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
#[verifier=abcd] pub(in self::super::crate) default const MY_CONST3: some_type = 5;
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
struct Struct2 {
    a_very_very__very_very_very_very_very_very_long_name:
        a_very_very_very_very_very_very_very_very_very_very_very_very_long_type,
    b: bool,
    c: u32,
}
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
"#;
    compare(file);
}

