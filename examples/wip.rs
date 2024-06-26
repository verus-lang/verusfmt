// External comment 1
/// External comment 2
verus! {

// This comment should stay with the function definition, even though it's parsed as a "prefix" comment
fn clone_value() -> (out: u8) {
}

spec fn my_spec_fun() -> int {
    2
}

enum ReaderState {
    Starting {
        /// Test
        start: LogIdx,
    },
}

/// exec code cannot directly call proof functions or spec functions.
/// However, exec code can contain proof blocks (proof { ... }),
/// which contain proof code.
/// This proof code can call proof functions and spec functions.
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // my_proof_fun(x, y); // not allowed in exec code
    // let u = my_spec_fun(x, y); // not allowed exec code
    proof {
        let u = my_spec_fun(x as int, y as int);  // allowed in proof code
        my_proof_fun(u / 2, y as int);  // allowed in proof code
    }
}

/// Comment 1
/// Comment 2
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // Line comment 1
    // Line comment 2
    proof {
        let u = my_spec_fun(x as int, y as int);  // inline comment 1
        my_proof_fun(u / 2, y as int);  // inline comment 2
    }
}

fn test_ghost_unwrap(x: int)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        y < 100,
{
}

fn test_ghost_unwrap(
    x: u32,
    y: very_very_very_very_very_long_type,
)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        x < 100,
{
}

fn heap_malloc()  // $line_count$Trusted$ 1
 -> (t: nat)  // $line_count$Trusted$ 2
    requires
        true,
{
    a
}

fn test_my_funs2(
    a: u32,  // long comment1
    b: u32,  // long comment2
) {
}

pub struct SHTKey {
    pub  // workaround
     ukey: u64,
}

fn test_my_funs3(
    // exec variable
    a: u32,
    // exec variable
    b: u32,
) {
}

fn my_proof_fun(x: int, y: int)
    requires
        x < 100,  // Very important!
        y < 100,  // This gets parsed as a top-level comment, hence extra newline

    ensures
        sum < 200,  // Definitely want this
        x < 200,  // And this
{
}

#[verifier(external_body)]  // inline comment
pub exec fn foo()
    requires
        a > 5,
{
}

impl AbstractEndPoint {
    fn abstractable() {
        0
    }

    // Multiline comment
    // that should stay together
    fn valid_ipv4() {
        true
    }
}

const y: int = 5;

// Comment
const x: int = 5;

impl a {
    // My favorite function
    fn b()
    //
    ;
}

fn try_parse() -> (u: u32)
//    1
//    2
//    3
{
    8
}

pub fn test() {
    if false {
    }  // No space between the one character indicating non-inline and the comment

}

fn test() {
    let x = 1;  /* inline multi-line comment stays inline */
    let y = 1;
    /* Long
                  dangling
                  comment doesn't */
}

} // verus!
