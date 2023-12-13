verus! {

// Why the extra newline for the semi-colon?
// Answer: The parser sees the `;` as redundant and treats it as a separate statement
fn test() -> u64 {
    proof { assert_sets_equal!(a, b); };
    proof {
        assert_sets_equal!(a, b);
        assert_sets_equal!(c, d);
    };
    5

}

/*
// The first set of &&& get out-dented, while the second one is absorbed into a single line
fn clone_value() -> (out: u8)
    ensures
        match value {
            Some(vec) => {
                &&& out.is_Some()
                &&& out.unwrap()@ == vec@
            },
            None => {
                &&& out.is_None()
            },
        },
{
}

// Weird indenting of the last line
proof fn test() {
    assert_seqs_equal!(v@,
                   old(v)@.subrange(0, start as int) +
                   old(v)@.subrange(start as int + deleted as int,
                                               old(v)@.len() as int));
}

*/
} // verus!
