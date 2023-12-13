verus! {

// Weird indenting of the last line
// Answer: This is because we don't format inside macro calls
proof fn test() {
    assert_seqs_equal!(v@,
                   old(v)@.subrange(0, start as int) +
                   old(v)@.subrange(start as int + deleted as int,
                                               old(v)@.len() as int));
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

*/
} // verus!
