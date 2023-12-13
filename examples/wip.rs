verus! {

// Weird formatting of the constructor in the second case
fn clone_up_to_view() {
    match self {
        GetLongDestructorNameGetRequest { k } => { GetLongConstructorNameGetRequest{ k: 5 } },
        SetLongDestructorNameSetRequest { k, v } => { SetLongConstructorNameSetRequest { k: k.clone(), v: CMessage::clone_value(v) } },
    }
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

// Why the extra newline for the semi-colon?
fn test() -> u64 {
    proof { assert_sets_equal!(a, b); };
    proof {
        assert_sets_equal!(a, b);
        assert_sets_equal!(c, d);
    };
    5

}
*/
} // verus!
