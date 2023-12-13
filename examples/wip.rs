verus! {

// The first set of &&& get out-dented, while the second one is absorbed into a single line
fn clone_value() -> (out: u8)
    ensures
        match value {
            None => {
                &&& out.is_None()
            },
        },
{
}

} // verus!
