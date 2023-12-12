verus! {

/*
 This comment absorbes the newline that should separate it from the struct
 */
struct Constants {
    b: int,
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

// Weird formatting of the constructor in the second case
pub fn clone_up_to_view(&self) -> (c: Self)
    ensures
        c@ == self@,
{
    match self {
        CMessage::GetRequest { k } => { CMessage::GetRequest { k: k.clone() } },
        CMessage::SetRequest { k, v } => { CMessage::SetRequest { k: k.clone(), v: CMessage::clone_value(v) } },
    }
}

// Weird formatting of the return value
pub open spec fn abstractify_outbound_packets_to_seq_of_lsht_packets(packets: Seq<CPacket>) -> Seq<
    LSHTPacket,
>
    recommends
        cpacket_seq_is_abstractable(packets),
{
    []
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
