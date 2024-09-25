#![verus::trusted]
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::seq::*;
use vstd::set::*;

use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;

use crate::abstract_end_point_t::*;

verus! {

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },  // I have received everything up to and including seqno
    InvalidMessage {},  // ... what parse returns for raw messages we can't otherwise parse into a valid message above
}

} // verus!
