#![verus::trusted]
use vstd::prelude::*;

verus! {

pub struct LPacket<IdType, MessageType> {
    pub dst: IdType,
    pub src: IdType,
    pub msg: MessageType,
}

pub enum LIoOp<IdType, MessageType> {
    Send { s: LPacket<IdType, MessageType> },
    Receive { r: LPacket<IdType, MessageType> },
    TimeoutReceive {  },
    ReadClock { t: int },
}

pub enum LEnvStep<IdType, MessageType> {
    HostIos { actor: IdType, ios: Seq<LIoOp<IdType, MessageType>> },
    DeliverPacket { p: LPacket<IdType, MessageType> },
    AdvanceTime {  },
    Stutter {  },
}

pub struct LHostInfo<IdType, MessageType> {
    pub queue: Seq<LPacket<IdType, MessageType>>,
}

#[verifier::reject_recursive_types(IdType)]
#[verifier::reject_recursive_types(MessageType)]
pub struct LEnvironment<IdType, MessageType> {
    pub time: int,
    pub sent_packets: Set<LPacket<IdType, MessageType>>,
    pub host_info: Map<IdType, LHostInfo<IdType, MessageType>>,
    pub next_step: LEnvStep<IdType, MessageType>,
}

pub open spec fn is_valid_lio_op<IdType, MessageType>(
    io: LIoOp<IdType, MessageType>,
    actor: IdType,
    e: LEnvironment<IdType, MessageType>,
) -> bool {
    match io {
        LIoOp::Send { s } => s.src == actor,
        LIoOp::Receive { r } => r.dst == actor,
        LIoOp::TimeoutReceive {  } => true,
        LIoOp::ReadClock { t } => true,
    }
}

// These Ironfleet predicates go away, replaced by a requires-type check in NetClient receieve and
// send interaces.
// LIoOpOrderingOKForAction
// LIoOpSeqCompatibleWithReduction
} // verus!
// verus
