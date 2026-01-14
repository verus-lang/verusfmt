//! Translates file IronFleet Impl/SHT/CMessage.i.dfy
use vstd::prelude::*;

use vstd::{seq::*, seq_lib::*};

use crate::abstract_parameters_t::*;
use crate::app_interface_t::*;
use crate::args_t::clone_vec_u8;
use crate::hashmap_t::CKeyHashMap;
use crate::host_impl_v::*;
use crate::host_protocol_t::*;
use crate::io_t::EndPoint;
use crate::keys_t::KeyRange;
use crate::keys_t::*;
use crate::marshal_v::*;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_message_t::SingleMessage;

use crate::verus_extra::clone_v::*;

verus! {

#[allow(inconsistent_fields)]  // Not sure why we need this; v sure looks equivalent to me!
pub enum CMessage {
    GetRequest { k: CKey },
    SetRequest { k: CKey, v: Option::<Vec<u8>> },
    Reply { k: CKey, v: Option::<Vec::<u8>> },
    Redirect { k: CKey, id: EndPoint },
    Shard { kr: KeyRange::<CKey>, recipient: EndPoint },
    Delegate { range: KeyRange::<CKey>, h: CKeyHashMap },
}

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>> {
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
}

pub fn clone_optional_value(ov: &Option::<Vec::<u8>>) -> (res: Option::<Vec::<u8>>)
    ensures
        optional_value_view(*ov) == optional_value_view(res),
{
    match ov.as_ref() {
        Some(v) => Some(clone_vec_u8(v)),
        None => None,
    }
}

// Translates Impl/SHT/AppInterface.i.dfy :: IsKeyValid
pub fn is_key_valid(key: &CKey) -> (b: bool)
    ensures
        b == valid_key(*key),
{
    true
}

// Translates Impl/SHT/AppInterface.i.dfy :: IsValueValid
pub fn is_value_valid(val: &Vec<u8>) -> (b: bool)
    ensures
        b == valid_value(val@),
{
    val.len() < 1024
}

impl CMessage {
    // CMessageIsAbstractable
    pub open spec fn abstractable(self) -> bool {
        match self {
            CMessage::Redirect { k, id } => id@.abstractable(),
            CMessage::Shard { kr, recipient } => recipient@.abstractable(),
            _ => true,
        }
    }

    pub open spec fn view(self) -> Message {
        match self {
            CMessage::GetRequest { k } => Message::GetRequest { key: k },
            CMessage::SetRequest { k, v } => Message::SetRequest {
                key: k,
                value: optional_value_view(v),
            },
            CMessage::Reply { k, v } => Message::Reply { key: k, value: optional_value_view(v) },
            CMessage::Redirect { k, id } => Message::Redirect { key: k, id: id@ },
            CMessage::Shard { kr, recipient } => Message::Shard {
                range: kr,
                recipient: recipient@,
            },
            CMessage::Delegate { range, h } => Message::Delegate { range: range, h: h@ },
        }
    }

    pub proof fn view_equal_spec()
        ensures
            forall|x: &CMessage, y: &CMessage| #[trigger] x.view_equal(y) <==> x@ == y@,
    {
        assert forall|x: &CMessage, y: &CMessage| #[trigger] x.view_equal(y) <==> x@ == y@ by {
            match (x, y) {
                (CMessage::GetRequest { k: k1 }, CMessage::GetRequest { k: k2 }) => {},
                (
                    CMessage::SetRequest { k: k1, v: v1 },
                    CMessage::SetRequest { k: k2, v: v2 },
                ) => {},
                (CMessage::Reply { k: k1, v: v1 }, CMessage::Reply { k: k2, v: v2 }) => {},
                (
                    CMessage::Redirect { k: k1, id: id1 },
                    CMessage::Redirect { k: k2, id: id2 },
                ) => {},
                (
                    CMessage::Shard { kr: kr1, recipient: r1 },
                    CMessage::Shard { kr: kr2, recipient: r2 },
                ) => {},
                (
                    CMessage::Delegate { range: r1, h: h1 },
                    CMessage::Delegate { range: r2, h: h2 },
                ) => {},
                _ => {
                    assert(!x.view_equal(y) && x@ != y@);
                },
            }
        }
    }

    // This would be better if we had a View trait.
    pub fn clone_value(value: &Option<Vec<u8>>) -> (out: Option<Vec<u8>>)
        ensures
            match value {
                Some(vec) => {
                    &&& out.is_Some()
                    &&& out.unwrap()@ == vec@
                },
                None => { &&& out.is_None() },
            },
    {
        match value {
            Some(vec) => Some(clone_vec_u8(vec)),
            None => None,
        }
    }

    pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        match self {
            CMessage::GetRequest { k } => { CMessage::GetRequest { k: k.clone() } },
            CMessage::SetRequest { k, v } => {
                CMessage::SetRequest { k: k.clone(), v: CMessage::clone_value(v) }
            },
            CMessage::Reply { k, v } => {
                CMessage::Reply { k: k.clone(), v: CMessage::clone_value(v) }
            },
            CMessage::Redirect { k, id } => {
                CMessage::Redirect { k: k.clone(), id: id.clone_up_to_view() }
            },
            CMessage::Shard { kr, recipient } => {
                CMessage::Shard { kr: kr.clone(), recipient: recipient.clone_up_to_view() }
            },
            CMessage::Delegate { range, h } => {
                CMessage::Delegate { range: range.clone(), h: h.clone_up_to_view() }
            },
        }
    }

    // Translates Impl/SHT/PacketParsing.i.dfy :: MessageMarshallable
    pub open spec fn message_marshallable(&self) -> bool {
        match self {
            CMessage::GetRequest { k } => valid_key(*k),
            CMessage::SetRequest { k, v } => valid_key(*k) && valid_optional_value(
                optional_value_view(*v),
            ),
            CMessage::Reply { k, v } => valid_key(*k) && valid_optional_value(
                optional_value_view(*v),
            ),
            CMessage::Redirect { k, id } => valid_key(*k) && id@.valid_physical_address(),
            CMessage::Shard { kr, recipient } => recipient@.valid_physical_address()
                && !kr.is_empty(),
            CMessage::Delegate { range, h } => !range.is_empty() && valid_hashtable(h@),
        }
    }

    // Translates Impl/SHT/PacketParsing.i.dfy :: IsMessageMarshallable
    pub fn is_message_marshallable(&self) -> (b: bool)
        ensures
            b == self.message_marshallable(),
    {
        match self {
            CMessage::GetRequest { k } => is_key_valid(k),
            CMessage::SetRequest { k, v } => is_key_valid(k) && match v {
                Some(v) => is_value_valid(v),
                None => true,
            },
            CMessage::Reply { k, v } => is_key_valid(k) && match v {
                Some(v) => is_value_valid(v),
                None => true,
            },
            CMessage::Redirect { k, id } => is_key_valid(k) && id.valid_physical_address(),
            CMessage::Shard { kr, recipient } => recipient.valid_physical_address() && kr.lo.lt(
                &kr.hi,
            ),
            CMessage::Delegate { range, h } => range.lo.lt(&range.hi) && h.valid(),
        }
    }
}

pub open spec fn abstractify_cmessage_seq(
    messages: Seq<CSingleMessage>,
) -> Seq<SingleMessage<Message>> {
    messages.map_values(|msg: CSingleMessage| msg@)
}

/* $line_count$Proof$ */

define_enum_and_derive_marshalable! {
/* $line_count$Exec$ */ pub enum CSingleMessage {
/* $line_count$Exec$ */   #[tag = 0]
/* $line_count$Exec$ */   Message{ #[o=o0] seqno: u64, #[o=o1] dst: EndPoint, #[o=o2] m: CMessage },
/* $line_count$Exec$ */   #[tag = 1]
/* $line_count$Exec$ */   // I got everything up to and including `ack_seqno`
/* $line_count$Exec$ */   Ack{ #[o=o0] ack_seqno: u64},
/* $line_count$Exec$ */   #[tag = 2]
/* $line_count$Exec$ */   InvalidMessage,
/* $line_count$Exec$ */ }
/* $line_count$Proof$ */ [rlimit attr = verifier::rlimit(25)]
}
// Note simplifications from IronFleet:
// - we don't have a runtime Parameters, just a static value supplied by a function.
// - we don't have a separate CParameters, just AbstractParameters.


impl CSingleMessage {
    /// translates CSingleMessageIsAbstractable
    pub open spec fn abstractable(self) -> bool {
        match self {
            CSingleMessage::Message { seqno: _, dst, m } => dst@.abstractable() && m.abstractable(),
            CSingleMessage::Ack { ack_seqno: _ } => true,
            CSingleMessage::InvalidMessage {  } => true,
        }
    }

    /// translates CSingleMessageIsValid
    // temp_valid to catch old callsites that intended to call abstractable()
    pub open spec fn temp_valid(&self) -> bool {
        match self {
            CSingleMessage::Message { seqno, .. } => seqno
                < AbstractParameters::static_params().max_seqno,
            CSingleMessage::Ack { ack_seqno } => ack_seqno
                < AbstractParameters::static_params().max_seqno,
            CSingleMessage::InvalidMessage {  } => false,
        }
    }

    pub open spec fn view(self) -> SingleMessage<Message> {
        match self {
            CSingleMessage::Message { seqno, dst, m } => SingleMessage::Message {
                seqno: seqno as nat,
                dst: dst@,
                m: m@,
            },
            CSingleMessage::Ack { ack_seqno } => SingleMessage::Ack { ack_seqno: ack_seqno as nat },
            CSingleMessage::InvalidMessage {  } => SingleMessage::InvalidMessage {  },
        }
    }

    pub proof fn view_equal_spec()
        ensures
            forall|x: &CSingleMessage, y: &CSingleMessage| #[trigger] x.view_equal(y) <==> x@ == y@,
    {
        assert forall|x: &CSingleMessage, y: &CSingleMessage| #[trigger]
            x.view_equal(y) <==> x@ == y@ by {
            match (x, y) {
                (
                    CSingleMessage::Message { seqno: seqno1, dst: dst1, m: m1 },
                    CSingleMessage::Message { seqno: seqno2, dst: dst2, m: m2 },
                ) => {
                    CMessage::view_equal_spec();
                    assert(seqno1.view_equal(seqno2) <==> seqno1 == seqno2);
                    assert(dst1.view_equal(dst2) <==> dst1@ == dst2@);
                    assert(m1.view_equal(m2) <==> m1@ == m2@);
                },
                (CSingleMessage::InvalidMessage {  }, CSingleMessage::InvalidMessage {  }) => {},
                (
                    CSingleMessage::Ack { ack_seqno: x1 },
                    CSingleMessage::Ack { ack_seqno: x2 },
                ) => {},
                _ => {
                    assert(!x.view_equal(y) && x@ != y@);
                },
            }
        }
    }

    pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        match self {
            CSingleMessage::Message { seqno, dst, m } => {
                CSingleMessage::Message {
                    seqno: *seqno,
                    dst: dst.clone_up_to_view(),
                    m: m.clone_up_to_view(),
                }
            },
            CSingleMessage::Ack { ack_seqno } => { CSingleMessage::Ack { ack_seqno: *ack_seqno } },
            CSingleMessage::InvalidMessage {  } => { CSingleMessage::InvalidMessage {  } },
        }
    }

    // Translates Impl/SHT/PacketParsing.i.dfy :: CSingleMessageMarshallable
    pub open spec fn marshallable(&self) -> bool {
        match self {
            CSingleMessage::Ack { .. } => true,
            CSingleMessage::Message { seqno, dst, m } => dst.valid_public_key()
                && m.message_marshallable(),
            CSingleMessage::InvalidMessage {  } => false,
        }
    }

    // Translates Impl/SHT/PacketParsing.i.dfy :: IsCSingleMessageMarshallable
    pub fn is_marshallable(&self) -> (b: bool)
        ensures
            b == self.marshallable(),
    {
        match self {
            CSingleMessage::Ack { ack_seqno } => true,
            CSingleMessage::Message { seqno, dst, m } => dst.valid_physical_address()
                && m.is_message_marshallable(),
            CSingleMessage::InvalidMessage {  } => false,
        }
    }
}

pub struct CPacket {
    pub dst: EndPoint,
    pub src: EndPoint,
    pub msg: CSingleMessage,
}

impl CPacket {
    pub open spec fn valid(self) -> bool {
        &&& self.msg.temp_valid()
    }

    // Translates Impl/SHT/PacketParsing.i.dfy :: AbstractifyCPacketToShtPacket
    pub open spec fn view(self) -> Packet {
        Packet { dst: self.dst@, src: self.src@, msg: self.msg@ }
    }

    pub open spec fn abstractable(self) -> bool {
        &&& self.dst.abstractable()
        &&& self.src.abstractable()
        &&& self.msg.abstractable()
    }
}

// Translates Impl/SHT/CMessage :: CPacketSeqIsAbstractable
pub open spec fn cpacket_seq_is_abstractable(packets: Seq<CPacket>) -> bool {
    forall|i: int| 0 <= i && i < packets.len() ==> #[trigger] packets[i].abstractable()
}

// Translates Impl/SHT/PacketParsing.i.dfy :: AbstractifyOutboundPacketsToSeqOfLSHTPackets
pub open spec fn abstractify_outbound_packets_to_seq_of_lsht_packets(
    packets: Seq<CPacket>,
) -> Seq<LSHTPacket>
    recommends
        cpacket_seq_is_abstractable(packets),
{
    packets.map_values(|packet: CPacket| abstractify_cpacket_to_lsht_packet(packet))
}

// Translates Impl/SHT/CMessage.i.dfy :: AbstractifySeqOfCPacketsToSetOfShtPackets
pub open spec fn abstractify_seq_of_cpackets_to_set_of_sht_packets(cps: Seq<CPacket>) -> Set<Packet>
    recommends
        cpacket_seq_is_abstractable(cps),
{
    cps.map_values(|cp: CPacket| cp@).to_set()
}

impl CPacket {
    fn clone_up_to_view(&self) -> (o: Self) {
        CPacket {
            dst: self.dst.clone_up_to_view(),
            src: self.src.clone_up_to_view(),
            msg: self.msg.clone_up_to_view(),
        }
    }
}

} // verus!
