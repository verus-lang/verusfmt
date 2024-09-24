use builtin::*;
use builtin_macros::*;

use crate::abstract_end_point_t::*;
use crate::abstract_parameters_t::*;
use crate::abstract_service_t::*;
use crate::app_interface_t::*;
use crate::args_t::*;
use crate::cmessage_v::*;
use crate::delegation_map_t::*;
use crate::delegation_map_v::*;
use crate::environment_t::*;
use crate::hashmap_t::*;
use crate::host_protocol_t;
use crate::host_protocol_t::*;
use crate::io_t::*;
use crate::keys_t::*;
use crate::marshal_ironsht_specific_v::*;
use crate::marshal_v::Marshalable;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_delivery_state_v::*;
use crate::single_delivery_t::*;
use crate::single_message_t::*;
use vstd::map::*; // TODO(andrea): prelude doesn't give me the macros?
use vstd::prelude::*;
use vstd::seq_lib::*; // TODO(andrea): prelude doesn't give me the macros?

use crate::host_impl_t::*; // need some definitions from Rust

verus! {

pub enum ReceiveResult {
    Fail,
    Timeout,
    Packet { cpacket: CPacket },
}

// zoology ontology:
//
// Packet: Message (parsed payload), AbstractEndPoint
// (seqs)
// CPacket: CMessage (parsed payload), raw endpoint
// (vecs)
// ReceiveResult wraps a CPacket.
// NetEvent: LIoOp<AbstractEndPoint, Seq<u8>>
// NetPacket: LPacket<EndPoint, Vec<u8>>
// NetcReceiveResult: Vec<u8>
pub type LSHTPacket = LPacket<AbstractEndPoint, SingleMessage<Message>>;

// Ports Impl/SHT/PacketParsing.i.dfy :: NetPacketIsAbstractable
pub open spec fn net_packet_is_abstractable(net: NetPacket) -> bool {
    true
}

// Translates Impl/LiveSHT/NetSHT.i.dfy :: NetEventIsAbstractable
pub open spec fn net_event_is_abstractable(evt: NetEvent) -> bool {
    match evt {
        LIoOp::<AbstractEndPoint, Seq<u8>>::Send { s } => net_packet_is_abstractable(s),
        LIoOp::<AbstractEndPoint, Seq<u8>>::Receive { r } => net_packet_is_abstractable(r),
        LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive {  } => true,
        LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock { t } => true,
    }
}

// Translates Distributed/Impl/SHT/PacketParsing.i.dfy SHTDemarshallData
pub open spec fn sht_demarshal_data(data: Seq<u8>) -> CSingleMessage
    recommends
        exists|v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data,
{
    let v = choose|v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data;
    v
}

#[verifier(spinoff_prover)]
pub proof fn sht_marshal_data_injective(a: &CSingleMessage, b: &CSingleMessage)
    requires
        a.is_marshalable(),
        b.is_marshalable(),
        a.ghost_serialize() == b.ghost_serialize(),
    ensures
        a@ == b@,
{
    a.lemma_serialize_injective(b);
    assert(a@ == b@);  // OBSERVE; although not entirely sure why this is necessary here, esp since it exactly matches the postcondition.
}

// Ports Impl/SHT/PacketParsing.i.dfy :: AbstractifyNetPacketToLSHTPacket
pub open spec fn abstractify_net_packet_to_lsht_packet(net: NetPacket) -> LSHTPacket
    recommends
        net_packet_is_abstractable(net),
{
    LPacket { dst: net.dst, src: net.src, msg: (sht_demarshal_data(net.msg))@ }
}

// Translates Impl/LiveSHT/NetSHT.i.dfy :: AbstractifyNetEventToLSHTIo
pub open spec fn abstractify_net_event_to_lsht_io(evt: NetEvent) -> LSHTIo
    recommends
        net_event_is_abstractable(evt),
{
    match evt {
        LIoOp::<AbstractEndPoint, Seq<u8>>::Send { s } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::Send { s: abstractify_net_packet_to_lsht_packet(s) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::Receive { r } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::Receive { r: abstractify_net_packet_to_lsht_packet(r) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive {  } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::TimeoutReceive {  },
        LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock { t } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::ReadClock { t: t as int },
    }
}

// Ports Impl/SHT/PacketParsing.i.dfy :: AbstractifyNetPacketToShtPacket
pub open spec fn abstractify_net_packet_to_sht_packet(net: NetPacket) -> Packet
    recommends
        net_packet_is_abstractable(net),
{
    let lp = abstractify_net_packet_to_lsht_packet(net);
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

// Translates Impl/LiveSHT/NetSHT.i.dfy :: NetEventLogIsAbstractable
pub open spec fn net_event_log_is_abstractable(rawlog: Seq<NetEvent>) -> bool {
    forall|i: int| 0 <= i && i < rawlog.len() ==> #[trigger] net_event_is_abstractable(rawlog[i])
}

// Translates Distributed/Impl/SHT/PacketParsing.i.dfy SHTDemarshallDataMethod
pub fn sht_demarshall_data_method(buffer: &Vec<u8>) -> (out: CSingleMessage)
    ensures
        !(out is InvalidMessage) ==> {
            &&& out.is_marshalable()
            &&& out@ == sht_demarshal_data(buffer@)@
            &&& out.abstractable()
        },
{
    match CSingleMessage::deserialize(&buffer, 0) {
        None => { CSingleMessage::InvalidMessage },
        Some((cmessage, count)) => {
            if count != buffer.len() {
                return CSingleMessage::InvalidMessage;
            }
            match &cmessage {
                CSingleMessage::Message { dst, m, .. } => {
                    if !dst.valid_physical_address() {
                        return CSingleMessage::InvalidMessage;
                    }
                    match m {
                        CMessage::Redirect { id, .. } => {
                            if !id.valid_physical_address() {
                                return CSingleMessage::InvalidMessage;
                            }
                        },
                        CMessage::Shard { recipient, .. } => {
                            if !recipient.valid_physical_address() {
                                return CSingleMessage::InvalidMessage;
                            }
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
            proof {
                assert(buffer@.subrange(0, count as int) =~= buffer@);
                sht_marshal_data_injective(&sht_demarshal_data(buffer@), &cmessage);
            }
            cmessage
        },
    }
}

// ported from Impl/LiveSHT/NetSHT Receive
pub fn receive_with_demarshal(netc: &mut NetClient, local_addr: &EndPoint) -> (rc: (
    ReceiveResult,
    Ghost<NetEvent>,
))
    requires
        old(netc).ok(),
        old(netc).my_end_point() == local_addr@,
        old(netc).state() is Receiving,
        local_addr.abstractable(),
    ensures
        ({
            let (rr, net_event) = rc;
            &&& netc.my_end_point() == old(netc).my_end_point()
            &&& netc.ok() == !(rr is Fail)
            &&& !(rr is Fail) ==> netc.ok() && netc.history() == old(netc).history()
                + seq!( net_event@ )
            &&& rr is Timeout ==> net_event@ is TimeoutReceive
            &&& (rr is Packet ==> {
                &&& net_event@ is Receive
                &&& true  // NetPacketIsAbstractable is true
                &&& rr.arrow_Packet_cpacket().abstractable()  // can parse u8s up to NetEvent.
                &&& true  // EndPointIsValidPublicKey
                &&& !(rr.arrow_Packet_cpacket()@.msg is InvalidMessage) ==> {
                    &&& rr.arrow_Packet_cpacket()@ == abstractify_net_packet_to_sht_packet(
                        net_event@.arrow_Receive_r(),
                    )
                    &&& rr.arrow_Packet_cpacket().msg@ == sht_demarshal_data(
                        net_event@.arrow_Receive_r().msg,
                    )@
                }
                &&& rr.arrow_Packet_cpacket().dst@ == local_addr@
            })
        }),
{
    let timeout = 0;
    let netr = netc.receive(timeout);

    match netr {
        NetcReceiveResult::Error => {
            // Dafny IronFleet leaves this unassigned, but we have to make something up.
            let dummy = NetEvent::TimeoutReceive {  };
            (ReceiveResult::Fail, Ghost(dummy))
        },
        NetcReceiveResult::TimedOut {  } => {
            (ReceiveResult::Timeout, Ghost(NetEvent::TimeoutReceive {  }))
        },
        NetcReceiveResult::Received { sender, message } => {
            let csinglemessage = sht_demarshall_data_method(&message);
            assert(csinglemessage is Message ==> csinglemessage@ == sht_demarshal_data(message@)@);
            let src_ep = sender;
            let cpacket = CPacket {
                dst: local_addr.clone_up_to_view(),
                src: src_ep,
                msg: csinglemessage,
            };
            let ghost net_event: NetEvent = LIoOp::Receive {
                r: LPacket { dst: local_addr@, src: src_ep@, msg: message@ },
            };
            assert(cpacket.dst@ == local_addr@);
            assert(cpacket.src.abstractable());
            assert(cpacket.abstractable());

            proof {
                let ghost gsinglemessage = csinglemessage;
                if !(gsinglemessage is InvalidMessage) {
                    let lp = LPacket {
                        dst: local_addr@,
                        src: src_ep@,
                        msg: (sht_demarshal_data(message@))@,
                    };
                    assert(lp == abstractify_net_packet_to_lsht_packet(
                        net_event.arrow_Receive_r(),
                    ));
                    let p = Packet { dst: lp.dst, src: lp.src, msg: lp.msg };
                    assert(p == abstractify_net_packet_to_sht_packet(net_event.arrow_Receive_r()));

                    assert(!(gsinglemessage is InvalidMessage));
                    assert(gsinglemessage@ == (sht_demarshal_data(message@))@);
                    assert(cpacket@.dst =~= p.dst);
                    assert(cpacket@.src =~= p.src);
                    assert(cpacket@.msg =~= p.msg);
                    assert(cpacket@ =~= p);
                    assert(cpacket@ == abstractify_net_packet_to_sht_packet(
                        net_event.arrow_Receive_r(),
                    ));
                    assert(gsinglemessage is Message ==> cpacket.msg@ == sht_demarshal_data(
                        net_event.arrow_Receive_r().msg,
                    )@);
                }
            }
            (ReceiveResult::Packet { cpacket }, Ghost(net_event))
        },
    }
}

fn take_buf(buf: &mut Vec<u8>) {
}

/// Impl.SHT.PacketParsing.OutboundPacketsIsValid, which curiously doesn't involve the notion of
/// valid()
pub open spec fn outbound_packet_is_valid(cpacket: &CPacket) -> bool {
    &&& cpacket.abstractable()  // CPacketIsAbstractable
    &&& cpacket.msg.is_marshalable()  // CSingleMessageMarshallable
    &&& !(
    cpacket.msg is InvalidMessage)  // (out.msg.CSingleMessage? || out.msg.CAck?)

}

pub open spec fn send_log_entry_reflects_packet(event: NetEvent, cpacket: &CPacket) -> bool {
    &&& event is Send
    &&& true  // NetPacketIsAbstractable == EndPointIsAbstractable == true
    &&& cpacket.abstractable()
    &&& cpacket@ == abstractify_net_packet_to_sht_packet(event.arrow_Send_s())
}

//impl EventResults {
//    pub open spec fn singleton_send(net_event: NetEvent) -> EventResults
//    {
//        EventResults{
//            recvs: seq!(),
//            clocks: seq!(),
//            sends: seq!(net_event),
//            ios: seq!(net_event),
//        }
//    }
//}
pub fn send_packet(cpacket: &CPacket, netc: &mut NetClient) -> (rc: (bool, Ghost<Option<NetEvent>>))
    requires
        old(netc).ok(),
        outbound_packet_is_valid(cpacket),
        cpacket.src@ == old(netc).my_end_point(),  // OutboundPacketsSeqHasCorrectSrc

    ensures
        netc.my_end_point() == old(netc).my_end_point(),
        ({
            let (ok, Ghost(net_event)) = rc;
            {
                &&& netc.ok() <==> ok
                &&& ok ==> net_event is Some
                &&& ok ==> netc.history() == old(netc).history() + seq![net_event.unwrap()]
                &&& ok ==> rc.1@ is Some && send_log_entry_reflects_packet(
                    net_event.unwrap(),
                    &cpacket,
                ) && is_marshalable_data(net_event.unwrap())
            }
        }),
{
    let mut buf: Vec<u8> = Vec::new();
    cpacket.msg.serialize(&mut buf);
    // witness that buf@.len() < 2^64
    let _ = buf.len();
    match netc.send(&cpacket.dst, &buf) {
        Ok(_) => {
            let ghost lpacket = LPacket::<AbstractEndPoint, Seq<u8>> {
                dst: cpacket.dst@,
                src: cpacket.src@,
                msg: buf@,
            };
            let ghost net_event = LIoOp::Send { s: lpacket };

            proof {
                assert_seqs_equal!( buf@ == cpacket.msg.ghost_serialize() );
                assert(net_packet_bound(buf@));
                let purported_cpacket = sht_demarshal_data(buf@);
                sht_marshal_data_injective(&cpacket.msg, &purported_cpacket);
            }
            (true, Ghost(Some(net_event)))
        },
        Err(_) => { (false, Ghost(None)) },
    }
}

pub open spec fn outbound_packet_seq_is_valid(cpackets: Seq<CPacket>) -> bool {
    forall|i| 0 <= i < cpackets.len() ==> #[trigger] outbound_packet_is_valid(&cpackets[i])
}

pub open spec fn outbound_packet_seq_has_correct_srcs(
    cpackets: Seq<CPacket>,
    end_point: AbstractEndPoint,
) -> bool {
    forall|i| #![auto] 0 <= i < cpackets.len() ==> cpackets[i].src@ == end_point
}

pub open spec fn net_packet_bound(data: Seq<u8>) -> bool {
    data.len() <= 0xffff_ffff_ffff_ffff
}

pub open spec fn is_marshalable_data(event: NetEvent) -> bool
    recommends
        event is Send,
{
    &&& net_packet_bound(event.arrow_Send_s().msg)
    &&& sht_demarshal_data(event.arrow_Send_s().msg).is_marshalable()
}

pub open spec fn only_sent_marshalable_data(rawlog: Seq<NetEvent>) -> bool {
    forall|i|
        0 <= i < rawlog.len() && rawlog[i] is Send ==> #[trigger] is_marshalable_data(rawlog[i])
}

/// translates SendLogReflectsPacket
pub open spec fn send_log_entries_reflect_packets(
    net_event_log: Seq<NetEvent>,
    cpackets: Seq<CPacket>,
) -> bool {
    &&& net_event_log.len() == cpackets.len()
    &&& (forall|i|
        0 <= i < cpackets.len() ==> #[trigger] send_log_entry_reflects_packet(
            net_event_log[i],
            &cpackets[i],
        ))
}

#[verifier(spinoff_prover)]  // suddenly this is taking a long time due to an unrelated change elsewhere
pub fn send_packet_seq(cpackets: &Vec<CPacket>, netc: &mut NetClient) -> (rc: (
    bool,
    Ghost<Seq<NetEvent>>,
))
    requires
        old(netc).ok(),
        outbound_packet_seq_is_valid(cpackets@),
        outbound_packet_seq_has_correct_srcs(cpackets@, old(netc).my_end_point()),
    ensures
        netc.my_end_point() == old(netc).my_end_point(),
        ({
            let (ok, Ghost(net_events)) = rc;
            {
                &&& netc.ok() <==> ok
                &&& ok ==> netc.history() == old(netc).history() + net_events
                &&& ok ==> send_log_entries_reflect_packets(net_events, cpackets@)
                &&& ok ==> only_sent_marshalable_data(net_events)
                &&& forall|i| 0 <= i < net_events.len() ==> net_events[i] is Send
            }
        }),
{
    let ghost net_events = Seq::<NetEvent>::empty();
    assert(netc.history() == old(netc).history() + net_events);

    let mut i: usize = 0;
    while i < cpackets.len()
        invariant
            i <= cpackets.len(),
            outbound_packet_seq_is_valid(cpackets@),
            outbound_packet_seq_has_correct_srcs(cpackets@, old(netc).my_end_point()),
            netc.my_end_point() == old(netc).my_end_point(),
            netc.ok(),
            netc.history() == old(netc).history() + net_events,
            send_log_entries_reflect_packets(net_events, cpackets@.subrange(0, i as int)),
            only_sent_marshalable_data(net_events),
            forall|i| 0 <= i < net_events.len() ==> net_events[i] is Send,
    {
        let cpacket: &CPacket = &cpackets[i];
        let (ok, Ghost(net_event)) = send_packet(cpacket, netc);
        if !ok {
            return (false, Ghost(Seq::<NetEvent>::empty()));
        }
        i = i + 1;
        proof {
            let net_event = net_event.unwrap();
            let net_events0 = net_events;
            net_events = net_events + seq![net_event];
            let cpackets_prefix = cpackets@.subrange(0, i as int);
            assert forall|j| 0 <= j < i as int implies #[trigger] send_log_entry_reflects_packet(
                net_events[j],
                &cpackets_prefix[j],
            ) by {
                if j == i - 1 {
                    assert(net_events[j] == net_event);
                } else {
                    assert(cpackets_prefix[j] == cpackets@.subrange(0, i - 1 as int)[j]);
                }
            }
            assert forall|j|
                0 <= j < net_events.len()
                    && net_events[j] is Send implies #[trigger] is_marshalable_data(
                net_events[j],
            ) by {
                assert(send_log_entry_reflects_packet(net_events[j], &cpackets_prefix[j]));
                if j == i - 1 {
                    assert(net_events[j] == net_event);
                } else {
                    assert(net_events[j] == net_events0[j]);
                }
            }
            assert(netc.history() == old(netc).history() + net_events);
        }
    }
    proof {
        assert_seqs_equal!(cpackets@.subrange(0, cpackets@.len() as int), cpackets@);
    }
    (true, Ghost(net_events))
}

} // verus!
