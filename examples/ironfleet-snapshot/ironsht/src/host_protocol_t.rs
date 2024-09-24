#![verus::trusted]
use vstd::prelude::*;

use builtin::*;
use builtin_macros::*;

use crate::abstract_end_point_t::*;
use crate::abstract_parameters_t::*;
use crate::abstract_service_t::*;
use crate::app_interface_t::*;
use crate::args_t::*;
use crate::delegation_map_t::*;
use crate::environment_t::*;
use crate::io_t::*;
use crate::keys_t::*;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_delivery_t::*;
use crate::single_message_t::*;

// Protocol/SHT/Host.i.dfy

verus! {

// TODO Try translating this into *_state_machine!{} form
// This ports Protocol/LiveSHT/RefinementProof/Environment ::LSHTIo
pub type LSHTIo = LIoOp<AbstractEndPoint, SingleMessage<Message>>;

// This ports Protocol/LiveSHT/RefinementProof/Environment ::LSHTPacket
pub use crate::net_sht_v::LSHTPacket;

pub type AbstractIos = Seq<LSHTIo>;

pub struct AbstractConstants {
    pub root_identity: AbstractEndPoint,
    pub host_ids: Seq<AbstractEndPoint>,
    pub params: AbstractParameters,
    pub me: AbstractEndPoint,
}

pub struct AbstractHostState {
    pub constants: AbstractConstants,
    pub delegation_map: AbstractDelegationMap,
    pub h: Hashtable,
    pub sd: SingleDelivery<Message>,
    pub received_packet: Option<Packet>,
    pub num_delegations: int,  // TODO nat?
    pub received_requests: Seq<
        AppRequest,
    >,
    // We decided to elide resendCount and nextActionIndex from this translated spec
    // because they're only relevant to liveness.
}

impl AbstractHostState {
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.delegation_map.is_complete()
    }
}

// Protocol/SHT/Host.i.dfy max_hashtable_size()
pub open spec fn max_hashtable_size() -> int {
    62
}

// Ports Impl/SHT/PacketParsing.i.dfy :: ValidHashtable
pub open spec fn valid_hashtable(h: Hashtable) -> bool {
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall|k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

pub open spec(checked) fn hashtable_lookup(h: Hashtable, k: AbstractKey) -> Option<AbstractValue> {
    if h.dom().contains(k) {
        Some(h[k])
    } else {
        None
    }
}

// Protocol/SHT/Delegations.i.dfy BulkUpdateDomain
pub open spec(checked) fn bulk_update_domain(
    h: Hashtable,
    kr: KeyRange<AbstractKey>,
    u: Hashtable,
) -> Set<AbstractKey> {
    Set::<AbstractKey>::new(
        |k|
            (h.dom().contains(k) || u.dom().contains(k)) && (kr.contains(k) ==> u.dom().contains(
                k,
            )),
    )
}

// Protocol/SHT/Delegations.i.dfy BulkUpdateHashtable
pub open spec   /*(checked) because lambdas*/
fn bulk_update_hashtable(h: Hashtable, kr: KeyRange<AbstractKey>, u: Hashtable) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| bulk_update_domain(h, kr, u).contains(k),
        |k: AbstractKey|
            if u.dom().contains(k) {
                u[k]
            } else {
                h[k]
            },
    )
}

// Impl/SHT/HostModel.i.dfy BulkRemoveHashtable
pub open spec   /*(checked) because lambdas*/
fn bulk_remove_hashtable(h: Hashtable, kr: KeyRange<AbstractKey>) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| h.dom().contains(k) && !kr.contains(k),
        |k: AbstractKey| h[k],
    )
}

pub open spec(checked) fn valid_optional_value(ov: Option<AbstractValue>) -> bool {
    match ov {
        None => true,
        Some(value) => valid_value(value),
    }
}

// In Ironfleet, proving liveness demands that we not simply willy-nilly reject packets we don't like.
// However, in this port, we used a freshly-written general marshalling library. It's a good
// library, but it didn't happen to provide support for proving that, if demarshal(bytes) fails,
// then no structured message marshals to those bytes. Since we're not proving liveness of this
// implementation, we instead provide this placeholder marker for where the implementation is
// unable to prove demarshaling invertibility.
#[verifier::opaque]
pub open spec fn okay_to_ignore_packets() -> bool {
    true
}

pub proof fn workaround_dermarshal_not_invertible()
    ensures
        okay_to_ignore_packets(),
{
    reveal(okay_to_ignore_packets);
}

pub open spec(checked) fn receive_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
    ack: Packet,
) -> bool {
    ||| {
        &&& pre.received_packet is None  // No packet currently waiting to be processed (buffered in my state)
        // Record incoming packet in my state and possibly ack it
        &&& SingleDelivery::receive(pre.sd, post.sd, pkt, ack, out)
        &&& if SingleDelivery::new_single_message(pre.sd, pkt) {
            post.received_packet == Some(pkt)  // Enqueue this packet for processing

        } else {
            post.received_packet is None
        }
        &&& post == AbstractHostState {
            sd: post.sd,
            received_packet: post.received_packet,
            ..post
        }  // Nothing else changes

    }||| {
        // internal buffer full or okay to ignore packets; drop this message and wait for it to be retransmitted.
        &&& pre.received_packet is Some || okay_to_ignore_packets()
        &&& post == pre
        &&& out == Set::<Packet>::empty()
    }
}

// Translates Protocol/LiveSHT/Scheduler.i.dfy :: ExtractSentPacketsFromIos
pub open spec fn extract_sent_packets_from_ios(ios: Seq<LSHTIo>) -> Seq<LSHTPacket> {
    ios.filter(|io: LSHTIo| io is Send).map_values(|io: LSHTIo| io.arrow_Send_s())
}

// Protocol/SHT/Host.i.dfy :: LSHTPacketToPacket
pub open spec fn extract_packet_from_lsht_packet(lp: LSHTPacket) -> Packet {
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

// Translates Protocol/SHT/Host.i.dfy :: ExtractPacketsFromLSHTPackets
pub open spec fn extract_packets_from_lsht_packets(seq_packets: Seq<LSHTPacket>) -> Set<Packet> {
    seq_packets.map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)).to_set()
}

// Translates ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios))
pub open spec fn extract_packets_from_abstract_ios(ios: AbstractIos) -> Set<Packet> {
    extract_packets_from_lsht_packets(extract_sent_packets_from_ios(ios))
}

// Protocol/LiveSHT/Scheduler.i.dfy ::ReceivePacket_Wrapper
// nb: Dafny split this out to enable easy triggering of this exists
pub open spec(checked) fn receive_packet_wrapper(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    sent_packets: Set<Packet>,
) -> bool {
    exists|ack| receive_packet(pre, post, pkt, sent_packets, ack)
}

// Protocol/LiveSHT/Scheduler.i.dfy ::LHost_ReceivePacketWithoutReadingClock
pub open spec(checked) fn receive_packet_without_reading_clock(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool
    recommends
        ios.len() >= 1,
        ios[0] is Receive,
        pre.delegation_map.is_complete(),
{
    let r = ios[0].arrow_Receive_r();
    let pkt = Packet { dst: r.dst, src: r.src, msg: r.msg };
    let sent_packets = extract_packets_from_abstract_ios(ios);
    receive_packet_wrapper(pre, post, pkt, sent_packets)
}

// Protocol/LiveSHT/Scheduler.i.dfy ::LHost_ReceivePacket_Next
pub open spec(checked) fn receive_packet_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() >= 1
    &&& if ios[0] is TimeoutReceive {
        &&& post == pre
        &&& ios.len() == 1
    } else {
        &&& pre.delegation_map.is_complete()
        &&& ios[0] is Receive
        &&& forall|i| 1 <= i < ios.len() ==>   /*#[trigger]*/ ios[i] is Send
        &&& receive_packet_without_reading_clock(pre, post, ios)
    }
}

pub open spec(checked) fn next_get_request_reply(
    pre: AbstractHostState,
    post: AbstractHostState,
    src: AbstractEndPoint,
    seqno: nat,
    k: AbstractKey,
    sm: SingleMessage<Message>,
    m: Message,
    out: Set<Packet>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    let owner = pre.delegation_map[k];
    if should_send && valid_key(k) {
        &&& if owner == pre.constants.me {
            &&& m == Message::Reply { key: k, value: hashtable_lookup(pre.h, k) }
            &&& post.received_requests == pre.received_requests.push(
                AppRequest::AppGetRequest { seqno, key: k },
            )
        } else {
            &&& m == Message::Redirect { key: k, id: owner }
            &&& post.received_requests == pre.received_requests
        }
        &&& SingleDelivery::send_single_message(
            pre.sd,
            post.sd,
            m,
            src,
            Some(sm),
            pre.constants.params,
        )
        &&& sm.arrow_Message_dst() == src
        &&& out == set![ Packet{dst: src, src: pre.constants.me, msg: sm} ]
    } else {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn next_get_request(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is GetRequest
    &&& post.delegation_map == pre.delegation_map
    &&& post.h == pre.h
    &&& post.num_delegations == pre.num_delegations
    &&& (exists|sm, m, b|
        next_get_request_reply(
            pre,
            post,
            pkt.src,
            pkt.msg.arrow_Message_seqno(),
            pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
            sm,
            m,
            out,
            b,
        ))
}

// Protocol/SHT/Host.i.dfy :: NextSetRequest_Complete
pub open spec(checked) fn next_set_request_complete(
    pre: AbstractHostState,
    post: AbstractHostState,
    src: AbstractEndPoint,
    seqno: nat,
    reqm: Message,
    sm: SingleMessage<Message>,
    replym: Message,
    out: Set<Packet>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
        reqm is SetRequest,
{
    let k = reqm.arrow_SetRequest_key();
    let ov = reqm.arrow_SetRequest_value();
    let owner = pre.delegation_map[k];
    if should_send && valid_key(k) && valid_optional_value(ov) {
        &&& if owner == pre.constants.me {
            &&& post.h == match ov {
                None => pre.h.remove(k),
                Some(v) => pre.h.insert(k, v),
            }
            &&& replym == Message::Reply { key: k, value: ov }
            &&& post.received_requests == pre.received_requests.push(
                AppRequest::AppSetRequest { seqno: seqno, key: k, ov: ov },
            )
        } else {
            &&& post.h == pre.h
            &&& replym == Message::Redirect { key: k, id: owner }
            &&& post.received_requests == pre.received_requests
        }
        &&& SingleDelivery::send_single_message(
            pre.sd,
            post.sd,
            replym,
            src,
            Some(sm),
            pre.constants.params,
        )
        &&& sm.arrow_Message_dst() == src
        &&& out == set![Packet{dst: src, src: pre.constants.me, msg: sm}]
    } else {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    }
}

// Protocol/SHT/Host.i.dfy :: NextSetRequest
pub open spec(checked) fn next_set_request(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is SetRequest
    &&& exists|sm: SingleMessage<Message>, replym: Message, should_send: bool|
        next_set_request_complete(
            pre,
            post,
            pkt.src,
            pkt.msg.arrow_Message_seqno(),
            pkt.msg.arrow_Message_m(),
            sm,
            replym,
            out,
            should_send,
        )
    &&& post.delegation_map == pre.delegation_map
    &&& post.num_delegations == pre.num_delegations
}

// Protocol/SHT/Host.i.dfy :: NextDelegate
pub open spec(checked) fn next_delegate(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Delegate
    &&& if pre.constants.host_ids.contains(pkt.src) {
        let m = pkt.msg.arrow_Message_m();
        &&& post.delegation_map == pre.delegation_map.update(
            m.arrow_Delegate_range(),
            pre.constants.me,
        )
        &&& post.h == bulk_update_hashtable(pre.h, m.arrow_Delegate_range(), m.arrow_Delegate_h())
        &&& post.num_delegations == pre.num_delegations + 1
    } else {
        &&& post.delegation_map == pre.delegation_map
        &&& post.h == pre.h
        &&& post.num_delegations == pre.num_delegations
    }
    &&& SingleDelivery::<Message>::send_no_message(pre.sd, post.sd)
    &&& SingleDelivery::<Message>::receive_no_message(pre.sd, post.sd)
    &&& out == Set::<Packet>::empty()
    &&& post.received_requests == pre.received_requests
}

// Protocol/SHT/Host.i.dfy NextShard
pub open spec(checked) fn next_shard(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
    kr: KeyRange<AbstractKey>,
    recipient: AbstractEndPoint,
    sm: SingleMessage<Message>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    &&& recipient != pre.constants.me
    &&& pre.constants.host_ids.contains(recipient)
    &&& pre.delegation_map.delegate_for_key_range_is_host(kr, pre.constants.me)
    &&& SingleDelivery::send_single_message(
        pre.sd,
        post.sd,
        Message::Delegate { range: kr, h: extract_range(pre.h, kr) },
        recipient,
        if should_send {
            Some(sm)
        } else {
            None
        },
        pre.constants.params,
    )
    &&& should_send ==> recipient == sm.arrow_Message_dst()
    &&& pre.constants == post.constants
    &&& post.num_delegations == pre.num_delegations + 1
    &&& post.received_requests == pre.received_requests
    &&& if should_send {
        &&& out == set![Packet{dst: recipient, src: pre.constants.me, msg: sm}]
        &&& post.delegation_map == pre.delegation_map.update(kr, recipient)
        &&& post.h == bulk_remove_hashtable(pre.h, kr)
    } else {
        &&& out == Set::<Packet>::empty()
        &&& post.delegation_map == pre.delegation_map
        &&& post.h == pre.h
    }
}

pub open spec   /*(checked)*/
fn next_shard_wrapper_must_reject(pre: AbstractHostState, m: Message) -> bool {
    let recipient = m.arrow_Shard_recipient();
    let kr = m.arrow_Shard_range();
    ||| recipient == pre.constants.me
    ||| !recipient.valid_physical_address()
    ||| kr.is_empty()
    ||| !pre.constants.host_ids.contains(recipient)
    ||| !pre.delegation_map.delegate_for_key_range_is_host(kr, pre.constants.me)
    ||| extract_range(pre.h, kr).dom().len() >= max_hashtable_size()
}

// Protocol/SHT/Host.i.dfy NextShard_Wrapper
pub open spec(checked) fn next_shard_wrapper(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    let m: Message = pkt.msg.arrow_Message_m();
    let recipient = m.arrow_Shard_recipient();
    let kr = m.arrow_Shard_range();

    &&& m is Shard
    &&& if next_shard_wrapper_must_reject(pre, m) {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    } else {
        exists|sm: SingleMessage<Message>, b: bool| next_shard(pre, post, out, kr, recipient, sm, b)
    }
}

// Protocol/SHT/Host.i.dfy :: NextReply
pub open spec(checked) fn next_reply(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Reply
    &&& out == Set::<Packet>::empty()
    &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
}

// Protocol/SHT/Host.i.dfy :: NextRedirect
pub open spec(checked) fn next_redirect(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Redirect
    &&& out == Set::<Packet>::empty()
    &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
}

pub open spec(checked) fn should_process_received_message(pre: AbstractHostState) -> bool {
    &&& pre.received_packet.is_some()
    &&& pre.received_packet.arrow_Some_0().msg is Message
    &&& {
        ||| pre.received_packet.arrow_Some_0().msg.arrow_Message_m() is Delegate
        ||| pre.received_packet.arrow_Some_0().msg.arrow_Message_m() is Shard
    } ==> pre.num_delegations < pre.constants.params.max_delegations - 2
}

pub open spec(checked) fn process_message(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    if should_process_received_message(pre) {
        let packet = pre.received_packet.arrow_Some_0();
        &&& {
            ||| next_get_request(pre, post, packet, out)
            ||| next_set_request(pre, post, packet, out)
            ||| next_delegate(pre, post, packet, out)
            ||| next_shard_wrapper(pre, post, packet, out)
            ||| next_reply(pre, post, packet, out)
            ||| next_redirect(pre, post, packet, out)
        }
        &&& post.received_packet is None
    } else {
        &&& post == pre
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn process_received_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    match pre.received_packet {
        Some(_) => process_message(pre, post, out),
        None => {
            &&& post == pre
            &&& out == Set::<Packet>::empty()
        },
    }
}

// Translates Protocol/LiveSHT/Scheduler.i.dfy :: LHost_ProcessReceivedPacket_Next
pub open spec(checked) fn process_received_packet_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& forall|i| 0 <= i < ios.len() ==> ios[i] is Send
    &&& process_received_packet(pre, post, extract_packets_from_abstract_ios(ios))
}

pub open spec(checked) fn spontaneously_retransmit(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool {
    &&& out == SingleDelivery::un_acked_messages(pre.sd, pre.constants.me)
    &&& post == pre
}

// Skips LHost_NoReceive_Next_Wrapper, which delays resends, and translates LHost_NoReceive_Next
pub open spec(checked) fn spontaneously_retransmit_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& {
        ||| {
            &&& forall|i| 0 <= i < ios.len() ==> ios[i] is Send
            &&& spontaneously_retransmit(pre, post, extract_packets_from_abstract_ios(ios))
        }
        ||| {
            &&& post == pre
            &&& ios =~= Seq::<LSHTIo>::empty()
        }
    }
}

// Translates Impl/LiveSHT/Unsendable HostNextIgnoreUnsendableReceive (inlining IosReflectIgnoringUnDemarshallable)
pub open spec(checked) fn ignore_unparseable_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() == 1
    &&& ios[0] is Receive
    &&& ios[0].arrow_Receive_r().msg is InvalidMessage
    &&& pre == post
}

// Translates Impl/LiveSHT/Unsendable HostNextIgnoreUnsendableProcess (inlining IosReflectIgnoringUnParseable)
pub open spec(checked) fn ignore_nonsensical_delegation_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() == 0
    &&& pre.received_packet.is_some()
    &&& pre.received_packet.arrow_Some_0().msg is Message
    &&& match pre.received_packet.arrow_Some_0().msg.arrow_Message_m() {
        Message::Delegate { range: range, h: h } => !({
            // no need to check for valid_key_range(range)
            // (See Distributed/Services/SHT/AppInterface.i.dfy: ValidKey() == true)
            &&& valid_hashtable(h)
            &&& !range.is_empty()
            &&& pre.received_packet.arrow_Some_0().msg.arrow_Message_dst().valid_physical_address()
        }),
        _ => false,
    }
    &&& if should_process_received_message(pre) {
        post == AbstractHostState { received_packet: None, ..pre }
    } else {
        post == pre
    }
}

pub enum Step {
    ReceivePacket,
    ProcessReceivedPacket,
    SpontaneouslyRetransmit,
    Stutter,  // Allowed by LHost_NoReceive_Next_Wrapper when resendCount != 0
    IgnoreUnparseablePacket,
    IgnoreNonsensicalDelegationPacket,
}

pub open spec fn parse_arg_as_end_point(arg: AbstractArg) -> AbstractEndPoint {
    AbstractEndPoint { id: arg }
}

pub open spec fn unchecked_parse_args(args: AbstractArgs) -> Seq<AbstractEndPoint> {
    args.map(|idx, arg: AbstractArg| parse_arg_as_end_point(arg))
}

pub open spec(checked) fn parse_args(args: AbstractArgs) -> Option<Seq<AbstractEndPoint>> {
    let end_points = unchecked_parse_args(args);
    if forall|i| #![auto] 0 <= i < end_points.len() ==> end_points[i].valid_physical_address() {
        Some(end_points)
    } else {
        None
    }
}

// Ironfleet's trusted spec left ParseCommandLineConfiguration unspecified, which was an auditing
// hole. Here we're going to define the parsing in the trusted domain.
pub open spec(checked) fn init(
    pre: AbstractHostState,
    id: AbstractEndPoint,
    args: AbstractArgs,
) -> bool {
    let end_points = parse_args(args);
    if end_points is None || end_points.unwrap().len() == 0 {
        false
    } else {
        let root_identity = end_points.unwrap()[0];
        let params = AbstractParameters::static_params();
        pre == AbstractHostState {
            constants: AbstractConstants {
                root_identity,
                host_ids: end_points.unwrap(),
                params,
                me: id,
            },
            delegation_map: AbstractDelegationMap::init(root_identity),
            h: Map::empty(),
            sd: SingleDelivery::init(),
            received_packet: None,
            num_delegations: 1,  // TODO nat?
            received_requests: seq![],
        }
    }
}

// This translates Distributed/Protocol/SHT/Host.i.dfy
pub open spec(checked) fn next_step(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
    step: Step,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& match step {
        Step::ReceivePacket => receive_packet_next(pre, post, ios),
        Step::ProcessReceivedPacket => process_received_packet_next(pre, post, ios),
        Step::SpontaneouslyRetransmit => spontaneously_retransmit_next(pre, post, ios),
        Step::Stutter => pre == post && ios.len() == 0,  // See LHost_NoReceive_Next_Wrapper when resendCount != 0
        Step::IgnoreUnparseablePacket => ignore_unparseable_packet(pre, post, ios),
        Step::IgnoreNonsensicalDelegationPacket => ignore_nonsensical_delegation_packet(
            pre,
            post,
            ios,
        ),
    }
}

//pub open no_invalid_messages fn next(pre: AbstractHostState, post: AbstractHostState, recv: Set<Packet>, out: Set<Packet>) -> bool {
pub open spec(checked) fn no_invalid_sends(ios: AbstractIos) -> bool {
    forall|i|
        #![auto]
        0 <= i < ios.len() && ios[i] is Send ==> !(ios[i].arrow_Send_s().msg is InvalidMessage)
}

pub open spec(checked) fn next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.wf()
    &&& pre.constants == post.constants
    &&& exists|step| next_step(pre, post, ios, step)
    &&& no_invalid_sends(
        ios,
    )  // A double check that our trusted translation of Host satisfies OnlySentMarshallableData

}

} // verus!
