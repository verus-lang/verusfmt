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
use crate::marshal_v::*;
use crate::message_t::*;
use crate::net_sht_v::*;
use crate::network_t::*;
use crate::seq_is_unique_v::*;
use crate::single_delivery_model_v::*;
use crate::single_delivery_state_v::*;
use crate::single_delivery_t::*;
use crate::single_message_t::*;
use crate::verus_extra::clone_v::*;
use crate::verus_extra::seq_lib_v::*;
use crate::verus_extra::set_lib_ext_v::*;
use vstd::assert_by_contradiction;
use vstd::bytes::*;
use vstd::calc_macro::*;
use vstd::map::*; // TODO: prelude doesn't supply the macros?
use vstd::prelude::*;
use vstd::seq_lib::*; // TODO: prelude doesn't supply the macros?
use vstd::set::*;
use vstd::set_lib::*; // TODO: prelude doesn't supply the macros?

use crate::host_impl_t::*; // need some definitions from Rust

verus! {

/*
 This file ports this call stack from Ironfleet

 Distributed/Common/Framework::IronfleetMain.s (trusted) -> host_impl_t

 Impl/LiveSHT/Host::HostNextImpl
 Impl/LiveSHT/SchedulerImpl::Host_Next_main
 Impl/LiveSHT/SchedulerImpl::Host_ProcessReceivedPacket_Next
 Impl/SHT/HostModel::HostModelNextReceiveMessage
 Impl/SHT/HostModel::HostModelNextGetRequest

 */
pub struct Constants {
    pub root_identity: EndPoint,
    pub host_ids: Vec<EndPoint>,
    pub params: Parameters,
    pub me: EndPoint,
}

impl Constants {
    pub open spec fn view(self) -> AbstractConstants {
        AbstractConstants {
            root_identity: self.root_identity@,
            host_ids: abstractify_end_points(self.host_ids),
            params: self.params@,
            me: self.me@,
        }
    }

    pub closed spec fn abstractable(self) -> bool {
        true
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.params.valid()
        &&& seq_is_unique(abstractify_end_points(self.host_ids))
        &&& self.root_identity@.valid_physical_address()
    }
}

pub struct Parameters {
    pub max_seqno: u64,
    pub max_delegations: u64,
}

impl Parameters {
    pub open spec fn view(self) -> AbstractParameters {
        AbstractParameters {
            max_seqno: self.max_seqno as nat,
            max_delegations: self.max_delegations as nat,
        }
    }

    // Translates Impl/SHT/Parameters::StaticParams
    pub fn static_params() -> (out: Parameters)
        ensures
            out@ == AbstractParameters::static_params(),
    {
        Parameters { max_seqno: 0xffff_ffff_ffff_ffff, max_delegations: 0x7FFF_FFFF_FFFF_FFFF }
    }

    // Translates Impl/SHT/Parameters.i.dfy :: CParametersIsValid
    pub open spec fn valid(self) -> bool {
        &&& self.max_seqno == 0xffff_ffff_ffff_ffff
        &&& 3 < self.max_delegations
        &&& self.max_delegations < 0x8000_0000_0000_0000
    }
}

// Translates Impl/LiveSHT/SchedulerModel.i.dfy :: AllIosAreSends
pub open spec fn all_ios_are_sends(ios: Seq<LSHTIo>) -> bool {
    forall|i: int| 0 <= i && i < ios.len() ==> ios[i] is Send
}

// Translates Impl/SHT/PacketParsing.i.dfy :: AbstractifyCPacketToLSHTPacket
pub open spec fn abstractify_cpacket_to_lsht_packet(cp: CPacket) -> LSHTPacket
    recommends
        cp.abstractable(),
{
    LPacket { dst: cp.dst@, src: cp.src@, msg: cp.msg@ }
}

// Translates Impl/LiveSHT/SchedulerModel.i.dfy :: MapSentPacketSeqToIos
pub open spec fn map_sent_packet_seq_to_ios(sent_packets: Seq<CPacket>) -> Seq<LSHTIo> {
    sent_packets.map_values(
        |sent_packet: CPacket|
            LIoOp::<AbstractEndPoint, SingleMessage<Message>>::Send {
                s: abstractify_cpacket_to_lsht_packet(sent_packet),
            },
    )
}

// Translates Impl/LiveSHT/NetSHT.i.dfy :: AbstractifyRawLogToIos
pub open spec fn abstractify_raw_log_to_ios(rawlog: Seq<NetEvent>) -> Seq<LSHTIo> {
    rawlog.map_values(|evt: NetEvent| abstractify_net_event_to_lsht_io(evt))
}

// Translates Impl/LiveSHT/RawIoConsistentWithSpecIO
pub open spec fn raw_io_consistent_with_spec_io(rawlog: Seq<NetEvent>, ios: Seq<LSHTIo>) -> bool {
    &&& net_event_log_is_abstractable(rawlog)
    &&& abstractify_raw_log_to_ios(rawlog) == ios
}

pub fn make_empty_event_results() -> (res: Ghost<EventResults>)
    ensures
        res@.recvs == Seq::<NetEvent>::empty(),
        res@.clocks == Seq::<NetEvent>::empty(),
        res@.sends == Seq::<NetEvent>::empty(),
        res@.ios == Seq::<NetEvent>::empty(),
        extract_packets_from_abstract_ios(abstractify_raw_log_to_ios(res@.ios)) == Set::<
            Packet,
        >::empty(),
{
    let ghost res = EventResults {
        recvs: Seq::<NetEvent>::empty(),
        clocks: Seq::<NetEvent>::empty(),
        sends: Seq::<NetEvent>::empty(),
        ios: Seq::<NetEvent>::empty(),
    };
    proof {
        assert_sets_equal!(extract_packets_from_abstract_ios(abstractify_raw_log_to_ios(res.ios)),
                           Set::<Packet>::empty());
    }
    ;
    Ghost(res)
}

pub fn make_send_only_event_results(net_events: Ghost<Seq<NetEvent>>) -> (res: Ghost<EventResults>)
    requires
        forall|i: int| 0 <= i && i < net_events@.len() ==> net_events@[i] is Send,
    ensures
        res@.recvs == Seq::<NetEvent>::empty(),
        res@.clocks == Seq::<NetEvent>::empty(),
        res@.sends == net_events@,
        res@.ios == net_events@,
        res@.event_seq() == net_events@,
        res@.well_typed_events(),
{
    let ghost res = EventResults {
        recvs: Seq::<NetEvent>::empty(),
        clocks: Seq::<NetEvent>::empty(),
        sends: net_events@,
        ios: net_events@,
    };
    assert(forall|i| 0 <= i < res.recvs.len() ==> res.recvs[i] is Receive);
    assert(forall|i|
        0 <= i < res.clocks.len() ==> res.clocks[i] is ReadClock
            || res.clocks[i] is TimeoutReceive);
    assert(forall|i| 0 <= i < res.sends.len() ==> res.sends[i] is Send);
    assert(res.clocks.len() <= 1);
    assert(res.well_typed_events());
    proof {
        assert_seqs_equal!(res.event_seq(), net_events@);
    }
    ;
    Ghost(res)
}

pub struct HostState {
    // Fields from Impl/LiveSHT/SchedulerImpl::SchedulerImpl
    next_action_index: u64,
    resend_count: u64,
    // Fields from Impl/SHT/HostState::HostState
    constants: Constants,
    delegation_map: DelegationMap<CKey>,
    h: CKeyHashMap,
    sd: CSingleDelivery,
    received_packet: Option<CPacket>,
    num_delegations: u64,
    received_requests: Ghost<Seq<AppRequest>>,
}

/// Translates Distributed/Impl/SHT/HostModel.i ExtractRange
fn extract_range_impl(h: &CKeyHashMap, kr: &KeyRange<CKey>) -> (ext: CKeyHashMap)
    requires  //h@.valid_key_range()
// (See Distributed/Services/SHT/AppInterface.i.dfy: ValidKey() == true)

        forall|k|
            h@.contains_key(k) ==>   /*#[trigger] valid_key(k) &&*/
            #[trigger] valid_value(h@[k]),
    ensures
        ext@ =~= extract_range(h@, *kr),
{
    let exec_lambda = |key| -> (b: bool)
        ensures
            b == kr.contains(key),
        { kr.contains_exec(&key) };

    h.filter(exec_lambda, Ghost(|ak| kr.contains(ak)))
}

impl HostState {
    // AbstractHostState is the protocol host state
    pub closed spec fn view(self) -> AbstractHostState {
        AbstractHostState {
            constants: self.constants@,
            delegation_map: AbstractDelegationMap(self.delegation_map@),
            h: self.h@,
            sd: self.sd@,
            received_packet: match self.received_packet {
                None => None,
                Some(cpacket) => Some(cpacket@),
                // TODO(tej): add map to Verus Option
                // received_packet.map(|cpacket| cpacket@),
            },
            num_delegations: self.num_delegations as int,
            received_requests: self.received_requests@,
        }
    }

    pub closed spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
    }

    pub closed spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.delegation_map.valid()
        // TODO why no valid_key?
        &&& (forall|k| self.h@.dom().contains(k) ==> #[trigger] valid_value(self.h@[k]))
        &&& self.sd.valid()
        &&& match &self.received_packet {
            Some(v) => v.abstractable() && v.msg is Message && v.dst@ == self.constants.me@,
            None => true,
        }
        &&& self.constants.valid()
        &&& self.num_delegations
            < self.constants.params.max_delegations
        // TODO why no delegation_map.lows

    }

    /// Translates Impl/LiveSHT/Host.i.dfy :: HostStateInvariants
    ///
    /// Still many invariants missing; will be faulted in as proof is completed.
    pub closed spec fn invariants(&self, netc_end_point: &AbstractEndPoint) -> bool {
        &&& self.next_action_index < 3
        &&& self.delegation_map.valid()
        &&& self@.constants.me == netc_end_point
        &&& self.valid()
        &&& self@.constants.me.abstractable()
        &&& self.num_delegations
            < self.constants.params.max_delegations  // why did we move this here?
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

    fn parse_end_point(arg: &Arg) -> (out: EndPoint)
        ensures
            out@ == host_protocol_t::parse_arg_as_end_point(arg@),
    {
        EndPoint { id: clone_arg(arg) }
    }

    // translates Impl/Common/CmdLineParser parse_end_points
    fn parse_end_points(args: &Args) -> (out: Option<Vec<EndPoint>>)
        ensures
            match out {
                None => host_protocol_t::parse_args(abstractify_args(*args)) is None,
                Some(vec) => {
                    &&& host_protocol_t::parse_args(abstractify_args(*args)) is Some
                    &&& abstractify_end_points(vec) == host_protocol_t::parse_args(
                        abstractify_args(*args),
                    ).unwrap()
                },
            },
    {
        let mut end_points: Vec<EndPoint> = Vec::new();
        let mut i: usize = 0;

        while i < args.len()
            invariant
                i <= args.len(),
                end_points.len() == i,
                forall|j|
                    #![auto]
                    0 <= j < i ==> parse_arg_as_end_point(abstractify_args(*args)[j])
                        == end_points@[j]@,
                forall|j| #![auto] 0 <= j < i ==> end_points@[j]@.valid_physical_address(),
        {
            let end_point = Self::parse_end_point(&(*args)[i]);
            if !end_point.valid_physical_address() {
                assert(!unchecked_parse_args(
                    abstractify_args(*args),
                )[i as int].valid_physical_address());  // witness to !forall
                return None;
            }
            end_points.push(end_point);
            i = i + 1;
        }
        proof {
            assert_seqs_equal!(abstractify_end_points(end_points), unchecked_parse_args(abstractify_args(*args)));
        }
        Some(end_points)
    }

    //pub open spec fn parse_command_line_configuration_matches(args: &Args, me: EndPoint, rc: Option<Constants>)
    // TODO: In the IronFleet original, this parse method was part of the trusted application spec.
    // Somehow, in this port, it wound up being entirely verified. That may be because IronFleet
    // used this method in a trusted place in a different application, but it wasn't really TCB for
    // the KV app? May warrant further investigation.
    fn parse_command_line_configuration(args: &Args, me: EndPoint) -> (rc: Option<Constants>)
        ensures
            ({
                let abstract_end_points = parse_args(abstractify_args(*args));
                match rc {
                    None => {
                        ||| abstract_end_points.is_None()
                        ||| abstract_end_points.unwrap().len() == 0
                        ||| !seq_is_unique(abstract_end_points.unwrap())
                    },
                    Some(c) => {
                        &&& abstract_end_points.is_some()
                        &&& abstract_end_points.unwrap().len() > 0
                        &&& seq_is_unique(abstract_end_points.unwrap())
                        &&& c@ == AbstractConstants {
                            root_identity: abstract_end_points.unwrap()[0],
                            host_ids: abstract_end_points.unwrap(),
                            params: AbstractParameters::static_params(),
                            me: me@,
                        }
                    },
                }
            }),
    {
        let end_points = Self::parse_end_points(args);
        if matches!(end_points, None) {
            return None;
        }
        let abstract_end_points: Ghost<Option<Seq<AbstractEndPoint>>> = Ghost(
            parse_args(abstractify_args(*args)),
        );

        assert(abstract_end_points@.is_some());

        let end_points: Vec<EndPoint> = end_points.unwrap();
        if end_points.len() == 0 {
            return None;
        }
        assert(abstract_end_points@.unwrap().len() > 0);

        let unique = test_unique(&end_points);
        if !unique {
            return None;
        }
        let constants = Constants {
            root_identity: end_points[0].clone_up_to_view(),
            host_ids: end_points,
            params: Parameters::static_params(),
            me: me,
        };

        proof {
            assert(!(abstract_end_points@.is_None() || abstract_end_points@.unwrap().len() == 0));
            assert(abstract_end_points@.is_some());
            assert(abstract_end_points@.unwrap().len() > 0);
            assert(constants@.root_identity == abstract_end_points@.unwrap()[0]);
            assert(constants@.host_ids == abstract_end_points@.unwrap());
            assert(constants@.params == AbstractParameters::static_params());
            assert(constants@.me == me@);

            assert(constants@ == AbstractConstants {
                root_identity: abstract_end_points@.unwrap()[0],
                host_ids: abstract_end_points@.unwrap(),
                params: AbstractParameters::static_params(),
                me: me@,
            });

        }
        Some(constants)
    }

    // translates Impl/LiveSHT/SchedulerImpl :: Host_Init_Impl
    // and Impl/LiveSHT/Host ::
    pub fn real_init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
        requires
            netc.valid(),
        ensures
            Self::init_ensures(netc, *args, rc),
    {
        let me = netc.get_my_end_point();
        let constants =   /*Self -- Verus unimpl*/
        HostState::parse_command_line_configuration(args, me);
        if matches!(constants, None) {
            return None;
        }
        let constants = constants.unwrap();
        let spare_root = constants.root_identity.clone_up_to_view();
        let zero_key = SHTKey::zero();  //SHTKey{ukey: 0};   // for some reason we can't make this call inside the ::new method below
        assert(SHTKey::zero_spec() == zero_key);
        let host_state = HostState {
            next_action_index: 0,
            resend_count: 0,
            constants: constants,
            delegation_map: DelegationMap::new(  /*SHTKey::zero()*/
            zero_key, spare_root),
            h: CKeyHashMap::new(),
            sd: CSingleDelivery::empty(),
            received_packet: None,
            num_delegations: 1,
            received_requests: Ghost(Seq::<AppRequest>::empty()),
        };
        let rc = Some(host_state);
        assert(netc.ok());
        assert(host_state.invariants(&netc.my_end_point()));  // would pass some initial env state?
        assert(host_state@.delegation_map == AbstractDelegationMap::init(constants.root_identity@))
            by {
            reveal(HostState::view);
            assert_maps_equal!(host_state.delegation_map@, AbstractDelegationMap::init(constants.root_identity@)@);
            assert(host_state.delegation_map@ == AbstractDelegationMap::init(
                constants.root_identity@,
            )@);
        }
        assert(crate::host_protocol_t::init(
            host_state@,
            netc.my_end_point(),
            abstractify_args(*args),
        ));
        rc
    }

    // Translates Impl/LiveSHT/SchedulerImpl.i.dfy :: DeliverPacketSeq
    pub fn deliver_packet_seq(
        &self,
        netc: &mut NetClient,
        packets: &Vec<CPacket>,
    ) -> (rc: (bool, Ghost<Seq<NetEvent>>, Ghost<Seq<LSHTIo>>))
        requires
            old(netc).ok(),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, old(netc).my_end_point()),
        ensures
            netc.my_end_point() == old(netc).my_end_point(),
            ({
                let (ok, Ghost(net_events), Ghost(ios)) = rc;
                {
                    &&& netc.ok() <==> ok
                    &&& ok ==> {
                        &&& all_ios_are_sends(ios)
                        &&& (forall|i: int|
                            0 <= i && i < net_events.len() ==> net_events[i] is Send)
                        &&& ios == map_sent_packet_seq_to_ios(packets@)
                        &&& abstractify_outbound_packets_to_seq_of_lsht_packets(packets@)
                            == extract_sent_packets_from_ios(ios)
                        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@)
                            == extract_packets_from_abstract_ios(ios)
                        &&& no_invalid_sends(ios)
                        &&& raw_io_consistent_with_spec_io(net_events, ios)
                        &&& only_sent_marshalable_data(net_events)
                        &&& netc.history() == old(netc).history() + net_events
                    }
                }
            }),
    {
        let (ok, events) = send_packet_seq(packets, netc);
        if !ok {
            (ok, Ghost(Seq::<NetEvent>::empty()), Ghost(Seq::<LSHTIo>::empty()))
        } else {
            let ghost ios: Seq<LSHTIo> = map_sent_packet_seq_to_ios(packets@);
            proof {
                assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@)
                    == extract_packets_from_abstract_ios(ios)) by {
                    lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(
                        ios,
                        |io: LSHTIo| io is Send,
                    );
                    assert(ios.filter(|io: LSHTIo| io is Send) == ios);
                    let set1 = abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@);
                    let set2 = extract_packets_from_abstract_ios(ios);
                    let seq1 = packets@.map_values(|cp: CPacket| cp@);
                    let seq2 = extract_sent_packets_from_ios(ios).map_values(
                        |lp: LSHTPacket| extract_packet_from_lsht_packet(lp),
                    );
                    assert(set1 == seq1.to_set());
                    assert(set2 == seq2.to_set());
                    assert forall|x| set1.contains(x) implies set2.contains(x) by {
                        let idx: int = choose|idx: int|
                            0 <= idx && idx < seq1.len() && #[trigger] seq1[idx] == x;
                        assert(seq2[idx] == x);
                        assert(set2.contains(x));
                    };
                    assert forall|x| set2.contains(x) implies set1.contains(x) by {
                        let idx: int = choose|idx: int|
                            0 <= idx && idx < seq2.len() && #[trigger] seq2[idx] == x;
                        assert(seq1[idx] == x);
                        assert(set1.contains(x));
                    };
                    assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@),
                                       extract_packets_from_abstract_ios(ios));
                }
                assert(abstractify_outbound_packets_to_seq_of_lsht_packets(packets@)
                    == extract_sent_packets_from_ios(ios)) by {
                    lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(
                        ios,
                        |io: LSHTIo| io is Send,
                    );
                    assert(ios.filter(|io: LSHTIo| io is Send) == ios);
                    assert_seqs_equal!(abstractify_outbound_packets_to_seq_of_lsht_packets(packets@),
                                       extract_sent_packets_from_ios(ios));
                }
                assert(abstractify_raw_log_to_ios(events@) == ios) by {
                    let aios = abstractify_raw_log_to_ios(events@);
                    assert forall|i: int| 0 <= i && i < ios.len() implies aios[i] == ios[i] by {
                        assert(send_log_entry_reflects_packet(events@[i], &packets[i]));
                    }
                    assert_seqs_equal!(aios, ios);
                };
                assert forall|i| 0 <= i < ios.len() && #[trigger] ios[i] is Send implies !(
                ios[i]->s.msg is InvalidMessage) by {
                    let msg = ios[i]->s.msg;
                    assert(msg == abstractify_cpacket_to_lsht_packet(packets[i]).msg);
                    assert(outbound_packet_is_valid(&packets[i]));
                };
                assert forall|i: int| 0 <= i && i < events@.len() implies events@[i] is Send by {
                    assert(send_log_entry_reflects_packet(events@[i], &packets[i]));
                };
            }
            (ok, events, Ghost(ios))
        }
    }

    // Translates Impl/LiveSHT/SchedulerImpl.i.dfy :: DeliverOutboundPackets
    pub fn deliver_outbound_packets(
        &self,
        netc: &mut NetClient,
        packets: &Vec<CPacket>,
    ) -> (rc: (bool, Ghost<Seq<NetEvent>>, Ghost<Seq<LSHTIo>>))
        requires
            old(netc).ok(),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, old(netc).my_end_point()),
        ensures
            netc.my_end_point() == old(netc).my_end_point(),
            ({
                let (ok, Ghost(net_events), Ghost(ios)) = rc;
                {
                    &&& netc.ok() <==> ok
                    &&& ok ==> {
                        &&& all_ios_are_sends(ios)
                        &&& (forall|i: int|
                            0 <= i && i < net_events.len() ==> net_events[i] is Send)
                        &&& ios == map_sent_packet_seq_to_ios(packets@)
                        &&& abstractify_outbound_packets_to_seq_of_lsht_packets(packets@)
                            == extract_sent_packets_from_ios(ios)
                        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@)
                            == extract_packets_from_abstract_ios(ios)
                        &&& no_invalid_sends(ios)
                        &&& raw_io_consistent_with_spec_io(net_events, ios)
                        &&& only_sent_marshalable_data(net_events)
                        &&& netc.history() == old(netc).history() + net_events
                    }
                }
            }),
    {
        self.deliver_packet_seq(netc, packets)
    }

    // Impl/LiveSHT/SchedulerImpl.i.dfy Host_ReceivePacket_Next
    pub fn receive_packet_next(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
    {
        let ghost old_self: HostState = *self;
        let (rr, net_event) = receive_with_demarshal(netc, &self.constants.me);
        match rr {
            ReceiveResult::Fail {  } => {
                return (
                    false,
                    Ghost(
                        EventResults { recvs: seq![], clocks: seq![], sends: seq![], ios: seq![] },
                    ),
                );
            },
            ReceiveResult::Timeout {  } => {
                let iop: NetEvent = LIoOp::TimeoutReceive {  };
                let ghost res = EventResults {
                    recvs: seq![],
                    clocks: seq![iop],
                    sends: seq![],
                    ios: seq![iop],
                };
                proof {
                    old_self.delegation_map.valid_implies_complete();
                    assert(next_step(
                        old_self@,
                        self@,
                        abstractify_raw_log_to_ios(res.ios),
                        Step::ReceivePacket,
                    ));
                    assert(res.event_seq() == res.ios);
                }
                return (true, Ghost(res));  // iop should also appear as a clock?
            },
            ReceiveResult::Packet { cpacket } => {
                match cpacket.msg {
                    CSingleMessage::InvalidMessage {  } => {
                        let ghost res = EventResults {
                            recvs: seq![net_event@],
                            clocks: seq![],
                            sends: seq![],
                            ios: seq![net_event@],
                        };
                        proof {
                            old_self.delegation_map.valid_implies_complete();
                            let ios = abstractify_raw_log_to_ios(res.ios);
                            let r = ios[0]->r;
                            let pkt = Packet { dst: r.dst, src: r.src, msg: r.msg };
                            let sent_packets = extract_packets_from_abstract_ios(ios);
                            lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty(
                                ios,
                                |io: LSHTIo| io is Send,
                            );
                            assert(extract_sent_packets_from_ios(ios) =~= Seq::<
                                LSHTPacket,
                            >::empty());
                            assert(sent_packets =~= Set::<Packet>::empty());
                            workaround_dermarshal_not_invertible();
                            assert(host_protocol_t::receive_packet(
                                old(self)@,
                                self@,
                                pkt,
                                sent_packets,
                                arbitrary(),
                            ));
                            assert(receive_packet_wrapper(old(self)@, self@, pkt, sent_packets));
                            assert(receive_packet_without_reading_clock(
                                old(self)@,
                                self@,
                                abstractify_raw_log_to_ios(res.ios),
                            ));
                            assert(host_protocol_t::next_step(
                                old(self)@,
                                self@,
                                abstractify_raw_log_to_ios(res.ios),
                                Step::ReceivePacket,
                            ));
                            assert(res.event_seq() == res.ios);
                        }
                        return (true, Ghost(res));
                    },
                    _ => {
                        assert(*old(self) == *self);
                        let ghost mid_netc = *netc;
                        assert(netc.history() == old(netc).history().push(net_event@));
                        let (ok, Ghost(event_results), Ghost(ios)) = self.host_next_receive_packet(
                            netc,
                            Ghost(old(netc).history()),
                            cpacket,
                            Ghost(net_event@),
                        );

                        if !ok {
                            return (ok, Ghost(event_results));
                        }
                        let rc = (ok, Ghost(event_results));
                        assert(self.invariants(&netc.my_end_point()));
                        proof {
                            old(self).delegation_map.valid_implies_complete();
                        }
                        assert(host_protocol_t::next_step(
                            old(self)@,
                            self@,
                            ios,
                            Step::ReceivePacket,
                        ));
                        assert(Self::next(old(self)@, self@, event_results.ios));
                        rc
                    },
                }
            },
        }
    }

    // In the process of porting this, we found a bug in the Ironfleet spec, in Host.s.dfy. It
    // says:
    // ```
    // ensures  (ok || |sends| > 0) ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
    // ``
    // but this isn't strong enough. Indeed, in Dafny we were able to unwittingly
    // ``trick'' it by just setting the sends to empty. What it should say is that
    // if ok was false, then the env history reflects a prefix of the receives,
    // clocks, and sends we intended to perform, and the HostNext holds on the
    // full list of receives, clocks, and sends we intended to perform.
    //
    // In staying true to the original, this version "tricks the spec" in the same way that the
    // Ironfleet Dafny code did.
    proof fn empty_event_results() -> (event_results: EventResults)
        ensures
            event_results.well_typed_events(),
            event_results.ios =~= event_results.event_seq(),
            event_results.ios == Seq::<NetEvent>::empty(),
    {
        EventResults {
            recvs: Seq::<NetEvent>::empty(),
            clocks: Seq::<NetEvent>::empty(),
            sends: Seq::<NetEvent>::empty(),
            ios: Seq::<NetEvent>::empty(),
        }
    }

    /// Impl/LiveSHT/SchedulerImpl.i.dfy HostNextReceivePacket
    /// Here we've replaced the Dafny input parameter `rr` with `cpacket`, which represents `rr.cpacket`.
    #[verifier(spinoff_prover)]  // suddenly this is taking a long time due to an unrelated change elsewhere
    fn host_next_receive_packet(
        &mut self,
        netc: &mut NetClient,
        Ghost(old_netc_history): Ghost<Seq<NetEvent>>,
        cpacket: CPacket,
        Ghost(receive_event): Ghost<NetEvent>,
    ) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LSHTIo>>))
        requires
            old(netc).ok(),
            old(self).invariants(&old(netc).my_end_point()),
            !(cpacket.msg is InvalidMessage),
            cpacket.dst@ == old(self).constants.me@,
            // cpacket.dst@ == old(netc).my_end_point(),    // probably provable from the above
            cpacket.abstractable(),
            cpacket.src@.valid_physical_address(),
            old(netc).history() == old_netc_history.push(receive_event),
            receive_event is Receive,
            abstractify_cpacket_to_lsht_packet(cpacket) == abstractify_net_packet_to_lsht_packet(
                receive_event.arrow_Receive_r(),
            ),
        ensures
            ({
                let (ok, Ghost(event_results), Ghost(ios)) = rc;
                &&& self.invariants(&netc.my_end_point())
                &&& self@.constants == old(self)@.constants
                &&& ok
                    == netc.ok()
                // Because all `net_events` are sends, the condition "even if ok is false, if we sent at least one
                // packet..." is implied by "even if ok is false, if `net_events` has length > 0...".
                &&& (ok || event_results.sends.len() > 0) ==> netc.history() == old_netc_history
                    + event_results.ios
                // There's supposed to be a distinction between the ios that we intended to do and the
                // event_seq that we actually did. (See EventResult definition.) But in the interest of
                // mimicking Dafny Ironfleet, we make no such distinction.
                &&& event_results.ios == event_results.event_seq()
                &&& event_results.well_typed_events()
                &&& ok ==> {
                    &&& host_protocol_t::receive_packet_next(old(self)@, self@, ios)
                    &&& raw_io_consistent_with_spec_io(event_results.ios, ios)
                    &&& no_invalid_sends(ios)
                }
            }),
    {
        let (sent_packets, ack) = self.host_model_receive_packet(cpacket);
        let ghost io0 = LIoOp::Receive { r: abstractify_cpacket_to_lsht_packet(cpacket) };
        let ghost ios_head = seq![io0];
        proof {
            let sent_packets_v = abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@);
            let mapped = sent_packets@.map_values(|cp: CPacket| cp@);
            let setted = mapped.to_set();
            if 0 < sent_packets_v.len() {
                // TODO(verus): improve automation for .map and .to_set. Note here we need lots of
                // triggering.
                assert forall|i| #![auto] 0 <= i < sent_packets@.len() implies sent_packets@[i].src@
                    == netc.my_end_point() by {
                    let cpacket = sent_packets@[i];
                    assert(mapped[i] == cpacket@);  // witness
                    assert(setted.contains(cpacket@));  // trigger
                }
            } else {
                assert(0 == mapped.len()) by {
                    if 0 < mapped.len() {
                        assert(setted.contains(mapped[0]));  // witness
                    }
                }
            }
            assert(outbound_packet_seq_has_correct_srcs(sent_packets@, netc.my_end_point()));
        }
        assert(netc.history() == old(netc).history());
        let rc = self.deliver_outbound_packets(netc, &sent_packets);

        let (ok, Ghost(net_events), Ghost(ios_tail)) = rc;
        assert(ok == netc.ok());
        if !ok {
            proof {
                self.delegation_map.valid_implies_complete();  // sorry, valid is opaque now
            }
            let ghost event_results = Self::empty_event_results();
            return (false, Ghost(event_results), Ghost(Seq::<LSHTIo>::empty()));
        }
        let ghost ios = ios_head + ios_tail;
        proof {
            old(self).delegation_map.valid_implies_complete();  // sorry, valid is opaque now
        }
        assert(ios_tail =~= ios.skip(1));
        proof {
            lemma_filter_skip_rejected(ios, |io: LSHTIo| io is Send, 1);
        }
        assert(receive_packet(
            old(self)@,
            self@,
            cpacket@,
            extract_packets_from_abstract_ios(ios),
            ack@@,
        ));  // trigger

        let ghost event_results = EventResults {
            recvs: seq![receive_event],
            clocks: seq![],
            sends: net_events,
            ios: seq![receive_event] + net_events,
        };
        assert(abstractify_raw_log_to_ios(event_results.ios) =~= ios);  // extensional equality

        proof {
            self.delegation_map.valid_implies_complete();  // sorry, valid is opaque now
            assert(netc.history() =~= old_netc_history + event_results.ios);
            assert(event_results.ios == event_results.event_seq());
        }
        (ok, Ghost(event_results), Ghost(ios))
    }

    /// Impl/SHT/HostModel.i HostModelReceivePacket
    ///
    /// In Dafny, ack (rc.1) isn't an Option, it is an InvalidPacket that didn't have any ensures
    /// obligations. That is confusing (surprising) to read, but changing it to an Option would
    /// entail making the corresponding change in the host_protocol so that abstraction stays
    /// parallel. That's too big of a change; we're going to stay true to the original lyrics.
    fn host_model_receive_packet(
        &mut self,
        cpacket: CPacket,
    ) -> (rc: (Vec<CPacket>, Ghost<CPacket>))
        requires
            old(self).valid(),
            old(self).host_state_packet_preconditions(cpacket),
            !(cpacket.msg is InvalidMessage),
            cpacket.dst@ == old(self).constants.me@,
        ensures
            ({
                let (sent_packets, ack) = rc;
                &&& outbound_packet_seq_is_valid(sent_packets@)
                &&& receive_packet(
                    old(self)@,
                    self@,
                    cpacket@,
                    abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                    ack@@,
                )
                // The Dafny Ironfleet "common preconditions" take an explicit cpacket, but we need to talk
                // about
                &&& self.host_state_common_postconditions(*old(self), cpacket, sent_packets@)
            }),
    {
        let mut sent_packets = Vec::new();

        if self.received_packet.is_none() {
            let recv_rr = self.sd.receive_impl(&cpacket);

            if matches!(recv_rr, ReceiveImplResult::AckOrInvalid) {
                let ghost g_ack: CPacket = arbitrary();
                proof {
                    assert(!Set::<Packet>::empty().contains(g_ack@));  // trigger
                    assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@)
                        =~= extract_packets_from_lsht_packets(
                        abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@),
                    ));

                    //                     assert( self.host_state_common_postconditions(*old(self), cpacket, sent_packets@) );
                    //                     assert( receive_packet(old(self)@, self@, cpacket@, abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@), g_ack@) );
                }
                (sent_packets, Ghost(g_ack))
            } else {
                match recv_rr {
                    ReceiveImplResult::FreshPacket { ack } => {
                        sent_packets.push(ack);
                        self.received_packet = Some(cpacket);
                    },
                    ReceiveImplResult::DuplicatePacket { ack } => {
                        sent_packets.push(ack);
                    },
                    _ => { unreached() },
                };
                let ghost g_ack = recv_rr.get_ack();

                proof {
                    lemma_map_values_singleton_auto::<CPacket, Packet>();
                    lemma_to_set_singleton_auto::<Packet>();
                    let abs_seq_lsht = abstractify_outbound_packets_to_seq_of_lsht_packets(
                        sent_packets@,
                    );
                    let ext_seq = abs_seq_lsht.map_values(
                        |lp: LSHTPacket| extract_packet_from_lsht_packet(lp),
                    );
                    assert(ext_seq =~= seq![g_ack@]);  // trigger auto lemmas
                    //                     assert( receive_packet(old(self)@, self@, cpacket@, abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@), g_ack@) );
                }
                (sent_packets, Ghost(g_ack))
            }
        } else {
            let ack = Ghost(cpacket);  // NB cpacket is a garbage value, since rc.0 vec is empty
            proof {
                assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@)
                    =~= extract_packets_from_lsht_packets(
                    abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@),
                ));

                assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@)
                    =~= Set::empty());
                //                 assert( receive_packet(old(self)@, self@, cpacket@, abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@), ack@@) );
            }
            (sent_packets, ack)
        }
    }

    // Implements Impl/SHT/HostModel.i.dfy :: ShouldProcessReceivedMessageImpl
    fn should_process_received_message_impl(&self) -> (b: bool)
        requires
            self.num_delegations
                < self.constants.params.max_delegations,  // part of invariants()

        ensures
            b == should_process_received_message(self@),
    {
        match &self.received_packet {
            Some(v) => {
                match &v.msg {
                    CSingleMessage::Message { seqno: _seqno, dst: _dst, m: cm } => {
                        match cm {
                            CMessage::Delegate { .. } | CMessage::Shard { .. } => {
                                // We can't just compare self.num_delegations <
                                // self.constants.params.max_delegations - 2 because the
                                // latter quantity might underflow. So we do the following,
                                // which is equivalent but can't overflow or underflow because
                                // self.num_delegations < self.constants.params.max_delegations.
                                self.num_delegations + 1 < self.constants.params.max_delegations - 1
                            },
                            _ => true,
                        }
                    },
                    _ => false,
                }
            },
            None => false,
        }
    }

    // Translates Impl/SHT/HostModel.i.dfy :: HostIgnoringUnParseable
    pub closed spec fn host_ignoring_unparseable(
        pre: AbstractHostState,
        post: AbstractHostState,
        packets: Set<Packet>,
    ) -> bool {
        &&& packets.len() == 0
        &&& post == AbstractHostState { received_packet: None, ..pre }
        &&& pre.received_packet is Some
        &&& pre.received_packet.arrow_Some_0().msg is Message
        &&& match pre.received_packet.arrow_Some_0().msg.arrow_Message_m() {
            Message::Delegate { range: range, h: h } => !({
                // no need to check for valid_key_range(range)
                &&& valid_hashtable(h)
                &&& !range.is_empty()
                &&& pre.received_packet.arrow_Some_0().msg.arrow_Message_dst().valid_physical_address()
            }),
            _ => false,
        }
    }

    // Forked from host_state_common_preconditions because Verus can't pass a copy
    // of cpacket around willy-nilly as Dafny Ironfleet does.
    pub closed spec fn host_state_packet_preconditions(&self, cpacket: CPacket) -> bool {
        &&& self.abstractable()
        &&& cpacket.abstractable()
        &&& self.valid()
        &&& cpacket.src@.valid_physical_address()
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

    // Translates Impl/SHT/HostState.i.dfy :: HostState_common_preconditions
    // These are now only "common" to the processing methods, not the receive a fresh packet and
    // record it method.
    pub closed spec fn host_state_common_preconditions(&self) -> bool {
        match self.received_packet {
            Some(cpacket) => self.host_state_packet_preconditions(cpacket),
            None => false,
        }
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextGetRequestPreconditions
    pub closed spec fn next_get_request_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& self.received_packet is Some
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg is Message
                &&& cpacket.msg.arrow_Message_m() is GetRequest
                &&& cpacket.src@.valid_physical_address()
            }
        }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextGetRequestPostconditions
    pub closed spec fn next_get_request_postconditions(
        &self,
        pre: Self,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& pre.next_get_request_preconditions()
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& match pre.received_packet {
            Some(cpacket) => next_get_request(
                pre@,
                self@,
                cpacket@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            ),
            None => false,
        }
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextSetRequestPreconditions
    pub closed spec fn next_set_request_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg is Message
                &&& cpacket.msg.arrow_Message_m() is SetRequest
                &&& cpacket.src@.valid_physical_address()
            }
        }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextSetRequestPostconditions
    pub closed spec fn next_set_request_postconditions(
        &self,
        pre: Self,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& pre.next_set_request_preconditions()
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& match pre.received_packet {
            Some(cpacket) => next_set_request(
                pre@,
                self@,
                cpacket@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            ),
            None => false,
        }
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextDelegatePreconditions
    // This includes the extra condition:
    //    &&& self.num_delegations < self.constants.params.max_delegations - 2
    // since this is always required alongside NextDelegatePreconditions.
    pub closed spec fn next_delegate_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg is Message
                &&& cpacket.msg.arrow_Message_m() is Delegate
                &&& cpacket.src@.valid_physical_address()
            }
        }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
        &&& self.constants.me@.valid_physical_address()
        &&& self.sd.valid()
        &&& self.num_delegations < self.constants.params.max_delegations - 2
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextDelegatePostconditions
    // It includes the extra condition next_delegate(...) since that's an
    // extra postcondition always included with NextDelegatePostconditions.
    pub closed spec fn next_delegate_postconditions(
        &self,
        pre: Self,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& pre.next_delegate_preconditions()
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
        &&& {
            ||| next_delegate(
                pre@,
                self@,
                pre.received_packet.unwrap()@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            )
            ||| Self::host_ignoring_unparseable(
                pre@,
                self@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            )
        }
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextShardPreconditions
    // This includes the extra condition:
    //    &&& self.num_delegations < self.constants.params.max_delegations - 2
    // since this is always required alongside NextShardPreconditions.
    pub closed spec fn next_shard_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg is Message
                &&& cpacket.msg.arrow_Message_m() is Shard
                &&& cpacket.src@.valid_physical_address()
            }
        }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
        &&& self.num_delegations < self.constants.params.max_delegations - 2
    }

    // Translates Impl/SHT/HostState.i.dfy :: NextShardPostconditions
    pub closed spec fn next_shard_postconditions(
        &self,
        pre: Self,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
        &&& match pre.received_packet {
            Some(cpacket) => next_shard_wrapper(
                pre@,
                self@,
                cpacket@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            ),
            None => false,
        }
    }

    // Translates Impl/SHT/HostModel.i.dfy :: HostState_common_postconditions
    pub closed spec fn host_state_common_postconditions(
        &self,
        pre: Self,
        cpacket: CPacket,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        // Removed at Lorch's suggestion: In Dafny, we needed this line to satisfy requires for later
        // terms; in Verus we don't because we're living carelessly wrt recommends.
        // Since we've split off host_state_common_preconditions for the receive_packet case (due to
        // not being able to duplicate exec cpacket), we're trying to avoid propagating that change here.
        //         &&& pre.host_state_common_preconditions()
        &&& self.abstractable()
        &&& self.constants == pre.constants
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.valid()
        &&& self.next_action_index == pre.next_action_index
        &&& outbound_packet_seq_is_valid(sent_packets)
        &&& outbound_packet_seq_has_correct_srcs(sent_packets, pre.constants.me@)
        &&& (forall|i: int|
            0 <= i && i < sent_packets.len() ==> (#[trigger] sent_packets[i].msg) is Message
                || sent_packets[i].msg is Ack)
        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets)
            =~= extract_packets_from_lsht_packets(
            abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets),
        )
        &&& self.resend_count < 100000000
    }

    /// Translates Impl/SHT/HostModel.i.dfy HostModelNextGetRequest
    ///
    /// The cpacket argument is self.received_packet.unwrap() - this is not
    /// translated because it is already mutably borrowed in self and thus
    /// cannot be passed separately.
    fn host_model_next_get_request(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            old(self).next_get_request_preconditions(),
        ensures
            self.next_get_request_postconditions(*old(self), sent_packets@),
    {
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        let ghost pkt: Packet = cpacket@;
        match &cpacket.msg {
            CSingleMessage::Message { m: CMessage::GetRequest { k }, seqno, .. } => {
                let owner: EndPoint = self.delegation_map.get(k);
                let ghost received_request: AppRequest = AppRequest::AppGetRequest {
                    seqno: seqno@ as nat,
                    key: *k,
                };
                let its_me: bool = do_end_points_match(&owner, &self.constants.me);
                let m: CMessage = if its_me {
                    let v = self.h.get(k);
                    // OBSERVE: Need to say `valid_value` to trigger the quantifier saying all values are valid.
                    assert(v.is_some() ==> valid_value(v.arrow_Some_0()@));
                    CMessage::Reply { k: SHTKey { ukey: k.ukey }, v: clone_option_vec_u8(v) }
                } else {
                    CMessage::Redirect { k: SHTKey { ukey: k.ukey }, id: clone_end_point(&owner) }
                };
                let ghost new_received_requests: Seq<AppRequest> = if its_me {
                    self.received_requests@.push(received_request)
                } else {
                    self.received_requests@
                };
                proof {
                    lemma_auto_spec_u64_to_from_le_bytes();
                }
                assert(m.is_marshalable());
                let optional_sm = self.sd.send_single_cmessage(&m, &cpacket.src);
                let mut sent_packets = Vec::<CPacket>::new();
                match optional_sm {
                    Some(sm) => {
                        let p = CPacket {
                            dst: clone_end_point(&cpacket.src),
                            src: clone_end_point(&self.constants.me),
                            msg: sm,
                        };
                        self.received_requests = Ghost(new_received_requests);
                        self.received_packet = None;
                        sent_packets.push(p);
                        // TODO replace a bunch of the proof below with these lines:
                        //                         proof {
                        //                             lemma_map_values_singleton_auto::<CPacket, Packet>();
                        //                             to_set_singleton_auto::<Packet>();
                        //                         }
                        proof {
                            let ap = abstractify_cpacket_to_lsht_packet(p);
                            let bp = Packet { dst: ap.dst, src: ap.src, msg: ap.msg };
                            assert_seqs_equal!(Seq::<CPacket>::empty().push(p).map_values(|cp: CPacket| cp@),
                                               Seq::<Packet>::empty().push(p@));
                            assert(Seq::<Packet>::empty().push(p@).index(0) == p@);  // needed to show it contains p@
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               Seq::<CPacket>::empty().push(p).map_values(|cp: CPacket| cp@).to_set());
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               Set::<Packet>::empty().insert(p@));
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               set![ Packet{dst: pkt.src, src: self.constants.me@, msg: sm@} ]);
                            assert_seqs_equal!(abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@),
                                               Seq::<LSHTPacket>::empty().push(ap));
                            assert_seqs_equal!(abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@)
                                               .map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)),
                                               Seq::<Packet>::empty().push(bp));
                            assert(Seq::<Packet>::empty().push(bp).index(0) == bp);  // needed to show it contains bp
                            assert_sets_equal!(Seq::<Packet>::empty().push(bp).to_set(),
                                               Set::<Packet>::empty().insert(bp));
                            assert(next_get_request_reply(
                                old(self)@,
                                self@,
                                pkt.src,
                                pkt.msg.arrow_Message_seqno(),
                                pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
                                sm@,
                                m@,
                                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                true,
                            ));
                        }
                        return sent_packets;
                    },
                    None => {
                        self.received_packet = None;
                        proof {
                            assert(sent_packets@ =~= Seq::<CPacket>::empty());
                            assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@)
                                =~= Set::<Packet>::empty());
                            assert(next_get_request_reply(
                                old(self)@,
                                self@,
                                pkt.src,
                                pkt.msg.arrow_Message_seqno(),
                                pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
                                SingleMessage::<Message>::InvalidMessage {  },
                                m@,
                                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                false,
                            ));
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               extract_packets_from_lsht_packets(
                                                   abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@)));
                        }
                        return sent_packets;
                    },
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    // Implements Impl/SHT/HostModel.i.dfy HostModelNextSetRequest
    fn host_model_next_set_request(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            old(self).next_set_request_preconditions(),
        ensures
            self.next_set_request_postconditions(*old(self), sent_packets@),
    {
        proof {
            self.delegation_map.valid_implies_complete();
        }
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        let ghost pkt: Packet = cpacket@;
        let ghost pre = *self;
        match &cpacket.msg {
            CSingleMessage::Message { m, seqno, .. } => {
                match m {
                    CMessage::SetRequest { k, v: ov } => {
                        let owner: EndPoint = self.delegation_map.get(k);
                        let marshalable: bool = m.is_message_marshallable();
                        if (!marshalable) {
                            self.received_packet = None;
                            let sent_packets = Vec::<CPacket>::new();
                            let ghost sm = SingleMessage::Ack { ack_seqno: 0 };
                            proof {
                                assert(!valid_key(*k) || !valid_optional_value(
                                    optional_value_view(*ov),
                                ));
                                assert(sent_packets@ == Seq::<CPacket>::empty());
                                assert_seqs_equal!(sent_packets@.map_values(|cp: CPacket| cp@),
                                                   Seq::<Packet>::empty());
                                assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                                   extract_packets_from_lsht_packets(
                                                       abstractify_outbound_packets_to_seq_of_lsht_packets(
                                                           sent_packets@)));
                                assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                                   Set::<Packet>::empty());
                                assert(next_set_request_complete(
                                    old(self)@,
                                    self@,
                                    pkt.src,
                                    pkt.msg.arrow_Message_seqno(),
                                    pkt.msg.arrow_Message_m(),
                                    sm,
                                    Message::Reply { key: *k, value: optional_value_view(*ov) },
                                    Set::<Packet>::empty(),
                                    true,
                                ));
                                assert(next_set_request(
                                    old(self)@,
                                    self@,
                                    cpacket@,
                                    abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                        sent_packets@,
                                    ),
                                ));
                            }
                            ;
                            return sent_packets;
                        } else {
                            assert(valid_key(*k) && valid_optional_value(optional_value_view(*ov)));
                            let its_me: bool = do_end_points_match(&owner, &self.constants.me);
                            let mm: CMessage = if its_me {
                                CMessage::Reply { k: k.clone(), v: clone_optional_value(ov) }
                            } else {
                                CMessage::Redirect { k: k.clone(), id: owner }
                            };
                            assert(mm.is_marshalable()) by {
                                lemma_auto_spec_u64_to_from_le_bytes();
                            }
                            let optional_sm = self.sd.send_single_cmessage(&mm, &cpacket.src);
                            let ghost received_request = AppRequest::AppSetRequest {
                                seqno: seqno@ as nat,
                                key: *k,
                                ov: optional_value_view(*ov),
                            };
                            let mut sent_packets = Vec::<CPacket>::new();
                            let ghost dst = cpacket.src@;
                            match optional_sm {
                                Some(sm) => {
                                    let p = CPacket {
                                        dst: clone_end_point(&cpacket.src),
                                        src: clone_end_point(&self.constants.me),
                                        msg: sm,
                                    };
                                    assert(p@ == Packet {
                                        dst: cpacket.src@,
                                        src: self.constants.me@,
                                        msg: sm@,
                                    });
                                    sent_packets.push(p);
                                    if its_me {
                                        assert(SingleDelivery::send_single_message(
                                            old(self).sd@,
                                            self.sd@,
                                            mm@,
                                            dst,
                                            Some(sm@),
                                            AbstractParameters::static_params(),
                                        ));
                                        self.received_requests = Ghost(
                                            self.received_requests@.push(received_request),
                                        );
                                        match ov {
                                            Some(v) => self.h.insert(k.clone(), clone_vec_u8(v)),
                                            None => self.h.remove(&k),
                                        };
                                        self.received_packet = None;
                                    } else {
                                        self.received_packet = None;
                                    }
                                    proof {
                                        assert(SingleDelivery::send_single_message(
                                            old(self).sd@,
                                            self.sd@,
                                            mm@,
                                            dst,
                                            Some(sm@),
                                            AbstractParameters::static_params(),
                                        ));
                                        assert_seqs_equal!(sent_packets@.map_values(|cp: CPacket| cp@),
                                                           seq![Packet{dst: cpacket.src@, src: self.constants.me@,
                                                                       msg: sm@}]);
                                        singleton_seq_to_set_is_singleton_set(
                                            Packet {
                                                dst: cpacket.src@,
                                                src: self.constants.me@,
                                                msg: sm@,
                                            },
                                        );
                                        assert_sets_equal!(
                                            abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                            set![Packet{dst: pkt.src, src: self.constants.me@, msg: sm@}]);
                                        assert(next_set_request_complete(
                                            old(self)@,
                                            self@,
                                            pkt.src,
                                            pkt.msg.arrow_Message_seqno(),
                                            m@,
                                            sm@,
                                            mm@,
                                            abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                                sent_packets@,
                                            ),
                                            true,
                                        ));
                                        assert(sm.is_marshalable()) by {
                                            lemma_auto_spec_u64_to_from_le_bytes();
                                        }
                                        assert(outbound_packet_is_valid(&p));
                                        assert(outbound_packet_seq_is_valid(sent_packets@));
                                        assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                            sent_packets@,
                                        )
                                            == set![Packet{dst: pkt.src, src: self.constants.me@, msg: sm@}]);
                                        assert(sent_packets@.map_values(
                                            |packet: CPacket|
                                                abstractify_cpacket_to_lsht_packet(packet),
                                        )[0] == LPacket {
                                            dst: pkt.src,
                                            src: self.constants.me@,
                                            msg: sm@,
                                        });
                                        singleton_seq_to_set_is_singleton_set(
                                            LPacket {
                                                dst: pkt.src,
                                                src: self.constants.me@,
                                                msg: sm@,
                                            },
                                        );
                                        assert_seqs_equal!(
                                            sent_packets@.map_values(|packet: CPacket|
                                                              abstractify_cpacket_to_lsht_packet(packet)),
                                            seq![LPacket{dst: pkt.src, src: self.constants.me@, msg: sm@}]);
                                        assert(abstractify_outbound_packets_to_seq_of_lsht_packets(
                                            sent_packets@,
                                        )[0] == abstractify_cpacket_to_lsht_packet(p));
                                        assert_seqs_equal!(
                                            abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@),
                                            seq![abstractify_cpacket_to_lsht_packet(p)]);
                                        assert(extract_packets_from_lsht_packets(
                                            abstractify_outbound_packets_to_seq_of_lsht_packets(
                                                sent_packets@,
                                            ),
                                        ) == extract_packets_from_lsht_packets(
                                            seq![abstractify_cpacket_to_lsht_packet(p)],
                                        ));
                                        assert(seq![
                                            abstractify_cpacket_to_lsht_packet(p),
                                        ].map_values(
                                            |lp: LSHTPacket| extract_packet_from_lsht_packet(lp),
                                        )[0] == Packet {
                                            dst: pkt.src,
                                            src: self.constants.me@,
                                            msg: sm@,
                                        });
                                        assert_seqs_equal!(
                                            seq![abstractify_cpacket_to_lsht_packet(p)].
                                                map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)),
                                            seq![Packet {dst: pkt.src, src: self.constants.me@, msg: sm@}]);
                                        singleton_seq_to_set_is_singleton_set(
                                            Packet {
                                                dst: pkt.src,
                                                src: self.constants.me@,
                                                msg: sm@,
                                            },
                                        );
                                        assert(extract_packets_from_lsht_packets(
                                            seq![abstractify_cpacket_to_lsht_packet(p)],
                                        )
                                            == set![Packet{dst: pkt.src, src: self.constants.me@, msg: sm@}]);
                                        assert(self.host_state_common_postconditions(
                                            pre,
                                            pre.received_packet.unwrap(),
                                            sent_packets@,
                                        ));
                                    }
                                    return sent_packets;
                                },
                                None => {
                                    self.received_packet = None;
                                    proof {
                                        let abs_sent_packets =
                                            abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                            sent_packets@,
                                        );
                                        assert(abs_sent_packets =~= Set::<Packet>::empty());
                                        assert(abstractify_outbound_packets_to_seq_of_lsht_packets(
                                            sent_packets@,
                                        ) =~= Seq::<LSHTPacket>::empty());
                                        assert(extract_packets_from_lsht_packets(
                                            Seq::<LSHTPacket>::empty(),
                                        ) =~= Set::<Packet>::empty());

                                        assert(next_set_request_complete(
                                            old(self)@,
                                            self@,
                                            pkt.src,
                                            pkt.msg.arrow_Message_seqno(),
                                            pkt.msg.arrow_Message_m(),
                                            arbitrary(),
                                            arbitrary(),
                                            abs_sent_packets,
                                            false,
                                        ));  // exists witness
                                    }
                                    return sent_packets;
                                },
                            }
                        }
                    },
                    _ => {
                        assert(false);
                        unreached()
                    },
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    proof fn effect_of_delegation_map_set(
        pre: DelegationMap<CKey>,
        post: DelegationMap<CKey>,
        lo: &KeyIterator<CKey>,
        hi: &KeyIterator<CKey>,
        dst: &EndPoint,
    )
        requires
            pre.valid(),
            post.valid(),
            forall|ki: KeyIterator<CKey>| #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> post@[*ki.get()] == dst@,
            forall|ki: KeyIterator<CKey>|
                !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi))
                    ==> post@[*ki.get()] == pre@[*ki.get()],
        ensures
            AbstractDelegationMap(post@) == AbstractDelegationMap(pre@).update(
                KeyRange::<AbstractKey> { lo: *lo, hi: *hi },
                dst@,
            ),
    {
        pre.valid_implies_complete();
        post.valid_implies_complete();
        assert_maps_equal!(AbstractDelegationMap(post@).0,
                           AbstractDelegationMap(pre@).update(KeyRange::<AbstractKey>{ lo: *lo, hi: *hi }, dst@).0);
    }

    proof fn effect_of_hashmap_bulk_update(
        pre: CKeyHashMap,
        post: CKeyHashMap,
        kr: &KeyRange::<CKey>,
        other: CKeyHashMap,
    )
        requires
            forall|k| pre@.dom().contains(k) ==> #[trigger] valid_value(pre@[k]),
            valid_hashtable(other@),
            post@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey|
                    (pre@.dom().contains(k) || other@.dom().contains(k)) && (kr.contains(k)
                        ==> other@.dom().contains(k)),
                |k: AbstractKey|
                    if other@.dom().contains(k) {
                        other@[k]
                    } else {
                        pre@[k]
                    },
            ),
        ensures
            post@ == bulk_update_hashtable(pre@, *kr, other@),
            forall|k| post@.dom().contains(k) ==> #[trigger] valid_value(post@[k]),
    {
        assert_maps_equal!(post@, bulk_update_hashtable(pre@, *kr, other@));
    }

    // Implements Impl/SHT/HostModel.i.dfy HostModelNextDelegate
    fn host_model_next_delegate(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            old(self).next_delegate_preconditions(),
        ensures
            self.next_delegate_postconditions(*old(self), sent_packets@),
    {
        let sent_packets = vec![];
        proof {
            self.delegation_map.valid_implies_complete();
        }
        ;
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        let ghost pkt: Packet = cpacket@;
        let ghost pre = *self;
        proof {
            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                               Set::<Packet>::empty());
            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                               extract_packets_from_lsht_packets(
                                   abstractify_outbound_packets_to_seq_of_lsht_packets(
                                       sent_packets@)));
        }
        ;
        match &cpacket.msg {
            CSingleMessage::Message { m, seqno, .. } => {
                match m {
                    CMessage::Delegate { range, h } => {
                        let marshalable: bool = m.is_message_marshallable();
                        if (!marshalable) {
                            self.received_packet = None;
                            assert(Self::host_ignoring_unparseable(
                                pre@,
                                self@,
                                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                            ));
                            return sent_packets;
                        } else if !endpoints_contain(&self.constants.host_ids, &cpacket.src) {
                            self.received_packet = None;
                            assert(next_delegate(
                                pre@,
                                self@,
                                pre.received_packet.unwrap()@,
                                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                            ));
                            return sent_packets;
                        } else {
                            self.delegation_map.set(&range.lo, &range.hi, &self.constants.me);
                            assert(valid_hashtable(h@));
                            self.h.bulk_update(&range, &h);
                            self.received_packet = None;
                            self.num_delegations = self.num_delegations + 1;
                            proof {
                                Self::effect_of_delegation_map_set(
                                    pre.delegation_map,
                                    self.delegation_map,
                                    &range.lo,
                                    &range.hi,
                                    &self.constants.me,
                                );
                                Self::effect_of_hashmap_bulk_update(pre.h, self.h, &range, *h);
                            }
                            assert(next_delegate(
                                pre@,
                                self@,
                                pre.received_packet.unwrap()@,
                                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                            ));
                            return sent_packets;
                        }
                    },
                    _ => {
                        assert(false);
                        unreached()
                    },
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        };
        assert(false);
        unreached()
    }

    // Implements Impl/SHT/HostModel.i.dfy HostModelNextShard
    fn host_model_next_shard(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            old(self).next_shard_preconditions(),
        ensures
            self.next_shard_postconditions(*old(self), sent_packets@),
    {
        proof {
            self.delegation_map.valid_implies_complete();
        }
        ;
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        let ghost pkt: Packet = cpacket@;
        let ghost pre = *self;
        match &cpacket.msg {
            CSingleMessage::Message { m, .. } => {
                let mut sent_packets: Vec<CPacket> = vec![];

                // Learn this for early return cases.
                assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@) =~= Set::<
                    Packet,
                >::empty());

                reveal(abstractify_seq_of_cpackets_to_set_of_sht_packets);

                let marshalable: bool = m.is_message_marshallable();

                match m {
                    CMessage::Shard { ref kr, ref recipient } => {
                        if {
                            ||| !marshalable
                            ||| do_end_points_match(&recipient, &self.constants.me)
                            ||| !endpoints_contain(&self.constants.host_ids, &recipient)
                        } {
                            assert(recipient.abstractable());
                            self.received_packet = None;
                            return sent_packets;
                        } else {
                            let this_host_owns_range =
                                self.delegation_map.delegate_for_key_range_is_host_impl(
                                &kr.lo,
                                &kr.hi,
                                &self.constants.me,
                            );

                            if !this_host_owns_range {
                                self.received_packet = None;
                                return sent_packets;
                            }
                            let h = extract_range_impl(&self.h, kr);
                            if h.len() >= 62 {
                                self.received_packet = None;
                                return sent_packets;
                            }
                            // assert( !next_shard_wrapper_must_reject(old(self)@, m@) );
                            // One thing that was surprising (and difficult to understand) in
                            // the Dafny code was that it called ExtractRange twice. This port
                            // eliminates that redundant call.

                            let out_m = CMessage::Delegate { range: kr.clone(), h };
                            assert(out_m.is_marshalable()) by {
                                vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
                                crate::marshal_ironsht_specific_v::lemma_is_marshalable_CKeyHashMap(
                                    h,
                                );
                                reveal(
                                    crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size,
                                );
                            }
                            let optional_sm = self.sd.send_single_cmessage(&out_m, &recipient);
                            match optional_sm {
                                None => {
                                    self.received_packet = None;
                                    self.num_delegations = self.num_delegations + 1;
                                    assert(next_shard(
                                        old(self)@,
                                        self@,
                                        abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                            sent_packets@,
                                        ),
                                        *kr,
                                        recipient@,
                                        arbitrary(),
                                        false,
                                    ));  // exists witness
                                    return sent_packets;
                                },
                                Some(sm) => {
                                    self.delegation_map.set(&kr.lo, &kr.hi, recipient);
                                    proof {
                                        // When porting this, we couldn't figure out why this lemma
                                        // proof consists entirely of a =~=, yet using that same
                                        // twiddle here isn't sufficient.
                                        DelegationMap::lemma_set_is_update(
                                            old(self).delegation_map,
                                            self.delegation_map,
                                            kr.lo,
                                            kr.hi,
                                            recipient,
                                        )
                                    }
                                    ;

                                    self.h.bulk_remove(&kr);

                                    // Borrowing rules (on kr) require us to copy-paste the
                                    // packet. Perhaps there would be a better way to structure
                                    // this code to follow a more borrow-friendly pattern.
                                    let p = CPacket {
                                        dst: clone_end_point(&recipient),
                                        src: clone_end_point(&self.constants.me),
                                        msg: sm,
                                    };
                                    sent_packets.push(p);
                                    self.received_packet = None;
                                    self.num_delegations = self.num_delegations + 1;

                                    proof {
                                        lemma_map_values_singleton_auto::<CPacket, Packet>();
                                        lemma_to_set_singleton_auto::<Packet>();

                                        assert(abstractify_outbound_packets_to_seq_of_lsht_packets(
                                            sent_packets@,
                                        ).map_values(
                                            |lp: LSHTPacket| extract_packet_from_lsht_packet(lp),
                                        ) =~= seq![
                                            extract_packet_from_lsht_packet(
                                                abstractify_cpacket_to_lsht_packet(p),
                                            ),
                                        ]);  // twiddle

                                        assert(next_shard(
                                            old(self)@,
                                            self@,
                                            abstractify_seq_of_cpackets_to_set_of_sht_packets(
                                                sent_packets@,
                                            ),
                                            *kr,
                                            recipient@,
                                            sm@,
                                            true,
                                        ));  // exists witness

                                        assert(p.msg.is_marshalable());
                                    }
                                    return sent_packets;
                                },
                            }
                        }
                    },
                    _ => assert(false),
                }
            },
            _ => assert(false),
        }
        unreached()
    }

    // Implements Impl/SHT/HostModel.i.dfy HostModelNextReceiveMessage
    fn host_model_next_receive_message(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            ({
                let old_self = *old(self);
                match old_self.received_packet {
                    Some(cpacket) => {
                        &&& old(self).sd.valid()
                        &&& old(self).host_state_common_preconditions()
                        &&& match cpacket.msg {
                            CSingleMessage::Message { m: m, .. } => match m {
                                CMessage::GetRequest {
                                    ..
                                } => old_self.next_get_request_preconditions(),
                                CMessage::SetRequest {
                                    ..
                                } => old_self.next_set_request_preconditions(),
                                CMessage::Delegate { .. } => old_self.next_delegate_preconditions(),
                                CMessage::Shard { .. } => old_self.next_shard_preconditions(),
                                _ => true,
                            },
                            _ => false,
                        }
                    },
                    None => false,
                }
            }),
        ensures
            match old(self).received_packet {
                Some(cpacket) => {
                    &&& cpacket_seq_is_abstractable(sent_packets@)
                    &&& self.host_state_common_postconditions(
                        *old(self),
                        (*old(self)).received_packet.unwrap(),
                        sent_packets@,
                    )
                    &&& {
                        ||| process_message(
                            old(self)@,
                            self@,
                            abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                        )
                        ||| Self::host_ignoring_unparseable(
                            old(self)@,
                            self@,
                            abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                        )
                    }
                },
                None => false,
            },
    {
        proof {
            self.delegation_map.valid_implies_complete();
        }
        let cpacket = self.received_packet.as_ref().unwrap();
        match &cpacket.msg {
            CSingleMessage::Message { m, .. } => match m {
                CMessage::GetRequest { .. } => self.host_model_next_get_request(),
                CMessage::SetRequest { .. } => self.host_model_next_set_request(),
                CMessage::Delegate { .. } => self.host_model_next_delegate(),
                CMessage::Shard { .. } => self.host_model_next_shard(),
                CMessage::Reply { .. } | CMessage::Redirect { .. } => {
                    self.received_packet = None;
                    let sent_packets = vec![];
                    proof {
                        assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               Set::<Packet>::empty());
                        assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               extract_packets_from_lsht_packets(
                                                   abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@)));
                    }
                    ;
                    sent_packets
                },
            },
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    // Impl/LiveSHT/SchedulerImpl.i.dfy Host_ProcessReceivedPacket_Next
    fn process_received_packet_next_impl(
        &mut self,
        netc: &mut NetClient,
    ) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            ({
                let (ok, res) = rc;
                &&& ok == netc.ok()
                &&& (*self).invariants(&netc.my_end_point())
                &&& ok ==> {
                    ||| process_received_packet_next(
                        (*old(self))@,
                        (*self)@,
                        abstractify_raw_log_to_ios(res@.ios),
                    )
                    ||| ignore_nonsensical_delegation_packet(
                        (*old(self))@,
                        (*self)@,
                        abstractify_raw_log_to_ios(res@.ios),
                    )
                }
                &&& self.constants == (*old(self)).constants
                &&& ok ==> res@.event_seq() == res@.ios
                &&& ok || (res@.sends.len() > 0) ==> (*netc).history() == (*old(netc)).history()
                    + res@.event_seq()
                &&& res@.well_typed_events()
                &&& no_invalid_sends(abstractify_raw_log_to_ios(res@.ios))
            }),
    {
        let ghost old_self = *self;

        // A lot of the cases below require that we establish that the delegation map was complete at the outset.
        // So we prove this first.

        proof {
            old_self.delegation_map.valid_implies_complete();
        }

        // First, check if we should process this message. If not, do nothing. It's pretty weird that
        // we don't set received_packet to None, but Ironfleet doesn't do it either. I guess the liveness
        // proof relies on the fact that these messages are never actually sent.

        if !self.should_process_received_message_impl() {
            let res = make_empty_event_results();
            proof {
                // The following assert isn't really necessary, but it may help the solver see that
                // we're in the case of process_received_packet_next, not the case of ignore_unparseable_packet.
                assert(process_received_packet_next(
                    old_self@,
                    (*self)@,
                    abstractify_raw_log_to_ios(res@.ios),
                ));
                assert(res@.ios == res@.event_seq());
                assert(true || (res@.sends.len() > 0) ==> (*netc).history() == (*old(
                    netc,
                )).history() + res@.event_seq());
            }
            return (true, res)
        }
        // Second, check if this is something other than a CSingleMessage::Message (e.g., an ack)
        // If so, process it by just setting self.received_packet = None.

        match self.received_packet.as_ref().unwrap().msg {
            CSingleMessage::Message { .. } => {},
            _ => {
                self.received_packet = None;
                let res = make_empty_event_results();
                proof {
                    // The following assert isn't really necessary, but it may help the solver see that
                    // we're in the case of process_received_packet_next, not the case of ignore_unparseable_packet.
                    assert(process_received_packet_next(
                        old_self@,
                        (*self)@,
                        abstractify_raw_log_to_ios(res@.ios),
                    ));
                }
                ;
                return (true, res)
            },
        }
        assert(self.sd.valid());
        assert(self.received_packet is Some);
        assert(self.received_packet.arrow_Some_0().msg is Message);
        assert(self.host_state_common_preconditions());
        let sent_packets = self.host_model_next_receive_message();
        let (ok, net_event_log, ios) = self.deliver_outbound_packets(netc, &sent_packets);
        if !ok {
            return (false, make_empty_event_results());
        } else {
            proof {
                if process_message(
                    old(self)@,
                    self@,
                    abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                ) {
                    assert(process_received_packet_next((*old(self))@, (*self)@, ios@));
                } else {
                    assert(Self::host_ignoring_unparseable(
                        old(self)@,
                        self@,
                        abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                    ));
                    assert_by_contradiction!(sent_packets@.len() == 0, {
                        let p = sent_packets@[0];
                        let s = abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@);
                        //XXX lemma_len0_is_empty(s);
                        assert (sent_packets@.map_values(|cp: CPacket| cp@)[0] == p@);
                        assert (s.contains(p@));
                    });
                    assert(ignore_nonsensical_delegation_packet((*old(self))@, (*self)@, ios@));
                }
            }
            return (true, make_send_only_event_results(net_event_log));
        }
    }

    // Distributed/Impl/LiveSHT/SchedulerImpl.i.dfy Host_NoReceive_NoClock_Next?
    #[verifier(spinoff_prover)]
    pub fn host_noreceive_noclock_next(
        &mut self,
        netc: &mut NetClient,
    ) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
    {
        // HostModel.HostModelSpontaneouslyRetransmit
        // SingleDeliveryModel.RetransmitUnAckedPackets
        let sent_packets = self.sd.retransmit_un_acked_packets(&self.constants.me);

        // SchedulerImpl.DeliverOutboundPackets (seems to be a no-op wrapper?)
        // SchedulerImpl.DeliverPacketSeq
        // NetSHT.SendPacketSeq
        let (ok, Ghost(send_events)) = send_packet_seq(&sent_packets, netc);
        if !ok {
            let ghost event_results = Self::empty_event_results();
            let rc = (false, Ghost(event_results));
            assert(Self::next_ensures(*old(self), *old(netc), *self, *netc, rc));
            // this return path seems unstable
            return rc;
        }
        let event_results = Ghost(
            EventResults { recvs: seq![], clocks: seq![], sends: send_events, ios: send_events },
        );
        proof {
            let aios = abstractify_raw_log_to_ios(event_results@.ios);

            assert forall|i| #![auto] 0 <= i < aios.len() && aios[i] is Send implies !(
            aios[i].arrow_Send_s().msg is InvalidMessage) by {
                assert(send_log_entry_reflects_packet(send_events[i], &sent_packets[i]));  // trigger
            }
            self.delegation_map.valid_implies_complete();  // Needed to get old(self)@.wf()

            // Have to do some =~= to the parts of these definitions before .to_set()
            let view_seq = sent_packets@.map_values(|cp: CPacket| cp@);
            let extract_seq = extract_sent_packets_from_ios(aios).map_values(
                |lp: LSHTPacket| extract_packet_from_lsht_packet(lp),
            );

            // Skip through the filter in extract_sent_packets_from_ios, which is a no-op here
            lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(
                aios,
                |io: LSHTIo| io is Send,
            );

            // Reach into an inconvenient trigger
            assert forall|i| 0 <= i < extract_seq.len() implies extract_seq[i] == view_seq[i] by {
                assert(send_log_entry_reflects_packet(event_results@.ios[i], &sent_packets@[i]));
            }
            assert(view_seq =~= extract_seq);  // prompt ext equality

            assert(next_step(old(self)@, self@, aios, Step::SpontaneouslyRetransmit));  // witness

            assert(ok ==> event_results@.event_seq() == event_results@.ios);
        }
        (ok, event_results)
    }

    pub fn real_next_impl(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
    {
        proof {
            old(self).delegation_map.valid_implies_complete();
        }
        let cur_action_index = self.next_action_index;
        let rc;
        if cur_action_index == 0 {
            rc = self.receive_packet_next(netc);
        } else if cur_action_index == 1 {
            let ghost old_self: HostState = *self;
            let ghost old_netc: NetClient = *netc;
            rc = self.process_received_packet_next_impl(netc);
            proof {
                let (ok, res) = rc;
                {
                    if ok {
                        if process_received_packet_next(
                            old_self@,
                            self@,
                            abstractify_raw_log_to_ios(res@.ios),
                        ) {
                            assert(next_step(
                                old_self@,
                                self@,
                                abstractify_raw_log_to_ios(res@.ios),
                                Step::ProcessReceivedPacket {  },
                            ));  // establish exists |step| next_step...
                        } else {
                            assert(ignore_nonsensical_delegation_packet(
                                old_self@,
                                self@,
                                abstractify_raw_log_to_ios(res@.ios),
                            ));
                            // establish exists |step| next_step...
                            assert(next_step(
                                old_self@,
                                self@,
                                abstractify_raw_log_to_ios(res@.ios),
                                Step::IgnoreNonsensicalDelegationPacket {  },
                            ));
                        }
                        assert(host_protocol_t::next(
                            old_self@,
                            self@,
                            abstractify_raw_log_to_ios(res@.ios),
                        ));
                    }
                }
            }
        } else if cur_action_index == 2 {
            self.resend_count = (self.resend_count + 1) % 100000000;
            if (self.resend_count == 0) {
                rc = self.host_noreceive_noclock_next(netc);
                assert(rc.0 ==> Self::next(old(self)@, self@, rc.1@.ios));
            } else {
                rc = (true, make_empty_event_results());
                assert(next_step(
                    old(self)@,
                    self@,
                    abstractify_raw_log_to_ios(rc.1@.ios),
                    Step::SpontaneouslyRetransmit {  },
                ));  // witness
            }
        } else {
            assert(false);
            rc = unreached()
        }
        if !rc.0 {
            return rc;
        }
        assert(self.invariants(&netc.my_end_point()));
        self.next_action_index = (self.next_action_index + 1) % 3;
        proof {
            let (ok, res) = rc;
            assert(res@.event_seq() == res@.ios);
            assert((ok || res@.sends.len() > 0) ==> netc.history() == old(netc).history()
                + res@.event_seq());
        }
        rc
    }
}

} // verus!
