//!
//!
//! Translation of Impl/SHT/SingleDeliveryModel.i.dfy
use crate::abstract_end_point_t::AbstractEndPoint;
use crate::abstract_parameters_t::AbstractParameters;
use crate::cmessage_v::*;
use crate::endpoint_hashmap_t;
use crate::endpoint_hashmap_t::HashMap;
use crate::host_impl_v::Parameters;
use crate::io_t::EndPoint;
use crate::marshal_v::Marshalable;
use crate::message_t::*;
use crate::net_sht_v::*;
use crate::network_t::*;
use crate::single_message_t::*;
use crate::verus_extra::set_lib_ext_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
// for tha macro

use crate::single_delivery_state_v::*;
use crate::single_delivery_t::*;

verus! {

pub proof fn same_view_same_marshalable(x: &CSingleMessage, y: &CSingleMessage)
    requires
        x@ == y@,
    ensures
        x.is_marshalable() == y.is_marshalable(),
{
    CSingleMessage::view_equal_spec();
    assert(x.view_equal(y));
    x.lemma_same_views_serialize_the_same(y);
}

// We had to do a refactoring from the original material here. The original
// code called NewSingleMessageImpl twice, apparently for proof expediency,
// since the second call used an *old copy* of the SingleDelivery state. That's
// kind of silly, and more importantly hard to represent with references in Rust.
// So we want receive_impl to communicate back to the caller the extra bit of
// info it learned from NewSingleMessageImpl.
pub enum ReceiveImplResult {
    // What does caller need to do?
    FreshPacket { ack: CPacket },  // Buffer the receivedPacket, send an ack
    DuplicatePacket { ack: CPacket },  // Send another ack
    AckOrInvalid,  // No obligation
}

pub open spec fn valid_ack(ack: CPacket, original: CPacket) -> bool {
    &&& ack.abstractable()
    &&& outbound_packet_is_valid(&ack)  // how does this relate to abstractable?
    &&& ack.src@ == original.dst@
    &&& ack.dst@ == original.src@
}

impl ReceiveImplResult {
    pub open spec fn ok(self) -> bool {
        self is FreshPacket || self is DuplicatePacket
    }

    pub open spec fn get_ack(
        self,
    ) -> CPacket
    // we rely on get_ack(AckOrInvalid) returning something about which
    // we don't care so we can pass it to SingleDelivery::receive. Meh.
    //     recommends
    //         self.ok(),
    {
        match self {
            Self::FreshPacket { ack } => ack,
            Self::DuplicatePacket { ack } => ack,
            _ => arbitrary(),
        }
    }

    pub open spec fn get_abstracted_ack_set(self) -> Set<Packet> {
        match self {
            Self::FreshPacket { ack } => set!{ack@},
            Self::DuplicatePacket { ack } => set!{ack@},
            _ => set!{},
        }
    }

    /// True when, if `self` contains an ack, that ack is a valid response to `pkt`.
    pub open spec fn valid_ack(self, pkt: CPacket) -> bool {
        self.ok() ==> valid_ack(self.get_ack(), pkt)
    }
}

/// Impl/SHT/SingleDeliveryModel.RetransmitUnAckedPackets
impl CSingleDelivery {
    pub open spec fn packets_are_valid_messages(packets: Seq<CPacket>) -> bool {
        forall|i| 0 <= i < packets.len() ==> #[trigger] packets[i].msg is Message
    }

    // Does not exist in ironfleet; both this method and its caller are a single glorious
    // executable set-with-mapping comprehension.
    pub fn retransmit_un_acked_packets_for_dst(
        &self,
        src: &EndPoint,
        dst: &EndPoint,
        packets: &mut Vec<CPacket>,
    )
        requires
            self.valid(),
            src.abstractable(),
            outbound_packet_seq_is_valid(old(packets)@),
            outbound_packet_seq_has_correct_srcs(old(packets)@, src@),
            self.send_state@.contains_key(dst@),
            Self::packets_are_valid_messages(old(packets)@),
        ensures
            packets@.map_values(|p: CPacket| p@).to_set() == old(packets)@.map_values(
                |p: CPacket| p@,
            ).to_set() + self@.un_acked_messages_for_dest(src@, dst@),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, src@),
            Self::packets_are_valid_messages(packets@),
    {
        proof {
            assert_sets_equal!(
                packets@.map_values(|p: CPacket| p@).to_set(),
                    old(packets)@.map_values(|p: CPacket| p@).to_set() + self@.un_acked_messages_for_dest_up_to(src@, dst@, 0 as nat),
            );
        }

        match self.send_state.epmap.get(dst) {
            Some(ack_state) => {
                let mut i = 0;

                while i < ack_state.un_acked.len()
                    invariant
                        0 <= i <= ack_state.un_acked.len(),
                        self.valid(),  // Everybody hates having to carry everything through here. :v(
                        src.abstractable(),
                        outbound_packet_seq_is_valid(packets@),
                        outbound_packet_seq_has_correct_srcs(packets@, src@),
                        self.send_state@.contains_key(dst@),
                        ack_state == self.send_state.epmap[dst],
                        packets@.map_values(|p: CPacket| p@).to_set() == old(packets)@.map_values(
                            |p: CPacket| p@,
                        ).to_set() + self@.un_acked_messages_for_dest_up_to(src@, dst@, i as nat),
                        Self::packets_are_valid_messages(packets@),
                {
                    let ghost packets0_view = packets@;

                    assert(CAckState::un_acked_valid(&ack_state.un_acked@[i as int]));  // trigger

                    let sm = &ack_state.un_acked[i];
                    let dst = match sm {
                        CSingleMessage::Message { dst, .. } => dst,
                        _ => {
                            proof {
                                assert(false);
                            }
                            unreached()
                        },
                    };

                    let cpacket = CPacket {
                        dst: dst.clone_up_to_view(),
                        src: src.clone_up_to_view(),
                        msg: sm.clone_up_to_view(),
                    };
                    packets.push(cpacket);

                    i = i + 1;

                    proof {
                        same_view_same_marshalable(&cpacket.msg, &sm);

                        lemma_seq_push_to_set(packets0_view, cpacket);

                        assert_seqs_equal!(packets@.map_values(|p: CPacket| p@),
                                           packets0_view.map_values(|p: CPacket| p@).push(cpacket@));

                        lemma_seq_push_to_set(packets0_view.map_values(|p: CPacket| p@), cpacket@);
                        self.un_acked_messages_extend(src@, dst@, (i - 1) as nat);

                        assert_sets_equal!(
                            packets@.map_values(|p: CPacket| p@).to_set(),
                            old(packets)@.map_values(|p: CPacket| p@).to_set() + self@.un_acked_messages_for_dest_up_to(src@, dst@, i as nat)
                        );
                    }
                }
            },
            None => {
                proof {
                    assert(false);
                }
            },
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: NewSingleMessageImpl
    pub fn new_impl(&self, pkt: &CPacket) -> (ok: bool)
        requires
            self.valid(),
            self.abstractable(),
            pkt.abstractable(),
        ensures
            ok == SingleDelivery::new_single_message(self@, pkt@),
    {
        match pkt.msg {
            CSingleMessage::Message { seqno, .. } => {
                seqno > 0 && seqno - 1 == self.receive_state.lookup(&pkt.src)
            },
            _ => false,
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: ReceiveAckImpl
    pub fn receive_ack_impl(&mut self, pkt: &CPacket)
        requires
            old(self).valid(),
            // self.abstractable(),
            pkt.abstractable(),
            pkt.msg is Ack,
        ensures
            self.valid(),
            SingleDelivery::receive_ack(old(self)@, self@, pkt@, set!{}),
    {
        let num_packets_acked = match self.send_state.get(&pkt.src) {
            Some(ref cack_state) => { cack_state.num_packets_acked },
            None => { 0 },
            // In the None case, we have no ack state. To meet our AckState::receive_ack assum-ed
            // protocol spec, we are forced to not update the send_state; stuffing an
            // CAckState::new in there would make spec unmeetable.
        };

        if let CSingleMessage::Ack { ack_seqno } = pkt.msg {
            if ack_seqno <= num_packets_acked {
                return ;
            }
            let mut local_state = CAckState::new();
            let default = CAckState::new();

            let ghost int_local_state = local_state;  // trigger fodder
            self.send_state.cack_state_swap(&pkt.src, &mut local_state, default);

            local_state.truncate(ack_seqno, Ghost(pkt.src@));
            self.send_state.put(&pkt.src, local_state);

            assert forall|ep: EndPoint| #[trigger] self.send_state@.contains_key(ep@) implies {
                &&& ep.abstractable()
                &&& self.send_state.epmap[&ep].abstractable()
            } by {
                if ep@ != pkt.src@ {
                    assert(old(self).send_state@.contains_key(ep@));
                }
            }
            assert forall|ep: AbstractEndPoint| #[trigger]
                self.send_state@.contains_key(ep) implies self.send_state.epmap@[ep].valid(ep) by {
                if ep != pkt.src@ {
                    assert(old(self).send_state@.contains_key(ep));
                }
            }
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: ReceiveRealPacketImpl
    pub fn receive_real_packet_impl(&mut self, pkt: &CPacket) -> (packet_is_fresh: bool)
        requires
            old(self).valid(),
            pkt.abstractable(),
            pkt.msg is Message,
        ensures
            self.valid(),
            SingleDelivery::receive_real_packet(old(self)@, self@, pkt@),
            packet_is_fresh == SingleDelivery::new_single_message(old(self)@, pkt@),
    {
        // We inlined NewSingleMessageImpl here.
        let last_seqno = self.receive_state.lookup(&pkt.src);
        match pkt.msg {
            CSingleMessage::Message { seqno: pkt_seqno, .. } => {
                let packet_is_fresh = pkt_seqno > 0 && pkt_seqno - 1 == last_seqno;
                if packet_is_fresh {
                    self.receive_state.insert(&pkt.src, last_seqno + 1);
                }
                packet_is_fresh
            },
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: ShouldAckSingleMessageImpl
    pub fn should_ack_sigle_message_impl(&self, pkt: &CPacket) -> bool {
        match pkt.msg {
            CSingleMessage::Message { seqno, .. } => { seqno <= self.receive_state.lookup(&pkt.src)
            },
            _ => false,
        }
    }

    pub open spec fn option_cpacket_to_set_packet(opt_pkt: Option<CPacket>) -> Set<Packet> {
        match opt_pkt {
            Some(pkt) => set!{pkt@},
            None => Set::<Packet>::empty(),
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: MaybeAckPacketImpl
    /// We know coming into this call that pkt satisfies ReceiveRealPacketImpl, so the possible
    /// outcomes are:
    /// Some -> pkt is fresh or duplicate
    /// None -> pkt is from the future; don't ack it!
    pub fn maybe_ack_packet_impl(&self, pkt: &CPacket) -> (opt_ack: Option<CPacket>)
        requires
            self.valid(),
            pkt.abstractable(),
            pkt.msg is Message,
        ensures
            SingleDelivery::maybe_ack_packet(
                self@,
                pkt@,
                opt_ack.unwrap()@,
                Self::option_cpacket_to_set_packet(opt_ack),
            ),
            opt_ack is Some ==> valid_ack(opt_ack.unwrap(), *pkt),
    {
        // jonh inlined ShouldAckSingleMessageImpl and SendAckImpl.
        // I feel like we could inline a LOT of these methods; they're
        // very much consequences of the painful Dafny break-everything-into-
        // two-line-methods lifestyle.
        match pkt.msg {
            CSingleMessage::Message { seqno, .. } => {
                if seqno <= self.receive_state.lookup(&pkt.src) {
                    let m_ack = CSingleMessage::Ack { ack_seqno: seqno };
                    assert(m_ack.is_marshalable()) by {
                        vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
                    }
                    let p_ack = CPacket {
                        dst: pkt.src.clone_up_to_view(),
                        src: pkt.dst.clone_up_to_view(),
                        msg: m_ack,
                    };
                    Some(p_ack)  // Fresh or Duplicate

                } else {
                    None
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        }
        // When ReceiveSingleMessageImpl calls MaybeAckPacketImpl(acct'), the returned b must be true,
        // because acct' came from ReceiveRealPacketImpl.
        //
        // The "weird" case is receiving a duplicate message; here's the call stack:
        // HMRP / ReceiveSingleMessageImpl / ReceiveRealPacketImpl / NewSingleMessageImpl returns false
        // HMRP / ReceiveSingleMessageImpl / MaybeAckPacketImpl(acct') returns true
        // HMRP / NewSingleMessageImpl(acct0) returns false

    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: ReceiveSingleMessageImpl
    pub fn receive_impl(&mut self, pkt: &CPacket) -> (rr: ReceiveImplResult)
        requires
            old(self).valid(),
            old(self).abstractable(),
            pkt.abstractable(),
        ensures
            self.valid(),
            rr.valid_ack(*pkt),
            SingleDelivery::receive(
                old(self)@,
                self@,
                pkt@,
                rr.get_ack()@,
                rr.get_abstracted_ack_set(),
            ),
            rr is FreshPacket ==> SingleDelivery::new_single_message(old(self)@, pkt@),
            rr is DuplicatePacket ==> !SingleDelivery::new_single_message(old(self)@, pkt@),
    {
        match pkt.msg {
            CSingleMessage::Ack { .. } => {
                self.receive_ack_impl(pkt);
                let rr = ReceiveImplResult::AckOrInvalid {  };
                rr
            },
            CSingleMessage::Message { .. } => {
                let packet_is_fresh = self.receive_real_packet_impl(pkt);
                let opt_ack = self.maybe_ack_packet_impl(pkt);

                match opt_ack {
                    Some(ack) => {
                        let rr = if packet_is_fresh {
                            ReceiveImplResult::FreshPacket { ack }
                        } else {
                            ReceiveImplResult::DuplicatePacket { ack }
                        };
                        assert(SingleDelivery::receive(
                            old(self)@,
                            self@,
                            pkt@,
                            rr.get_ack()@,
                            rr.get_abstracted_ack_set(),
                        ));
                        rr
                    },
                    None => {
                        assert(Self::option_cpacket_to_set_packet(opt_ack).is_empty());  // this is an unfortunate trigger to need
                        let rr = ReceiveImplResult::AckOrInvalid {  };
                        rr
                    },
                }
            },
            CSingleMessage::InvalidMessage { .. } => {
                let rr = ReceiveImplResult::AckOrInvalid {  };
                //                 assert( SingleDelivery::receive(old(self)@, self@, pkt@, rr.get_ack()@, rr.get_abstracted_ack_set()) );
                //                 assert( self.valid() );
                rr
            },
        }
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: SendSingleCMessage
    #[verifier::rlimit(15)]
    pub fn send_single_cmessage(
        &mut self,
        m: &CMessage,
        dst: &EndPoint,
    ) -> (sm: Option<CSingleMessage>)
        requires
            old(self).valid(),
            old(self).abstractable(),
            m.abstractable(),
            m.message_marshallable(),
            m.is_marshalable(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            match sm {
                Some(sm) => {
                    &&& sm.abstractable()
                    &&& sm is Message
                    &&& sm.arrow_Message_dst()@ == dst@
                    &&& SingleDelivery::send_single_message(
                        old(self)@,
                        self@,
                        m@,
                        dst@,
                        Some(sm@),
                        AbstractParameters::static_params(),
                    )
                    &&& sm.is_marshalable()
                },
                None => SingleDelivery::send_single_message(
                    old(self)@,
                    self@,
                    m@,
                    dst@,
                    None,
                    AbstractParameters::static_params(),
                ),
            },
    // TODO: capture the part of send_single_message when should_send == false

    {
        let (num_packets_acked, un_acked_len) = match self.send_state.get(dst) {
            Some(ref cack_state) => {
                proof {
                    if cack_state.un_acked.len() > 0 {
                        // This is necessary to show that appending our new seqno keeps the list sequential
                        cack_state.lemma_seqno_in_un_acked_list(
                            dst@,
                            (cack_state.un_acked.len() - 1) as int,
                        );
                    }
                }
                (cack_state.num_packets_acked, cack_state.un_acked.len() as u64)
            },
            None => { (0, 0) },
            // In the None case, we have no ack state. To meet our AckState::receive_ack assum-ed
            // protocol spec, we are forced to not update the send_state; stuffing an
            // CAckState::new in there would make spec unmeetable.
        };

        if Parameters::static_params().max_seqno - num_packets_acked == un_acked_len {
            // No more seqnos; must give up.
            return None;
        }
        assert(num_packets_acked + un_acked_len <= AbstractParameters::static_params().max_seqno);
        let new_seqno = num_packets_acked + un_acked_len + 1;
        let sm_new = CSingleMessage::Message {
            seqno: new_seqno,
            dst: dst.clone_up_to_view(),
            m: m.clone_up_to_view(),
        };
        assert(sm_new.abstractable());
        assert(sm_new.is_marshalable()) by {
            vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
            match sm_new {
                CSingleMessage::Message { seqno, dst: dst_new, m: m_new } => {
                    dst_new.lemma_same_views_serialize_the_same(&dst);
                    m_new.lemma_same_views_serialize_the_same(&m);
                    assert(sm_new.ghost_serialize().len() <= usize::MAX) by {
                        // assert(seqno.ghost_serialize().len() == 8);
                        // assert(dst_new.ghost_serialize().len() == dst.ghost_serialize().len());
                        // assert(m_new.ghost_serialize().len() == m.ghost_serialize().len());
                        // assert(dst_new.ghost_serialize().len() <= 0x100000 + 8);
                        match m_new {
                            CMessage::GetRequest { k } => {
                                // assert(m_new.ghost_serialize().len() <= 0x100000 + 8);
                            },
                            CMessage::SetRequest { k, v } => {
                                // assert(m_new.ghost_serialize().len() <= 0x100000 + 8);
                            },
                            CMessage::Reply { k, v } => {
                                // assert(m_new.ghost_serialize().len() <= 0x100000 + 8);
                            },
                            CMessage::Redirect { k, id } => {
                                // assert(m_new.ghost_serialize().len() <= 0x100000 + 16);
                            },
                            CMessage::Shard { kr, recipient } => {
                                // assert(recipient.ghost_serialize().len() <= 0x100000 + 24);
                                // assert(kr.ghost_serialize().len() <= 0x100000 + 24);
                                // assert(m_new.ghost_serialize().len() <= 0x100000 * 2);
                            },
                            CMessage::Delegate { range, h } => {
                                // assert(range.ghost_serialize().len() <= 30);
                                // assert(h.to_vec().len() <= 100);
                                // assert(h.is_marshalable());
                                // assert(h.ghost_serialize().len() <= crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size());
                                reveal(
                                    crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size,
                                );
                            },
                        };
                    }
                },
                _ => {},
            }
        }
        assert forall|sm_alt: CSingleMessage|
            sm_alt@ == sm_new@ implies sm_alt.is_marshalable() by {
            sm_alt.lemma_same_views_serialize_the_same(&sm_new);
        }
        let mut local_state = CAckState::new();
        let default = CAckState::new();

        let ghost int_local_state = local_state;  // trigger fodder
        self.send_state.cack_state_swap(&dst, &mut local_state, default);
        local_state.un_acked.push(sm_new.clone_up_to_view());

        let ghost old_ack_state = ack_state_lookup(dst@, old(self)@.send_state);
        assert(local_state@.un_acked =~= old_ack_state.un_acked.push(sm_new@));
        self.send_state.put(&dst, local_state);

        assert forall|ep: EndPoint| #[trigger]
            self.send_state@.contains_key(ep@) implies ep.abstractable()
            && self.send_state.epmap[&ep].abstractable() by {
            if ep@ != dst@ {
                assert(old(self).send_state@.contains_key(ep@));
            }
        }
        assert forall|ep: AbstractEndPoint| #[trigger]
            self.send_state@.contains_key(ep) implies self.send_state.epmap@[ep].valid(ep) by {
            if ep != dst@ {
                assert(old(self).send_state@.contains_key(ep));
                assert(self.send_state.epmap@[ep].valid(ep));
            } else {
                assert(self.send_state.epmap@[ep] == local_state);
                assert(self.send_state.epmap@[ep].valid(ep));
            }
        }
        assert(self@.send_state =~= old(self)@.send_state.insert(
            dst@,
            AckState { un_acked: old_ack_state.un_acked.push(sm_new@), ..old_ack_state },
        ));
        Some(sm_new)
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i.dfy :: RetransmitUnAckedPackets
    ///
    /// Does not actually retransmit; returns the packets that should be
    /// retransmitted because they are unacked
    pub fn retransmit_un_acked_packets(&self, src: &EndPoint) -> (packets: Vec<CPacket>)
        requires
            self.valid(),
            src.abstractable(),
        ensures
            abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@) == self@.un_acked_messages(
                src@,
            ),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, src@),
            self@.un_acked_messages(src@) == packets@.map_values(|p: CPacket| p@).to_set(),
            Self::packets_are_valid_messages(packets@),
    {
        let mut packets = Vec::new();

        let dests = self.send_state.epmap.keys();
        let mut dst_i = 0;

        proof {
            assert_seqs_equal!( dests@.subrange(0, dst_i as int) == seq![] );
            assert_sets_equal!(packets@.map_values(|p: CPacket| p@).to_set(), set![]);
            assert_sets_equal!(dests@.subrange(0, dst_i as int).map_values(|ep: EndPoint| ep@).to_set() == set![]);
            self@.lemma_un_acked_messages_for_dests_empty(
                src@,
                dests@.subrange(0, dst_i as int).map_values(|ep: EndPoint| ep@).to_set(),
            );
        }

        while dst_i < dests.len()
            invariant
                self.valid(),  // Everybody hates having to carry everything through here. :v(
                dests@.map_values(|ep: EndPoint| ep@).to_set() == self.send_state.epmap@.dom(),  // NOTE: hard to figure this one out: this comes from postcondition of .keys(). Losing while context extra sad here because it was very painful to reconstruct.
                src.abstractable(),
                0 <= dst_i <= dests.len(),
                outbound_packet_seq_is_valid(packets@),
                outbound_packet_seq_has_correct_srcs(packets@, src@),
                packets@.map_values(|p: CPacket| p@).to_set() == self@.un_acked_messages_for_dests(
                    src@,
                    dests@.subrange(0, dst_i as int).map_values(|ep: EndPoint| ep@).to_set(),
                ),
                Self::packets_are_valid_messages(packets@),
        {
            let ghost packets0_view = packets@;

            let dst = &dests[dst_i];
            assert(dests@.map_values(|ep: EndPoint| ep@)[dst_i as int] == dst@);  // OBSERVE
            // in principle basically need to call `lemma_flatten_sets_insert`,
            // but there's a Set::map in the way that will probably break things

            // The presence of this line seems to hide the trigger loop behavior.
            //            proof {
            //                lemma_seq_push_to_set(dests@.subrange(0, dst_i as int).map_values(|ep: EndPoint| ep@), dst@);
            //            }
            self.retransmit_un_acked_packets_for_dst(src, dst, &mut packets);
            let ghost dst_i0 = dst_i;
            dst_i = dst_i + 1;

            proof {
                let depa = dests@.subrange(0, dst_i0 as int);
                let depb = dests@.subrange(dst_i0 as int, dst_i as int);
                let depc = dests@.subrange(0, dst_i as int);
                assert_seqs_equal!(depc == depa + depb);
                assert_seqs_equal!( depb == seq![*dst] );

                lemma_to_set_singleton_auto::<AbstractEndPoint>();
                lemma_to_set_singleton_auto::<EndPoint>();
                lemma_map_values_singleton_auto::<EndPoint, AbstractEndPoint>();
                lemma_map_set_singleton_auto::<AbstractEndPoint, Set<Packet>>();
                lemma_map_seq_singleton_auto::<AbstractEndPoint, Set<Packet>>();  // was involved in a trigger loop when `set_map_union_auto` also required finite maps
                lemma_flatten_sets_union_auto::<Packet>();
                lemma_to_set_union_auto::<AbstractEndPoint>();  // somehow helps below, so saith Tej
                seq_map_values_concat_auto::<EndPoint, AbstractEndPoint>();
                map_set_finite_auto::<AbstractEndPoint, Set<Packet>>();
                set_map_union_auto::<AbstractEndPoint, Set<Packet>>();
                flatten_sets_singleton_auto::<Packet>();
                //                assert(packets@.map_values(|p: CPacket| p@).to_set() ==
                //                    self@.un_acked_messages_for_dests(src@, dests@.subrange(0, dst_i as int).map_values(|ep: EndPoint| ep@).to_set()));
            }
        }
        proof {
            assert_seqs_equal!(dests@.subrange(0, dests@.len() as int), dests@);
            assert_sets_equal!(self.send_state.epmap@.dom() == self@.send_state.dom());  // OBSERVE
        }

        packets
    }
}

} // verus!
