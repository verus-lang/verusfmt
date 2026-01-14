#![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::seq::*;

use vstd::{set::*, set_lib::*};

use crate::abstract_end_point_t::*;
use crate::abstract_parameters_t::*;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_message_t::*;
use crate::verus_extra::set_lib_ext_v::{flatten_sets, flatten_sets_spec};

verus! {

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

pub open spec fn tombstone_table_lookup(src: AbstractEndPoint, t: TombstoneTable) -> nat {
    if t.dom().contains(src) {
        t[src]
    } else {
        0
    }
}

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub open spec(checked) fn truncate_un_ack_list<MT>(
    un_acked: AckList<MT>,
    seqno_acked: nat,
) -> Seq<SingleMessage<MT>>
    decreases un_acked.len(),
{
    if un_acked.len() > 0 && un_acked[0] is Message && un_acked[0].arrow_Message_seqno()
        <= seqno_acked {
        truncate_un_ack_list(un_acked.skip(1), seqno_acked)
    } else {
        un_acked
    }
}

#[verifier::ext_equal]
pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

impl AckState<Message> {
    //pub spec fn abstractable
    pub open spec fn new() -> Self {
        AckState { num_packets_acked: 0, un_acked: seq![] }
    }
}

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

pub open spec(checked) fn ack_state_lookup<MT>(
    src: AbstractEndPoint,
    send_state: SendState<MT>,
) -> AckState<MT> {
    if send_state.contains_key(src) {
        send_state[src]
    } else {
        AckState { num_packets_acked: 0, un_acked: Seq::empty() }
    }
}

// NB we renamed SingleDeliveryAcct to SingleDelivery
#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>,
}

impl<MT> SingleDelivery<MT> {
    pub open spec fn init() -> Self {
        SingleDelivery { receive_state: Map::empty(), send_state: Map::empty() }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy NewSingleMessage
    pub open spec(checked) fn new_single_message(self, pkt: Packet) -> bool {
        let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
        &&& pkt.msg is Message
        &&& pkt.msg.arrow_Message_seqno() == last_seqno + 1
    }

    /// Protocol/SHT/SingleDelivery.i.dfy ReceiveAck
    pub open spec(checked) fn receive_ack(
        pre: Self,
        post: Self,
        pkt: Packet,
        acks: Set<Packet>,
    ) -> bool
        recommends
            pkt.msg is Ack,
    {
        &&& acks.is_empty()
        &&& {
            let old_ack_state = ack_state_lookup(pkt.src, pre.send_state);
            if pkt.msg.arrow_Ack_ack_seqno() > old_ack_state.num_packets_acked {
                let new_ack_state = AckState {
                    num_packets_acked: pkt.msg.arrow_Ack_ack_seqno(),
                    un_acked: truncate_un_ack_list(
                        old_ack_state.un_acked,
                        pkt.msg.arrow_Ack_ack_seqno(),
                    ),
                    ..old_ack_state
                };
                post =~= Self { send_state: pre.send_state.insert(pkt.src, new_ack_state), ..post }
            } else {
                post == pre
            }
        }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy ReceiveRealPacket
    pub open spec(checked) fn receive_real_packet(self, post: Self, pkt: Packet) -> bool {
        if self.new_single_message(pkt) {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            // Mark it received
            post == Self {
                receive_state: self.receive_state.insert(pkt.src, (last_seqno + 1) as nat),
                ..self
            }
        } else {
            post == self
        }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy ShouldAckSingleMessage
    pub open spec(checked) fn should_ack_single_message(self, pkt: Packet) -> bool {
        &&& pkt.msg is Message  // Don't want to ack acks
        &&& {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            pkt.msg.arrow_Message_seqno() <= last_seqno
        }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy SendAck
    pub open spec(checked) fn send_ack(self, pkt: Packet, ack: Packet, acks: Set<Packet>) -> bool
        recommends
            self.should_ack_single_message(pkt),
    {
        &&& ack.msg is Ack
        &&& ack.msg.arrow_Ack_ack_seqno() == pkt.msg.arrow_Message_seqno()
        &&& ack.src == pkt.dst
        &&& ack.dst == pkt.src
        &&& acks == set![ ack ]
    }

    /// Protocol/SHT/SingleDelivery.i.dfy MaybeAckPacket
    pub open spec(checked) fn maybe_ack_packet(
        pre: Self,
        pkt: Packet,
        ack: Packet,
        acks: Set<Packet>,
    ) -> bool {
        if pre.should_ack_single_message(pkt) {
            pre.send_ack(pkt, ack, acks)
        } else {
            acks.is_empty()
        }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy ReceiveSingleMessage
    pub open spec(checked) fn receive(
        pre: Self,
        post: Self,
        pkt: Packet,
        ack: Packet,
        acks: Set<Packet>,
    ) -> bool {
        match pkt.msg {
            SingleMessage::Ack { ack_seqno: _ } => Self::receive_ack(pre, post, pkt, acks),
            SingleMessage::Message { seqno, dst: _, m } => {
                &&& Self::receive_real_packet(pre, post, pkt)
                &&& Self::maybe_ack_packet(post, pkt, ack, acks)
            },
            SingleMessage::InvalidMessage {  } => {
                &&& post === pre
                &&& acks === Set::empty()
            },
        }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy SendSingleMessage
    /// NOTE the Verus port modifies this spec to carry the dst
    /// as a separate field, so that we can talk about it even in the
    /// !should_send (sm is None) case. In the original Dafny spec,
    /// sm was always present, and in the !should_send case, only the
    /// dst field was meaningful.
    pub open spec(checked) fn send_single_message(
        pre: Self,
        post: Self,
        m: MT,
        dst: AbstractEndPoint,  /*out*/
        sm: Option<SingleMessage<MT>>,
        params: AbstractParameters,
    ) -> bool {
        let old_ack_state = ack_state_lookup(dst, pre.send_state);
        let new_seqno = old_ack_state.num_packets_acked + old_ack_state.un_acked.len() + 1;
        if new_seqno > params.max_seqno {
            // Packet shouldn't be sent if we exceed the maximum sequence number
            &&& post == pre
            &&& sm is None
        } else {
            &&& sm == Some(SingleMessage::<MT>::Message { seqno: new_seqno, m: m, dst: dst })
            &&& post == SingleDelivery {
                send_state: pre.send_state.insert(
                    dst,
                    AckState {
                        un_acked: old_ack_state.un_acked.push(sm.unwrap()),
                        ..old_ack_state
                    },
                ),
                ..pre
            }
        }
    }

    // Protocol/SHT/SingleDelivery.i.dfy ReceiveNoMessage
    pub open spec(checked) fn receive_no_message(pre: Self, post: Self) -> bool {
        post.receive_state == pre.receive_state
    }

    // Protocol/SHT/SingleDelivery.i.dfy SendNoMessage
    pub open spec(checked) fn send_no_message(pre: Self, post: Self) -> bool {
        post.send_state == pre.send_state
    }
}

impl SingleDelivery<Message> {
    pub open spec(checked) fn un_acked_messages_for_dest_up_to(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
        count: nat,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
            count <= self.send_state[dst].un_acked.len(),
    {
        Set::new(
            |p: Packet|
                {
                    &&& p.src == src
                    &&& exists|i: int|
                        {
                            &&& 0 <= i < count
                            &&& self.send_state[dst].un_acked[i] is Message
                            &&& p.msg == self.send_state[dst].un_acked[i]
                            &&& p.dst == p.msg.arrow_Message_dst()
                        }
                },
        )
    }

    pub open spec(checked) fn un_acked_messages_for_dest(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
    {
        self.un_acked_messages_for_dest_up_to(src, dst, self.send_state[dst].un_acked.len())
    }

    // TODO(tchajed): I now think this should avoid mapping over a Set and
    // instead take dsts: Seq. Currently we convert a list of destinations to be
    // iterated over into a set, map over it, and then take the union; we might
    // as well remember the order and make use of it the whole way through. The
    // only slight cost is that we will need to implement a
    // union-of-seq-of-sets, just like in IronFleet.
    pub open spec fn un_acked_messages_for_dests(
        self,
        src: AbstractEndPoint,
        dsts: Set<AbstractEndPoint>,
    ) -> Set<Packet>
        recommends
            dsts.subset_of(self.send_state.dom()),
    {
        flatten_sets(dsts.map(|dst: AbstractEndPoint| self.un_acked_messages_for_dest(src, dst)))
    }

    /// Re-written Protocol/SHT/SingleDelivery.i.dfy UnAckedMessages
    pub open spec fn un_acked_messages(self, src: AbstractEndPoint) -> Set<Packet> {
        self.un_acked_messages_for_dests(src, self.send_state.dom())
    }
}

} // verus!
