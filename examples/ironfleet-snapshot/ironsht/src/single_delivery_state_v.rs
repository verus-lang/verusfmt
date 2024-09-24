//! Concrete state for single delivery
//!
//! Mainly defines CSingleState.
//!
//! Translation of Impl/SHT/SingleDeliveryState.i.dfy
use crate::abstract_end_point_t::AbstractEndPoint;
use crate::abstract_parameters_t::AbstractParameters;
use crate::cmessage_v::abstractify_cmessage_seq;
use crate::cmessage_v::CPacket;
use crate::cmessage_v::CSingleMessage;
use crate::endpoint_hashmap_t;
use crate::endpoint_hashmap_t::HashMap;
use crate::io_t::EndPoint;
use crate::marshal_v::Marshalable;
use crate::message_t::*;
use crate::network_t::Packet;
use crate::single_message_t::SingleMessage;
use crate::verus_extra::set_lib_ext_v::flatten_sets_spec;
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

use crate::single_delivery_t::*;

verus! {

/// translates `AckState<MT = CMessage>` (that is, we specialize the message type)
#[verifier::ext_equal]  // effing INSAASAAAAANNE
pub struct CAckState {
    pub num_packets_acked: u64,
    pub un_acked: Vec<CSingleMessage>,
}

impl CAckState {
    pub fn new() -> (e: CAckState)
        ensures
            e.num_packets_acked == 0,
            e.un_acked.len() == 0,
            e@ =~= AckState::new(),
    {
        CAckState {
            num_packets_acked: 0,
            un_acked: vec![],
        }
        //         let e = CAckState{ num_packets_acked: 0, un_acked: vec![] };
        //         assert( e@.num_packets_acked  == AckState::new().num_packets_acked );
        //         assert( e@.un_acked  =~= AckState::new().un_acked );
        //         e

    }

    pub open spec fn view(&self) -> AckState<Message> {
        AckState {
            num_packets_acked: self.num_packets_acked as nat,
            un_acked: abstractify_cmessage_seq(self.un_acked@),
        }
    }

    pub fn clone_up_to_view(&self) -> (o: Self)
        ensures
            o@ == self@,
    {
        let mut un_acked: Vec<CSingleMessage> = Vec::new();
        let mut i = 0;
        while i < self.un_acked.len()
            invariant
                i <= self.un_acked.len(),
                un_acked@.len() == i as nat,
                forall|j: int|
                    0 <= j < i as nat ==> #[trigger] (un_acked@[j]@) == self.un_acked@[j]@,
        {
            un_acked.push(self.un_acked[i].clone_up_to_view());
            i = i + 1;
        }
        proof {
            assert_seqs_equal!(abstractify_cmessage_seq(un_acked@) == abstractify_cmessage_seq(self.un_acked@));
        }
        CAckState { num_packets_acked: self.num_packets_acked, un_acked }
    }

    pub open spec fn abstractable(&self) -> bool {
        forall|i: int| 0 <= i < self.un_acked.len() ==> #[trigger] self.un_acked[i].abstractable()
    }

    pub open spec fn no_acks_in_unacked(list: Seq<CSingleMessage>) -> bool {
        forall|i: int| 0 <= i < list.len() ==> #[trigger] list[i] is Message
    }

    pub open spec fn un_acked_list_sequential(list: Seq<CSingleMessage>) -> bool
        recommends
            Self::no_acks_in_unacked(list),
    {
        forall|i: int, j: int|
            #![auto]
            0 <= i && j == i + 1 && j < list.len() ==> list[i].arrow_Message_seqno() as int + 1
                == list[j].arrow_Message_seqno() as int
    }

    pub open spec fn un_acked_valid(msg: &CSingleMessage) -> bool {
        &&& msg is Message
        &&& msg.abstractable()
        &&& msg.is_marshalable()
    }

    pub open spec fn un_acked_list_valid(list: Seq<CSingleMessage>) -> bool {
        &&& forall|i: int| 0 <= i < list.len() ==> #[trigger] Self::un_acked_valid(&list[i])
        &&& Self::un_acked_list_sequential(list)
    }

    pub open spec fn un_acked_list_valid_for_dst(
        list: Seq<CSingleMessage>,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid(list)
        &&& forall|i: int| 0 <= i < list.len() ==> (#[trigger] list[i].arrow_Message_dst())@ == dst
    }

    pub open spec fn valid_list(
        msgs: Seq<CSingleMessage>,
        num_packets_acked: int,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid_for_dst(msgs, dst)
        &&& num_packets_acked as int + msgs.len() as int
            <= AbstractParameters::static_params().max_seqno
        &&& (msgs.len() > 0 ==> msgs[0].arrow_Message_seqno() == num_packets_acked + 1)
    }

    /// Translates CAckStateIsValid
    pub open spec fn valid(&self, dst: AbstractEndPoint) -> bool {
        &&& self.abstractable()
        &&& Self::valid_list(self.un_acked@, self.num_packets_acked as int, dst)
    }

    pub proof fn lemma_seqno_in_un_acked_list(&self, dst: AbstractEndPoint, k: int)
        requires
            self.valid(dst),
            0 <= k < self.un_acked@.len(),
        ensures
            self.un_acked@[k].arrow_Message_seqno() == self.num_packets_acked + k + 1,
        decreases k,
    {
        if k > 0 {
            self.lemma_seqno_in_un_acked_list(dst, k - 1);
        }
    }

    proof fn abstractify_distributes_over_skip(cm: Seq<CSingleMessage>, i: int)
        requires
            0 <= i <= cm.len(),
        ensures
            abstractify_cmessage_seq(cm.skip(i)) =~= abstractify_cmessage_seq(cm).skip(i),
        decreases i,
    {
        if 0 < i {
            Self::abstractify_distributes_over_skip(cm.subrange(1, cm.len() as int), i - 1);
        }
    }

    pub fn truncate(&mut self, seqno_acked: u64, Ghost(dst): Ghost<AbstractEndPoint>)
        requires
            old(self).valid(dst),
            old(self).num_packets_acked <= seqno_acked,
        ensures
            self.valid(dst),
            abstractify_cmessage_seq(self.un_acked@) == truncate_un_ack_list(
                abstractify_cmessage_seq(old(self).un_acked@),
                seqno_acked as nat,
            ),
            self.un_acked@.len() > 0 ==> self.un_acked[0]@.arrow_Message_seqno() == seqno_acked + 1,
            self.num_packets_acked == seqno_acked,
    {
        let mut i: usize = 0;
        assert(self.un_acked@.skip(0 as int) =~= self.un_acked@);

        while (i < self.un_acked.len() && match self.un_acked[i] {
            CSingleMessage::Message { seqno, .. } => { seqno <= seqno_acked },
            _ => {
                assert(Self::un_acked_valid(&self.un_acked[i as int]));
                assert(false);
                true
            },
        })
            invariant
                self.valid(dst),
                self == old(self),
                i <= self.un_acked.len(),
                i < self.un_acked.len() ==> self.un_acked[i as int].arrow_Message_seqno()
                    <= seqno_acked + 1,
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> self.un_acked[j].arrow_Message_seqno() <= seqno_acked,
                Self::valid_list(self.un_acked@.skip(i as int), self.num_packets_acked + i, dst),
                truncate_un_ack_list(
                    abstractify_cmessage_seq(self.un_acked@.skip(i as int)),
                    seqno_acked as nat,
                ) == truncate_un_ack_list(
                    abstractify_cmessage_seq(old(self).un_acked@),
                    seqno_acked as nat,
                ),
                self.num_packets_acked + i <= seqno_acked,
        {
            assert(self.un_acked@.skip(i as int).skip(1) =~= self.un_acked@.skip((i + 1) as int));
            i = i + 1;

            proof {
                Self::abstractify_distributes_over_skip(self.un_acked@.skip(i - 1 as int), 1);
            }
        }
        self.num_packets_acked = seqno_acked;
        self.un_acked = self.un_acked.split_off(i);  // snip!
    }
}

pub struct CTombstoneTable {
    pub epmap: endpoint_hashmap_t::HashMap<u64>,
}

impl CTombstoneTable {
    pub open spec fn abstractable(&self) -> bool {
        forall|k: AbstractEndPoint| #[trigger] self@.contains_key(k) ==> k.valid_physical_address()
    }

    /// Since I'm a map, I already have a simple view(), hence the special name.
    pub open spec fn view(&self) -> TombstoneTable {
        self.epmap@.map_values(|v: u64| v as nat)
    }

    /// Translates Impl/SHT/SingleDeliveryModel.i CTombstoneTableLookup
    pub fn lookup(&self, src: &EndPoint) -> (last_seqno: u64)
        ensures
            last_seqno as int == tombstone_table_lookup(src@, self@),
    {
        match self.epmap.get(src) {
            Some(v) => *v,
            _ => 0,
        }
    }

    ///
    pub fn insert(&mut self, src: &EndPoint, last_seqno: u64)
        requires
            old(self).abstractable(),
            src@.valid_physical_address(),
        ensures
            self@ =~= old(self)@.insert(src@, last_seqno as nat),
            self.abstractable(),
    {
        self.epmap.insert(src, last_seqno);
        assert(forall|k: AbstractEndPoint| #[trigger]
            self@.contains_key(k) ==> old(self)@.contains_key(k) || k == src@);
    }
}

pub struct CSendState {
    pub epmap: endpoint_hashmap_t::HashMap<CAckState>,
}

impl CSendState {
    /// CSendStateIsAbstractable
    pub open spec fn abstractable(&self) -> bool {
        forall|ep: EndPoint| #[trigger]
            self@.contains_key(ep@) ==> ep.abstractable()
                && self.epmap[&ep].abstractable()
        // NB ignoring the "ReverseKey" stuff from GenericRefinement.MapIsAbstractable

    }

    // AbstractifyCSendStateToSendState is implied by the second type argument to HashMap. A
    // consequence is that you don't get recommends on view.
    /// CSendStateIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& forall|ep: AbstractEndPoint| #[trigger]
            self@.contains_key(ep) ==> self.epmap@[ep].valid(ep)
    }

    pub open spec fn view(&self) -> SendState<Message> {
        self.epmap@.map_values(|v: CAckState| v@)
    }

    //     /// Translates CAckStateLookup
    //     pub fn cack_state_lookup(&self, src: &EndPoint) -> (ack_state: CAckState)
    //         requires
    //             self.valid(),
    //             src.abstractable(),
    //         // TODO: write postcondition
    //     {
    //         match self.epmap.get(src) {
    //             Some(ack_state) => ack_state.clone_up_to_view(),
    //             None => CAckState { num_packets_acked: 0, un_acked: Vec::new(), }
    //         }
    //     }
    pub fn get(&self, src: &EndPoint) -> (value: Option<&CAckState>)
        ensures
            value == match HashMap::get_spec(self.epmap@, src@) {
                Some(v) => Some(&v),
                None => None,
            },
            value is Some ==> self@.contains_key(src@),  // helpfully trigger valid
    {
        self.epmap.get(src)
    }

    /// Translates CAckStateLookup. Swappy semantics because we can't return mutable
    /// refs in Verus yet.
    pub fn cack_state_swap(&mut self, src: &EndPoint, ack_state: &mut CAckState, default: CAckState)
        requires
            old(self).valid(),
            src.abstractable(),
        ensures
            HashMap::swap_spec(
                old(self).epmap@,
                self.epmap@,
                src@,
                *old(ack_state),
                *ack_state,
                default,
            ),
    {
        self.epmap.swap(src, ack_state, default)
    }

    pub fn put(&mut self, src: &EndPoint, value: CAckState)
        ensures
            HashMap::put_spec(old(self).epmap@, self.epmap@, src@, value),
    {
        self.epmap.put(src, value)
    }
}

/// Translates CSingleDeliveryAcct
pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}

impl CSingleDelivery {
    pub fn empty() -> (out: Self)
        ensures
            out@ == SingleDelivery::<Message>::init(),
    {
        let result = CSingleDelivery {
            receive_state: CTombstoneTable { epmap: HashMap::new() },
            send_state: CSendState { epmap: HashMap::new() },
        };
        proof {
            assert_maps_equal!(result.receive_state@, SingleDelivery::<Message>::init().receive_state);
            assert_maps_equal!(result.send_state@, SingleDelivery::<Message>::init().send_state);
        }
        result
    }

    /// Translates CSingleDeliveryAccountIsValid
    pub open spec fn abstractable(&self) -> bool {
        &&& self.receive_state.abstractable()
        &&& self.send_state.abstractable()
    }

    /// Translates AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct
    pub open spec fn view(self) -> SingleDelivery<Message> {
        SingleDelivery { receive_state: self.receive_state@, send_state: self.send_state@ }
    }

    /// Translates CSingleDeliveryAccountIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.send_state.valid()
    }

    /// Extend a un_acked_messages_for_dest_up_to fact from i to i+1.
    ///
    /// Not a translation - helper lemma to prove retransmit_un_acked_packets_for_dst
    pub proof fn un_acked_messages_extend(
        &self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
        i: nat,
    )
        requires
            self@.send_state.contains_key(dst),
            i < self@.send_state[dst].un_acked.len(),
            self.send_state.valid(),
        ensures
            self@.un_acked_messages_for_dest_up_to(src, dst, i + 1)
                == self@.un_acked_messages_for_dest_up_to(src, dst, i).insert(
                Packet { src, dst, msg: self@.send_state[dst].un_acked[i as int] },
            ),
    {
        let packet = Packet { src, dst, msg: self@.send_state[dst].un_acked[i as int] };
        assert(self.send_state.epmap@[dst].valid(dst));
        let un_acked: Seq<CSingleMessage> = self.send_state.epmap@[dst].un_acked@;
        let un_acked_at: Seq<SingleMessage<Message>> = self@.send_state[dst].un_acked;
        assert(CAckState::un_acked_list_valid(un_acked));
        assert(CAckState::un_acked_valid(&un_acked[i as int]));
        // assert(un_acked[i as int]@ == un_acked_at[i as int]);
        assert(un_acked_at[i as int] is Message);
        assert_sets_equal!(
            self@.un_acked_messages_for_dest_up_to(src, dst, i+1) ==
            self@.un_acked_messages_for_dest_up_to(src, dst, i).insert(packet)
        );
    }
}

impl SingleDelivery<Message> {
    pub proof fn lemma_un_acked_messages_for_dests_empty(
        &self,
        src: AbstractEndPoint,
        dests: Set<AbstractEndPoint>,
    )
        requires
            dests == Set::<AbstractEndPoint>::empty(),
        ensures
            self.un_acked_messages_for_dests(src, dests) == Set::<Packet>::empty(),
    {
        assert_sets_equal!(dests.map(|dst: AbstractEndPoint| self.un_acked_messages_for_dest(src, dst)) == set![]);
        assert_sets_equal!(self.un_acked_messages_for_dests(src, dests) == set![]);
    }
}

} // verus!
