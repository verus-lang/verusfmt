#![allow(unused_imports)]
#![allow(unused_attributes)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

mod abstract_end_point_t{
#![verus::trusted]

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

// This translates ironfleet's NodeIdentity type.
pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl AbstractEndPoint {
    // Translates Common/Native/Io.s.dfy0
    pub open spec fn valid_physical_address(self) -> bool {
        self.id.len() < 0x100000
    }
    
    pub open spec fn abstractable(self) -> bool {
        self.valid_physical_address()
    }
}

} // verus!

}

mod abstract_parameters_t{
#![verus::trusted]

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub struct AbstractParameters {
    pub max_seqno: nat,
    pub max_delegations: nat,
}

impl AbstractParameters {
    // Translates Impl/SHT/Parameters::StaticParams
    pub open spec fn static_params() -> AbstractParameters {
        AbstractParameters {
            max_seqno: 0xffff_ffff_ffff_ffff as nat,
            max_delegations: 0x7FFF_FFFF_FFFF_FFFF as nat,
        }
    }
}

} // verus!

}

mod abstract_service_t{
#![verus::trusted]

use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::seq::*;
use vstd::set::*;

use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;

use crate::app_interface_t::*;
use crate::keys_t::*;
use crate::message_t::*;
use crate::single_message_t::*;

verus! {

#[is_variant]
pub enum AppRequest {
    AppGetRequest { seqno: nat, key: AbstractKey },
    AppSetRequest { seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
}

#[is_variant]
pub enum AppReply {
    AppReply { g_seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
}

} // verus!
// verus

}

mod app_interface_t{
#![verus::trusted]

use crate::keys_t::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::seq::*;
use vstd::set::*;

use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;

verus! {

pub type AbstractValue = Seq<u8>;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

// Translates Services/SHT/AppInterface.i.dfy :: max_val_len
pub open spec fn max_val_len() -> int {
    1024
}

// Translates Services/SHT/AppInterface.i.dfy :: ValidKey
pub open spec fn valid_key(key: AbstractKey) -> bool {
    true
}

// Translates Services/SHT/AppInterface.i.dfy :: ValidValue
pub open spec fn valid_value(value: AbstractValue) -> bool {
    value.len() < max_val_len()
}

// Protocol/SHT/Delegations.i.dfy ExtractRange
pub open spec fn extract_range(h: Hashtable, kr: KeyRange<AbstractKey>) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| h.dom().contains(k) && kr.contains(k),
        |k: AbstractKey| h[k],
    )
}

} // verus!

}

mod args_t{
#![verus::trusted]

use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub type AbstractArg = Seq<u8>;

pub type AbstractArgs = Seq<AbstractArg>;

pub type Arg = Vec<u8>;

pub type Args = Vec<Arg>;

/// Clone a Vec<u8>.
///
/// Implemented as a loop, so might not be as efficient as the
/// `std::vec::Vec::clone` method.
// TODO: implemented to avoid depending on (and waiting for) Vec::clone,
// which is made complicated by how it should treat its generic type
// parameter. Here the elements are u8 which are easy to deal with.
pub fn clone_vec_u8(v: &Vec<u8>) -> (out: Vec<u8>)
    ensures
        out@ == v@,
{
    let mut out: Arg = Vec::with_capacity(v.len());
    let mut i = 0;
    while i < v.len() 
        invariant
            i <= v.len(),
            i == out.len(),
            forall|j| #![auto] 0 <= j < i ==> out@[j] == v@[j],
    {
        out.push(v[i]);
        i = i + 1;
    }
    proof {
        assert_seqs_equal!(out@, v@);
    }
    out
}

pub fn clone_arg(arg: &Arg) -> (out: Arg)
    ensures
        out@ == arg@,
{
    clone_vec_u8(arg)
}

pub open spec fn abstractify_args(args: Args) -> AbstractArgs {
    args@.map(|i, arg: Arg| arg@)
}

} // verus!

}

mod cmessage_v{
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

#[is_variant]
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
    
    // TODO this is awful ... because we don't have a View trait yet.
    pub fn clone_value(value: &Option<Vec<u8>>) -> (out: Option<Vec<u8>>)
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

pub open spec fn abstractify_cmessage_seq(messages: Seq<CSingleMessage>) -> Seq<
    SingleMessage<Message>,
> {
    messages.map_values(|msg: CSingleMessage| msg@)
}

/* $line_count$Proof$ */
define_enum_and_derive_marshalable! {
/* $line_count$Exec$ */ #[is_variant]
/* $line_count$Exec$ */ pub enum CSingleMessage {
/* $line_count$Exec$ */   #[tag = 0]
/* $line_count$Exec$ */   Message{ #[o=o0] seqno: u64, #[o=o1] dst: EndPoint, #[o=o2] m: CMessage },
/* $line_count$Exec$ */   #[tag = 1]
/* $line_count$Exec$ */   // I got everything up to and including `ack_seqno`
/* $line_count$Exec$ */   Ack{ #[o=o0] ack_seqno: u64},
/* $line_count$Exec$ */   #[tag = 2]
/* $line_count$Exec$ */   InvalidMessage,
/* $line_count$Exec$ */ }
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
        assert forall|x: &CSingleMessage, y: &CSingleMessage| 
            #[trigger]
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
    forall|i: int| 
        0 <= i && i < packets.len() ==> #[trigger]
        packets[i].abstractable()
}

// Translates Impl/SHT/PacketParsing.i.dfy :: AbstractifyOutboundPacketsToSeqOfLSHTPackets
pub open spec fn abstractify_outbound_packets_to_seq_of_lsht_packets(packets: Seq<CPacket>) -> Seq<
    LSHTPacket,
>
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

}

mod delegation_map_t{
#![verus::trusted]
//! Translates file Protocol/SHT/Delegations.i.dfy

use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::seq::*;
use vstd::set::*;

use crate::abstract_end_point_t::*;
use crate::app_interface_t::*;
use crate::keys_t::*;
use crate::network_t::*;

verus! {

#[verifier::ext_equal]  // effing INSAASAAAAANNE
pub struct AbstractDelegationMap(pub Map<AbstractKey, AbstractEndPoint>);

impl AbstractDelegationMap {
    pub open spec fn init(root_identity: AbstractEndPoint) -> Self {
        AbstractDelegationMap(Map::total(|k: AbstractKey| root_identity))
    }
    
    #[verifier(inline)]
    pub open spec fn view(self) -> Map<AbstractKey, AbstractEndPoint> {
        self.0
    }
    
    #[verifier(inline)]
    pub open spec fn spec_index(self, key: AbstractKey) -> AbstractEndPoint
        recommends
            self.0.dom().contains(key),
    {
        self@.index(key)
    }
    
    pub open spec fn is_complete(self) -> bool {
        self@.dom().is_full()
    }
    
    /// Translates Protocol/SHT/Delegations.i.dfy :: UpdateDelegationMap
    pub open spec fn update(self, newkr: KeyRange<AbstractKey>, host: AbstractEndPoint) -> Self
        recommends
            self.is_complete(),
    {
        AbstractDelegationMap(self@.union_prefer_right(Map::new(|k| newkr.contains(k), |k| host)))
    }
    
    /// Translates Protocol/SHT/Delegations.i.dfy :: DelegateForKeyRangeIsHost
    pub open spec fn delegate_for_key_range_is_host(
        self,
        kr: KeyRange<AbstractKey>,
        id: AbstractEndPoint,
    ) -> bool
        recommends
            self.is_complete(),
    {
        forall|k: AbstractKey| #[trigger] kr.contains(k) ==> self[k] == id
    }
}

} // verus!

}

mod delegation_map_v{
//! Translates file Distributed/Impl/SHT/Delegations.i.dfy
use builtin_macros::*;

use builtin::*;

use vstd::prelude::*;
use vstd::{map::*, modes::*, seq::*, seq_lib::*, set::*, set_lib::*, *};

use crate::abstract_end_point_t::AbstractEndPoint;
use crate::delegation_map_t::*;
use crate::io_t::EndPoint;
use crate::keys_t::*;
use crate::seq_is_unique_v::*;
use crate::verus_extra::clone_v::*;

verus! {

impl Ordering {
    pub open spec fn eq(self) -> bool {
        matches!(self, Ordering::Equal)
    }
    
    pub open spec fn ne(self) -> bool {
        !matches!(self, Ordering::Equal)
    }
    
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
    
    pub open spec fn gt(self) -> bool {
        matches!(self, Ordering::Greater)
    }
    
    pub open spec fn le(self) -> bool {
        !matches!(self, Ordering::Greater)
    }
    
    pub open spec fn ge(self) -> bool {
        !matches!(self, Ordering::Less)
    }
    
    pub fn is_eq(self) -> (b: bool)
        ensures
            b == self.eq(),
    {
        matches!(self, Ordering::Equal)
    }
    
    pub fn is_ne(self) -> (b: bool)
        ensures
            b == self.ne(),
    {
        !matches!(self, Ordering::Equal)
    }
    
    pub const fn is_lt(self) -> (b: bool)
        ensures
            b == self.lt(),
    {
        matches!(self, Ordering::Less)
    }
    
    pub const fn is_gt(self) -> (b: bool)
        ensures
            b == self.gt(),
    {
        matches!(self, Ordering::Greater)
    }
    
    pub const fn is_le(self) -> (b: bool)
        ensures
            b == self.le(),
    {
        !matches!(self, Ordering::Greater)
    }
    
    pub const fn is_ge(self) -> (b: bool)
        ensures
            b == self.ge(),
    {
        !matches!(self, Ordering::Less)
    }
}

// Stores the entries from smallest to largest
struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

/*
proof fn sorted_subrange<K: KeyTrait>(s: Seq<K>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        sorted(s),
    ensures
        sorted(s.subrange(i, j)),
{
    let sub = s.subrange(i, j);
    assert forall |m, n| 0 <= m < n < sub.len() implies #[trigger](sub[m].cmp_spec(sub[n]).lt()) by {
        K::cmp_properties();
    }
}
*/
impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {
    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }
    
    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }
    
    proof fn to_set(self) -> (s: Set<K>)
        requires
            self.valid(),
        ensures
            s == self@.to_set(),
            s.finite(),
            s.len() == self@.len(),
    {
        seq_to_set_is_finite::<K>(self@);
        self@.unique_seq_to_set();
        self@.to_set()
    }
    
    fn new() -> (v: Self)
        ensures
            v@ == Seq::<K>::empty(),
            v.valid(),
    {
        StrictlyOrderedVec { v: Vec::new() }
    }
    
    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    {
        self.v.len()
    }
    
    // TODO(parno): returning an &K is a bit more Rusty (and faster!)
    fn index(&self, i: usize) -> (k: K)
        requires
            i < self@.len(),
        ensures
            k == self@[i as int],
    {
        (self.v[i]).clone()
    }
    
    fn set(&mut self, i: usize, k: K)
        requires
            old(self).valid(),
            i < old(self)@.len(),
            i > 0 ==> old(self)@[i as int - 1].cmp_spec(k).lt(),
            i < old(self)@.len() - 1 ==> k.cmp_spec(old(self)@[i as int + 1]).lt(),
        ensures
            self.valid(),
            self@ == old(self)@.update(i as int, k),
    {
        self.v.set(i, k);
        assert forall|m, n| 0 <= m < n < self@.len() implies #[trigger]
        (self@[m].cmp_spec(self@[n]).lt()) by {
            K::cmp_properties();
        }
        assert forall|i, j| 0 <= i < self@.len() && 0 <= j < self@.len() && i != j implies self@[i]
            != self@[j] by {
            K::cmp_properties();
        }
    }
    
    fn remove(&mut self, i: usize) -> (k: K)
        requires
            old(self).valid(),
            i < old(self)@.len(),
        ensures
            self.valid(),
            k == old(self)@.index(i as int),
            self@ == old(self)@.remove(i as int),
            self@.to_set() == old(self)@.to_set().remove(k),
    {
        let k = self.v.remove(i);
        proof {
            let old_s = old(self)@.to_set().remove(k);
            let new_s = self@.to_set();
            assert forall|e| old_s.contains(e) implies new_s.contains(e) by {
                assert(old(self)@.to_set().contains(e));
                let n = choose|n: int| 0 <= n < old(self)@.len() && old(self)@[n] == e;
                if n < i {
                    assert(self@[n] == e);  // OBSERVE
                } else {
                    assert(self@[n - 1] == e);  // OBSERVE
                }
            }
            assert_sets_equal!(self@.to_set(), old(self)@.to_set().remove(k));
        }
        k
    }
    
    /// Remove entries in the range [start, end)
    fn erase(&mut self, start: usize, end: usize)
        requires
            old(self).valid(),
            start <= end <= old(self)@.len(),
        ensures
            self.valid(),
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(
                end as int,
                old(self)@.len() as int,
            ),
            // TODO: We might want to strengthen this further to say that the two sets on the RHS
            //       are disjoint
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(
                start as int,
                end as int,
            ).to_set(),
    {
        let mut deleted = 0;
        let ghost mut deleted_set;
        proof {
            deleted_set = Set::empty();
            assert_seqs_equal!(self@,
                               old(self)@.subrange(0, start as int) +
                               old(self)@.subrange(start as int + deleted as int,
                                                   old(self)@.len() as int));
            assert_sets_equal!(deleted_set,
                               old(self)@.subrange(start as int,
                                                   start as int + deleted as int).to_set());
            assert_sets_equal!(old(self)@.to_set(),
                               self@.to_set() + deleted_set);
        }
        while deleted < end - start 
            invariant
                start <= end <= old(self)@.len(),
                self@.len() == old(self)@.len() - deleted,
                0 <= deleted <= end - start,
                old(self).valid(),
                self.valid(),
                self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(
                    start as int + deleted as int,
                    old(self)@.len() as int,
                ),
                deleted_set == old(self)@.subrange(
                    start as int,
                    start as int + deleted as int,
                ).to_set(),
                deleted_set.len() == deleted,
                old(self)@.to_set() == self@.to_set() + deleted_set,
        {
            let ghost mut old_deleted_set;
            let ghost mut old_deleted_seq;
            let ghost mut target;
            proof {
                old_deleted_set = deleted_set;
                old_deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                target = self@[start as int];
                deleted_set = deleted_set.insert(self@[start as int]);
            }
            self.remove(start);
            deleted = deleted + 1;
            proof {
                assert_seqs_equal!(self@,
                                   old(self)@.subrange(0, start as int) +
                                   old(self)@.subrange(start as int + deleted as int,
                                                       old(self)@.len() as int));
                let deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                seq_to_set_is_finite::<K>(deleted_seq);
                deleted_seq.unique_seq_to_set();
                assert forall|e| 
                    #[trigger]
                    deleted_set.contains(e) implies deleted_seq.to_set().contains(e) by {
                    if e == target {
                        assert(deleted_seq[deleted as int - 1] == e);  // OBSERVE
                    } else {
                        assert(old_deleted_set.contains(e));
                        assert(old_deleted_seq.contains(e));
                        let i = choose|i| 0 <= i < old_deleted_seq.len() && old_deleted_seq[i] == e;
                        assert(deleted_seq[i] == e);  // OBSERVE
                    }
                }
                assert forall|e| 
                    #[trigger]
                    deleted_seq.to_set().contains(e) implies deleted_set.contains(e) by {
                    if e == target {
                    } else {
                        let i = choose|i| 0 <= i < deleted_seq.len() && deleted_seq[i] == e;
                        assert(old_deleted_seq[i] == e);  // OBSERVE
                    }
                }
                assert_sets_equal!(deleted_set,
                                   deleted_seq.to_set());
                assert_sets_equal!(old(self)@.to_set(),
                                   self@.to_set() + deleted_set);
            }
        }
    }
    
    fn insert(&mut self, k: K) -> (i: usize)
        requires
            old(self).valid(),
            !old(self)@.contains(k),
        ensures
            self.valid(),
            self@.len() == old(self)@.len() + 1,
            0 <= i < self@.len(),
            self@ == old(self)@.insert(i as int, k),
            self@.to_set() == old(self)@.to_set().insert(k),
    {
        // Find the index where we should insert k
        let mut index: usize = 0;
        while index < self.v.len() && self.v[index].cmp(&k).is_lt() 
            invariant
                0 <= index <= self@.len(),
                forall|i| 
                    0 <= i < index ==> (#[trigger]
                    self@.index(i).cmp_spec(k)).lt(),
        {
            index = index + 1;
        }
        self.v.insert(index, k);
        assert forall|m, n| 0 <= m < n < self@.len() implies #[trigger]
        (self@[m].cmp_spec(self@[n]).lt()) by {
            K::cmp_properties();
        }
        assert(self@.to_set() == old(self)@.to_set().insert(k)) by {
            let new_s = self@.to_set();
            let old_s = old(self)@.to_set().insert(k);
            assert(self@[index as int] == k);  // OBSERVE
            assert forall|e| old_s.contains(e) implies new_s.contains(e) by {
                if e == k {
                } else {
                    let i = choose|i: int| 0 <= i < old(self)@.len() && old(self)@[i] == e;
                    if i < index {
                        assert(self@[i] == e);  // OBSERVE
                    } else {
                        assert(self@[i + 1] == e);  // OBSERVE
                    }
                }
            };
            assert_sets_equal!(new_s, old_s);
        };
        return index;
    }
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    // #[verifier(when_used_as_spec(new_spec))]
    pub fn new(k: K) -> (s: Self)
        ensures
            s.k == Some(k),
    {
        KeyIterator { k: Some(k) }
    }
    
    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }
    
    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures
            s.k.is_None(),
    {
        KeyIterator { k: None }
    }
    
    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }
    
    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures
            b == self.is_end_spec(),
    {
        matches!(self.k, None)
    }
    
    pub open spec fn get_spec(&self) -> &K
        recommends
            self.k.is_some(),
    {
        &self.k.get_Some_0()
    }
    
    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires
            !self.is_end(),
        ensures
            k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }
    
    //    fn cmp(&self, other: &Self) -> (o: Ordering)
    //        ensures o == self.cmp_spec(*other),
    //    {
    //        match (self.k, other.k) {
    //            (None, None) => Ordering::Equal,
    //            (None, Some(_)) => Ordering::Less,
    //            (Some(_), None) => Ordering::Greater,
    //            (Some(i), Some(j)) => { i.cmp(&j) }
    //        }
    //    }
    //
    // #[verifier(when_used_as_spec(lt_spec))]
    pub fn lt(&self, other: &Self) -> (b: bool)
        ensures
            b == self.lt_spec(*other),
    {
        (!self.is_end() && other.is_end()) || (!self.is_end() && !other.is_end()
            && self.k.as_ref().unwrap().cmp(&other.k.as_ref().unwrap()).is_lt())
    }
    
    spec fn leq_spec(self, other: Self) -> bool {
        self.lt_spec(other) || self == other
    }
    
    spec fn geq_K(self, other: K) -> bool {
        !self.lt_spec(KeyIterator::new_spec(other))
    }
    
    // Ivy calls this `done`
    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }
    
    // Is this iterator strictly above the supplied value?
    #[verifier(when_used_as_spec(above_spec))]
    fn above(&self, k: K) -> (b: bool)
        ensures
            b == self.above_spec(k),
    {
        self.is_end() || k.cmp(&self.k.as_ref().unwrap().clone()).is_lt()
    }
    
    // Is k in the range [lhs, rhs)
    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }
}

pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize)
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
            end as int,
            old(v)@.len() as int,
        ),
{
    let mut deleted = 0;
    proof {
        assert_seqs_equal!(v@,
                           old(v)@.subrange(0, start as int) +
                           old(v)@.subrange(start as int + deleted as int,
                                               old(v)@.len() as int));
    }
    while deleted < end - start 
        invariant
            start <= end <= old(v)@.len(),
            v@.len() == old(v)@.len() - deleted,
            0 <= deleted <= end - start,
            v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
                start as int + deleted as int,
                old(v)@.len() as int,
            ),
    {
        v.remove(start);
        deleted = deleted + 1;
        proof {
            assert_seqs_equal!(v@,
                               old(v)@.subrange(0, start as int) +
                               old(v)@.subrange(start as int + deleted as int,
                                                   old(v)@.len() as int));
        }
    }
}

// TODO: Restore this to be generic over values V
struct StrictlyOrderedMap<
    #[verifier(maybe_negative)]
    K: KeyTrait + VerusClone,
> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedMap<K> {
    pub closed spec fn view(self) -> Map<K, ID> {
        self.m@
    }
    
    pub closed spec fn map_valid(
        self,
    ) -> bool// recommends self.keys@.len() == self.vals.len()  // error: public function requires cannot refer to private items
     {
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall|i| 
            0 <= i < self.keys@.len() ==> #[trigger]
            (self.m@[self.keys@.index(i)]) == self.vals@.index(i)
    }
    
    pub closed spec fn valid(self) -> bool {
        &&& self.keys.valid()
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }
    
    /// We hold no keys in the range (lo, hi)
    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall|ki| 
            lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger]
            self@.contains_key(*ki.get()))
    }
    
    proof fn mind_the_gap(self)
        ensures
            forall|w, x, y, z| 
                self.gap(w, x) && self.gap(y, z) && #[trigger]
                y.lt_spec(x) ==> #[trigger]
                self.gap(w, z),
            forall|w, x, y: KeyIterator<K>, z| 
                #[trigger]
                self.gap(w, x) && y.geq_spec(w) && x.geq_spec(z) ==> #[trigger]
                self.gap(y, z),
            forall|l: KeyIterator<K>, k, m| 
                #[trigger]
                self.gap(k, m) ==> !(k.lt_spec(l) && l.lt_spec(m) && #[trigger]
                self@.contains_key(*l.get())),
    {
        K::cmp_properties();
    }
    
    proof fn gap_means_empty(self, lo: KeyIterator<K>, hi: KeyIterator<K>, k: KeyIterator<K>)
        requires
            self.gap(lo, hi),
            lo.lt_spec(k) && k.lt_spec(hi),
            self@.contains_key(*k.get()),
        ensures
            false,
    {
        self.mind_the_gap();
    }
    
    proof fn choose_gap_violator(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> (r: KeyIterator<
        K,
    >)
        requires
            !self.gap(lo, hi),
        ensures
            lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get()),
    {
        choose|r| #![auto] lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get_spec())
    }
    
    fn new() -> (s: Self)
        ensures
            s.valid(),
            s@ == Map::<K, ID>::empty(),
    {
        let keys = StrictlyOrderedVec::new();
        let m = Ghost(Map::empty());
        proof {
            assert_sets_equal!(m@.dom(), keys@.to_set());
        }
        StrictlyOrderedMap { keys, vals: Vec::new(), m }
    }
    
    fn find_key(&self, k: &K) -> (o: Option<usize>)
        requires
            self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(i) => 0 <= i < self.keys@.len() && self.keys@[i as int] == k,
            },
    {
        let mut i = 0;
        while i < self.keys.len() 
            invariant
                forall|j| 0 <= j < i ==> self.keys@[j] != k,
        {
            //println!("Loop {} of find_key", i);
            if self.keys.index(i).cmp(&k).is_eq() {
                proof {
                    K::cmp_properties();
                }
                return Some(i);
            } else {
                proof {
                    K::cmp_properties();
                }
            }
            i = i + 1;
        }
        return None;
    }
    
    // All values in the index range [lo, hi] are `v`
    // Second return value says that all values in the index range [lo, hi) are `v`,
    // but the value at hi is not `v`
    fn values_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret: (bool, bool))
        requires
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures
            ret.0 == forall|i| #![auto] lo <= i <= hi ==> self.vals@[i]@ == v@,
            !ret.0 ==> (ret.1 == (self.vals@[hi as int]@ != v@ && forall|i| 
                #![auto]
                lo <= i < hi ==> self.vals@[i]@ == v@)),
    {
        let mut i = lo;
        while i <= hi 
            invariant
                lo <= i,
                hi < self.keys@.len() as usize == self.vals@.len(),
                forall|j| #![auto] lo <= j < i ==> self.vals@[j]@ == v@,
        {
            let eq = do_end_points_match(&self.vals[i], v);
            if !eq  {
                if i == hi {
                    return (false, true);
                } else {
                    return (false, false);
                }
            } else {
                proof {
                    //K::cmp_properties();
                }
            }
            i = i + 1;
        }
        (true, true)
    }
    
    // All keys in the range [keys[lo .. hi]] are `v`
    // Second return value says that all keys in the index range [keys[lo, hi)] are `v`,
    // but the value at hi is not `v`
    fn keys_in_index_range_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret: (bool, bool))
        requires
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures
            ret.0 == forall|i| #![auto] lo <= i <= hi ==> self@[self.keys@[i]]@ == v@,
            !ret.0 ==> (ret.1 == (self@[self.keys@[hi as int]]@ != v@ && (forall|i| 
                #![auto]
                lo <= i < hi ==> self@[self.keys@[i]]@ == v@))),
    {
        let (agree, almost) = self.values_agree(lo, hi, v);
        proof {
            if agree {
            } else {
                assert(!forall|i| #![auto] lo <= i <= hi ==> self.vals@[i]@ == v@);
                let i = choose|i| #![auto] !(lo <= i <= hi ==> self.vals@.index(i)@ == v@);
                assert(self.vals@.index(i)@ != v@);
                assert(self@[self.keys@[i]]@ == self.vals@.index(i)@);
                if almost {
                } else {
                    assert(!(self.vals@[hi as int]@ != v@ && forall|i| 
                        #![auto]
                        lo <= i < hi ==> self.vals@[i]@ == v@));
                    if self.vals@[hi as int]@ == v@ {
                    } else {
                        let j = choose|j| #![auto] lo <= j < hi && self.vals@[j]@ != v@;
                        assert(self@[self.keys@[j]]@ != v@);
                    }
                }
            }
        }
        (agree, almost)
    }
    
    //    // All keys present in the range [lo .. hi] map `v`
    //    fn keys_agree(&self, ghost(lo): Ghost<&K>, lo_index: usize, ghost(hi): Ghost<&K>, hi_index: usize, v: &ID) -> (b: bool)
    //        requires
    //            self.valid(),
    //            0 <= lo_index <= hi_index < self.keys@.len(),
    //            lo == self.keys@[lo_index as int],
    //            hi == self.keys@[hi_index as int],
    //        ensures b == forall |k| #![auto]
    //                        lo.cmp_spec(k).le()
    //                     && k.cmp_spec(*hi).le()
    //                     && self@.contains_key(k)
    //                     ==> self@[k]@ == v@,
    //    {
    //        let ret = self.keys_in_index_range_agree(lo_index, hi_index, v);
    //        proof {
    //            if ret {
    //                assert forall |k| #![auto]
    //                        lo.cmp_spec(k).le()
    //                     && k.cmp_spec(*hi).le()
    //                     && self@.contains_key(k)
    //                     implies self@[k]@ == v@ by {
    //                    assert(exists |i| 0 <= i < self.keys@.len() && self.keys@[i] == k);
    //                    let i = choose |i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
    //                    assert(lo_index <= i <= hi_index) by {
    //                        K::cmp_properties();
    //                    }
    //                }
    //            } else {
    //                let i = choose |i| #![auto] !(lo_index <= i <= hi_index ==> self@[self.keys@[i]]@ == v@);
    //                let k = self.keys@[i];
    //                assert(lo.cmp_spec(k).le() && k.cmp_spec(*hi).le()) by {
    //                    K::cmp_properties();
    //                }
    //                assert(self@.contains_key(k));
    //                assert(self@[k]@ != v@);
    //            }
    //        }
    //        ret
    //    }
    fn get<'a>(&'a self, k: &K) -> (o: Option<&'a ID>)
        requires
            self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(v) => self@[*k] == v,
            },
    {
        match self.find_key(k) {
            None => None,
            Some(i) => Some(&self.vals[i]),
        }
    }
    
    fn set(&mut self, k: K, v: ID)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@.insert(k, v),
            forall|lo, hi| 
                self.gap(lo, hi) <==> old(self).gap(lo, hi) && !(lo.lt_spec(
                    KeyIterator::new_spec(k),
                ) && KeyIterator::new_spec(k).lt_spec(hi)),
    {
        match self.find_key(&k) {
            Some(i) => {
                self.vals.set(i, v);
                self.m = Ghost(self.m@.insert(k, v));
                proof {
                    assert_sets_equal!(self.m@.dom() == self.keys@.to_set());
                }
            },
            None => {
                let index = self.keys.insert(k.clone());
                self.vals.insert(index, v);
                self.m = Ghost(self.m@.insert(k, v));
            },
        }
        assert forall|lo, hi| 
            self.gap(lo, hi) <==> old(self).gap(lo, hi) && !(lo.lt_spec(KeyIterator::new_spec(k))
                && KeyIterator::new_spec(k).lt_spec(hi)) by {
            self.mind_the_gap();
            old(self).mind_the_gap();
            if old(self).gap(lo, hi) && !(lo.lt_spec(KeyIterator::new_spec(k))
                && KeyIterator::new_spec(k).lt_spec(hi)) {
                assert forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger]
                self@.contains_key(*ki.get())) by {
                    // TODO: This was the previous (flaky) proof:
                    // K::cmp_properties();
                    //
                    assert_by_contradiction!(!old(self)@.contains_key(*ki.get()), {
                        old(self).gap_means_empty(lo, hi, ki);
                    });
                };
                assert(self.gap(lo, hi));
            }
            if self.gap(lo, hi) {
                assert forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger]
                old(self)@.contains_key(*ki.get())) by {
                    assert_by_contradiction!(!(old(self)@.contains_key(*ki.get())), {
                        assert(self@.contains_key(*ki.get()));
                        K::cmp_properties();
                    });
                };
                assert(old(self).gap(lo, hi));
                assert_by_contradiction!(!(lo.lt_spec(KeyIterator::new_spec(k)) && KeyIterator::new_spec(k).lt_spec(hi)), {
                    assert(self@.contains_key(k));
                    self.gap_means_empty(lo, hi, KeyIterator::new_spec(k));
                });
            }
        };
    }
    
    spec fn greatest_lower_bound_spec(self, iter: KeyIterator<K>, glb: KeyIterator<K>) -> bool {
        (glb == iter || glb.lt_spec(iter)) && (forall|k| 
            KeyIterator::new_spec(k) != glb && #[trigger]
            self@.contains_key(k) && iter.above(k) ==> glb.above(k)) && (!iter.is_end_spec()
            ==> glb.k.is_Some() && self@.contains_key(glb.k.get_Some_0())
            && // There are no keys in the interval (glb, hi), and iter falls into that gap
        (exists|hi| 
            #[trigger]
            self.gap(glb, hi) && #[trigger]
            KeyIterator::between(glb, iter, hi)))
    }
    
    // Finds the index of the largest iterator <= iter
    fn greatest_lower_bound_index(&self, iter: &KeyIterator<K>) -> (index: usize)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            0 <= index < self.keys@.len(),
            self.greatest_lower_bound_spec(*iter, KeyIterator::new_spec(self.keys@[index as int])),
    {
        let mut bound = 0;
        let mut i = 1;
        // Prove the initial starting condition
        assert forall|j: nat| j < i implies iter.geq_K(
            #[trigger]
            self.keys@.index(j as int),
        ) by {
            let z = K::zero_spec();
            assert(self.keys@.contains(z));
            let n = choose|n: int| 0 <= n < self.keys@.len() && self.keys@[n] == z;
            K::zero_properties();
            assert_by_contradiction!(n == 0, {
                assert(self.keys@[0].cmp_spec(self.keys@[n]).lt());
                K::cmp_properties();
            });
            assert(self.keys@[0] == z);
            K::cmp_properties();
        }// Find the glb's index (bound)
        
        while i < self.keys.len() 
            invariant
                1 <= i <= self.keys@.len(),
                bound == i - 1,
                forall|j: nat| 
                    j < i ==> iter.geq_K(
                        #[trigger]
                        self.keys@.index(j as int),
                    ),
            ensures
                bound == i - 1,
                (i == self.keys@.len() && forall|j: nat| 
                    j < i ==> iter.geq_K(
                        #[trigger]
                        self.keys@.index(j as int),
                    )) || (i < self.keys@.len() && !iter.geq_K(self.keys@.index(i as int))
                    && forall|j: nat| 
                    j < i ==> iter.geq_K(
                        #[trigger]
                        self.keys@.index(j as int),
                    )),
        {
            if iter.lt(&KeyIterator::new(self.keys.index(i))) {
                // Reached a key that's too large
                break ;
            }
            bound = i;
            i = i + 1;
        }
        let glb = KeyIterator::new(self.keys.index(bound));
        assert forall|k| 
            KeyIterator::new_spec(k) != glb && #[trigger]
            self@.contains_key(k) && iter.above(k) implies glb.above(k) by {
            K::cmp_properties();
        }
        proof {
            if !iter.is_end_spec()  {
                if i == self.keys@.len() {
                    let hi = KeyIterator::end();
                    // Prove self.gap(glb, hi)
                    assert forall|ki| glb.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger]
                    self@.contains_key(*ki.get())) by {
                        K::cmp_properties();
                    }
                    assert(self.gap(glb, hi));
                    assert(KeyIterator::between(glb, *iter, hi)) by {
                        K::cmp_properties();
                    }
                } else {
                    let hi = KeyIterator::new_spec(self.keys@[i as int]);
                    // Prove self.gap(glb, hi)
                    assert forall|ki| glb.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger]
                    self@.contains_key(*ki.get())) by {
                        K::cmp_properties();
                    }
                    assert(self.gap(glb, hi));
                    assert(KeyIterator::between(glb, *iter, hi)) by {
                        assert(iter.lt_spec(hi));
                        K::cmp_properties();
                    }
                }
            }
        }
        assert(glb == iter || glb.lt_spec(*iter)) by {
            K::cmp_properties();
        }
        return bound;
    }
    
    // Finds the largest iterator <= iter
    fn greatest_lower_bound(&self, iter: &KeyIterator<K>) -> (glb: KeyIterator<K>)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            self.greatest_lower_bound_spec(*iter, glb),
    {
        let index = self.greatest_lower_bound_index(iter);
        let glb = KeyIterator::new(self.keys.index(index));
        glb
    }
    
    // Remove all keys in the range [lo, hi)
    fn erase(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            forall|k| 
                {
                    let ki = KeyIterator::new_spec(k);
                    (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                        !(#[trigger]
                        self@.contains_key(k))
                    } else {
                        (old(self)@.contains_key(k) ==> self@.contains_key(k) && self@[k] == old(
                            self,
                        )@[k]) && (self@.contains_key(k) ==> old(self)@.contains_key(k))
                    })
                },
            forall|x, y| 
                self.gap(x, y) <==> ({
                    ||| old(self).gap(x, y)
                    ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                        || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                }),
    {
        // Find the point where keys are >= lo
        let mut start = 0;
        while start < self.keys.len() && lo.above(self.keys.index(start)) 
            invariant
                self.valid(),
                0 <= start <= self.keys@.len(),
                forall|j| #![auto] 0 <= j < start ==> lo.above(self.keys@.index(j)),
        {
            start = start + 1;
        }// Find the first point where keys are >= hi
        
        let mut end = start;
        while end < self.keys.len() && hi.above(self.keys.index(end)) 
            invariant
                self.valid(),
                start <= end <= self.keys@.len(),
                forall|j| #![auto] start <= j < end ==> hi.above(self.keys@[j]),
        {
            end = end + 1;
        }//assert(forall |i| #![auto] 0 <= i < start ==> lo.above(self.keys@.index(i)));
        
        assert forall|i| start <= i < end implies !lo.above(
            #[trigger]
            self.keys@[i],
        ) && hi.above(self.keys@[i]) by {
            K::cmp_properties();
        }
        self.keys.erase(start, end);
        vec_erase(&mut self.vals, start, end);
        self.m = Ghost(
            Map::new(
                |k| self.keys@.to_set().contains(k),
                |k| 
                    {
                        let i = choose|i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
                        self.vals@[i]
                    },
            ),
        );
        proof {
            let ks = self.keys.to_set();
            assert(self.keys@.to_set() == ks);
            assert_sets_equal!(self.m@.dom(), ks);
        }
        assert forall|k| 
            {
                let ki = KeyIterator::new_spec(k);
                (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                    !(#[trigger]
                    self@.contains_key(k))
                } else {
                    old(self)@.contains_key(k) ==> self@.contains_key(k) && self@[k] == old(
                        self,
                    )@[k]
                })
            } by {
            let ki = KeyIterator::new_spec(k);
            if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                assert_by_contradiction!(!self@.contains_key(k), {
                    K::cmp_properties();
                });
            }
        }
        assert forall|x, y| self.gap(x, y) implies ({
            ||| old(self).gap(x, y)
            ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                || hi.is_end_spec() || !self@.contains_key(*hi.get())))
        }) by {
            assert_by_contradiction!(
                             old(self).gap(x, y)
                         || (old(self).gap(x, *lo) &&
                             old(self).gap(*hi, y) &&
                             (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get()))), {
                //assert(exists |ki| x.lt_spec(ki) && ki.lt_spec(y) && old(self)@.contains_key(*ki.get()));
                let ki = old(self).choose_gap_violator(x, y);
                if !old(self).gap(x, *lo) {
                    let kk = old(self).choose_gap_violator(x, *lo);
                    assert(self@.contains_key(*kk.get())); // contradicts self.gap(x, y)
                    K::cmp_properties();
                } else if !old(self).gap(*hi, y) {
                    let kk = old(self).choose_gap_violator(*hi, y);
                    assert(self@.contains_key(*kk.get())) by {   // contradicts self.gap(x, y)
                        K::cmp_properties();
                    };
                    K::cmp_properties();
                } else {
                    assert(!(hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())));
                    assert(hi.lt_spec(y));
                    if x.lt_spec(*hi) {
                        self.gap_means_empty(x, y, *hi);
                    } else if x == hi {
                        self.gap_means_empty(*hi, ki, y);
                    } else {
                        assert(hi.lt_spec(x)) by { K::cmp_properties(); };
                        assert(self@.contains_key(*ki.get())) by { K::cmp_properties(); };
                    }
                }
                assert(self@.contains_key(*ki.get()));
            });
        }
        assert forall|x, y| 
            ({
                ||| old(self).gap(x, y)
                ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                    || hi.is_end_spec() || !self@.contains_key(*hi.get())))
            }) implies #[trigger]
        self.gap(x, y) by {
            if old(self).gap(x, y) {
                assert_by_contradiction!(self.gap(x, y), {
                    //let ki = self.choose_gap_violator(x, y);      // Flaky proof -- sometimes needs this line
                });
            }
            if old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y) || hi.is_end_spec()
                || !self@.contains_key(*hi.get())) {
                assert forall|ki| x.lt_spec(ki) && ki.lt_spec(y) implies !(#[trigger]
                self@.contains_key(*ki.get())) by {
                    assert(KeyIterator::between(x, ki, y)) by {
                        K::cmp_properties();
                    };
                    K::cmp_properties();  // Flaky
                    if ki.lt_spec(*lo) {
                        // flaky without assert_by_contradiction (and maybe still flaky)
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if hi.lt_spec(ki) {
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if ki == lo {
                        assert(!(self@.contains_key(*ki.get())));
                    } else if ki == hi {
                        assert(!(self@.contains_key(*ki.get())));
                    } else {
                        assert(KeyIterator::between(*lo, ki, *hi));
                    }//old(self).mind_the_gap();
                    
                };
            }
        }
    }
}

type ID = EndPoint;

// this code was trying to be too generic, but we need to know how to clone IDs. So we specialize.
pub struct DelegationMap<
    #[verifier(maybe_negative)]
    K: KeyTrait + VerusClone,
> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    pub closed spec fn view(self) -> Map<K, AbstractEndPoint> {
        self.m@
    }
    
    pub closed spec fn valid(self) -> bool {
        &&& self.lows.valid()
        &&& self.lows@.contains_key(K::zero_spec())
        &&& self@.dom().is_full()
        &&& (forall|k| #[trigger] self@[k].valid_physical_address())
        &&& (forall|k, i, j| 
            self.lows@.contains_key(i) && self.lows.gap(KeyIterator::new_spec(i), j) && #[trigger]
            KeyIterator::between(KeyIterator::new_spec(i), KeyIterator::new_spec(k), j) ==> self@[k]
                == self.lows@[i]@)
    }
    
    pub fn new(k_zero: K, id_zero: ID) -> (s: Self)
        requires
            k_zero == K::zero_spec(),
            id_zero@.valid_physical_address(),
        ensures
            s.valid(),
            s@ == Map::total(|k: K| id_zero@),
    {
        let mut lows = StrictlyOrderedMap::new();
        lows.set(k_zero, id_zero);
        let m = Ghost(Map::total(|k| id_zero@));
        let s = DelegationMap { lows, m };
        s
    }
    
    pub proof fn valid_implies_complete(&self)
        requires
            self.valid(),
        ensures
            self@.dom().is_full(),
    {
    }
    
    // Returns the greatest_lower_bound as evidence for the proof of correctness for set
    fn get_internal(&self, k: &K) -> (res: (ID, Ghost<KeyIterator<K>>))
        requires
            self.valid(),
        ensures
            ({
                let (id, glb) = res;
                &&& id@ == self@[*k]
                &&& self.lows.greatest_lower_bound_spec(KeyIterator::new_spec(*k), glb@)
                &&& id@.valid_physical_address()
            }),
    {
        let ki = KeyIterator::new(k.clone());
        let glb = self.lows.greatest_lower_bound(&ki);
        proof {
            let glb_k = *glb.get();
            assert(self.lows@.contains_key(glb_k));  // OBSERVE
            let hi = choose|hi| 
                self.lows.gap(glb, hi) && #[trigger]
                KeyIterator::between(glb, ki, hi);  // OBSERVE
            assert(KeyIterator::between(KeyIterator::new_spec(glb_k), ki, hi));
            // OBSERVE The following is required; unclear why the line above isn't sufficient
            assert(self.lows@.contains_key(glb_k) && self.lows.gap(KeyIterator::new_spec(glb_k), hi)
                && KeyIterator::between(
                KeyIterator::new_spec(glb_k),
                KeyIterator::new_spec(*k),
                hi,
            ));
        }
        let id = (*self.lows.get(glb.get()).unwrap()).clone_up_to_view();
        (id, Ghost(glb))
    }
    
    pub fn get(&self, k: &K) -> (id: ID)
        requires
            self.valid(),
        ensures
            id@ == self@[*k],
            id@.valid_physical_address(),
    {
        let (id, glb_ret) = self.get_internal(k);
        id
    }
    
    // Maps keys from [lo, hi) to dst
    pub fn set(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID)
        requires
            old(self).valid(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            forall|ki: KeyIterator<K>| 
                #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> self@[*ki.get()] == dst@,
            forall|ki: KeyIterator<K>| 
                !ki.is_end_spec() && !(#[trigger]
                KeyIterator::between(*lo, ki, *hi)) ==> self@[*ki.get()] == old(self)@[*ki.get()],
    {
        if lo.lt(&hi) {
            let ghost mut glb;
            if !hi.is_end()  {
                // Get the current value of hi
                let (id, glb_ret) = self.get_internal(hi.get());
                proof {
                    glb = glb_ret@;
                }
                // Set it explicitly
                self.lows.set(hi.get().clone(), id);
            }
            let ghost mut pre_erase;
            proof {
                pre_erase = self.lows@;
            }
            let ghost mut pre_erase_vec;
            proof {
                pre_erase_vec = self.lows;
            }
            self.lows.erase(&lo, &hi);
            let ghost mut erased;
            proof {
                erased = self.lows@;
            }
            let ghost mut erased_vec;
            proof {
                erased_vec = self.lows;
            }
            self.lows.set(lo.get().clone(), clone_end_point(dst));
            self.m = Ghost(
                self.m@.union_prefer_right(
                    Map::new(
                        |k| KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi),
                        |k| dst@,
                    ),
                ),
            );
            assert(self@.dom().is_full()) by {
                assert_sets_equal!(self@.dom(), Set::full());
            }
            assert(self.lows@.contains_key(K::zero_spec())) by {
                let ki = KeyIterator::new_spec(K::zero_spec());
                assert_by_contradiction!(!lo.lt_spec(ki), {
                    K::zero_properties();
                    K::cmp_properties();
                });
                if lo == ki {
                } else {
                    assert(ki.lt_spec(*lo)) by {
                        K::zero_properties();
                    }
                }
            };
            assert forall|k, i, j| 
                self.lows@.contains_key(i) && self.lows.gap(KeyIterator::new_spec(i), j)
                    && #[trigger]
                KeyIterator::between(
                    KeyIterator::new_spec(i),
                    KeyIterator::new_spec(k),
                    j,
                ) implies self@[k] == self.lows@[i]@ by {
                let ii = KeyIterator::new_spec(i);
                let ki = KeyIterator::new_spec(k);
                if KeyIterator::between(*lo, ki, *hi) {
                    assert(self@[k] == dst@);
                    assert_by_contradiction!(ii == lo, {
                        if lo.lt_spec(ii) {
                            K::cmp_properties();
                        } else {
                            K::cmp_properties();
                            assert(ii.lt_spec(*lo));
                            // We have ii < lo < hi && ii <= k < j, and nothing in (ii, j)
                            // and lo <= k < hi
                            // ==> ii < lo <= k < j
                            assert(lo.lt_spec(j));
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        }
                    });
                    assert(self.lows@[i]@ == dst@);
                } else if ki.lt_spec(*lo) {
                    assert(self@[k] == old(self)@[k]);
                    assert(!(ki.geq_spec(*lo) && ki.lt_spec(*hi)));
                    assert(erased.contains_key(i));
                    assert(ii != hi) by {
                        K::cmp_properties();
                    };
                    assert(old(self).lows@.contains_key(i));
                    assert(self.lows@[i] == old(self).lows@[i]);
                    assert(old(self).lows.gap(ii, j)) by {
                        assert_by_contradiction!(!lo.lt_spec(j), {
                            K::cmp_properties();
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        });
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall|m| KeyIterator::new_spec(m).lt_spec(*lo) implies (old(
                            self,
                        ).lows@.contains_key(m) == #[trigger]
                        self.lows@.contains_key(m)) by {
                            K::cmp_properties();
                        };
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall|mi| ii.lt_spec(mi) && mi.lt_spec(j) implies !(#[trigger]
                        old(self).lows@.contains_key(*mi.get())) by {
                            K::cmp_properties();
                        }
                    };
                    assert(old(self)@[k] == old(self).lows@[i]@);
                } else {
                    // We have:
                    //   self.lows@.contains i
                    //   nothing in (i, j)
                    //   i < k < j
                    //   lo < hi <= k < j
                    assert(ki.geq_spec(*hi));
                    assert(self@[k] == old(self)@[k]);
                    assert(!hi.is_end());
                    assert((ii != hi && old(self)@[k] == old(self).lows@[i]@) || self@[k]
                        == self.lows@[i]@) by {
                        assert((ii != hi && old(self).lows@.contains_key(i)) || ii == hi) by {
                            assert_by_contradiction!(!ii.lt_spec(*lo), {
                                // Flaky proof here
                                K::cmp_properties();
                            });
                            assert_by_contradiction!(ii != lo, {
                                // We need the following to prove hi is in self.lows@
                                assert(!hi.lt_spec(*hi)) by { K::cmp_properties(); };
                                assert(pre_erase.contains_key(*hi.get()));
                                assert(erased.contains_key(*hi.get()));
                                assert(self.lows@.contains_key(*hi.get()));

                                // But we have i < hi < j
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };

                                // which violates lows.gap(i, j)
                                //assert(false);
                            });
                            assert(lo.lt_spec(ii)) by {
                                K::cmp_properties();
                            };
                            // lo < i ==>
                            // lo < i <= k < j
                            // lo < hi <= k < j
                            assert_by_contradiction!(!ii.lt_spec(*hi), {
                                // If this were true, we would have i < hi < j,
                                // which violates gap(i, j)
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };
                                //assert(false);
                            });
                            // Therefore hi <= i
                            if ii == hi {
                            } else {
                                // hi < i   ==> keys from i to j in lows didn't change
                                assert(erased.contains_key(i));
                                assert(pre_erase.contains_key(i));
                                assert(old(self).lows@.contains_key(i));
                                //                                assert forall |m| ii.lt_spec(m) && m.lt_spec(j)
                                //                                        implies !(#[trigger] old(self)@.contains_key(*m.get())) by {
                                //                                    K::cmp_properties();
                                ////                                    assert_by_contradiction!(!old(self)@.contains_key(*m.get()), {
                                ////                                        K::cmp_properties();
                                ////                                        assert(self@.contains_key(*m.get()));
                                ////                                        assert(KeyIterator::between(ii, m, j));
                                ////                                        self.lows.gap_means_empty(ii, j, m);
                                ////                                    });
                                //                                };
                                K::cmp_properties();  // Flaky
                                assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                            }
                        };
                        //assert(erased.gap(i, j));
                        if ii == hi {
                            //   lo < (hi == i) < k < j
                            assert(pre_erase[*hi.get()]@ == old(self)@[*hi.get()]);
                            assert(erased[*hi.get()] == pre_erase[*hi.get()]) by {
                                K::cmp_properties();
                            };
                            assert(self@[*hi.get()] == erased[*hi.get()]@);
                            // Above establishes self@[*hi.get()] == old(self)@[*hi.get()]
                            assert(erased_vec.gap(ii, j));
                            assert(pre_erase_vec.gap(ii, j));
                            assert(old(self).lows.gap(ii, j));
                            if old(self).lows@.contains_key(i) {
                                assert(old(self)@[k] == old(self).lows@[i]@);
                            } else {
                                // old(self) did not contain hi; instead we added it inside the `if !hi.is_end()` clause
                                // But we know that glb was the closest bound to hi and glb is in old(self).lows@
                                assert(old(self).lows@.contains_key(*glb.get()));
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert_by_contradiction!(!ii.lt_spec(glb), {
                                    K::cmp_properties();
                                });
                                assert(ii.geq_spec(glb));
                                // Establish the preconditions to use @old(self).valid() to relate
                                // old(self)@[k] to old(self).lows@[glb]
                                let hi_hi = choose|h| 
                                    #[trigger]
                                    old(self).lows.gap(glb, h) && KeyIterator::between(glb, *hi, h);
                                assert(old(self).lows.gap(glb, j)) by {
                                    old(self).lows.mind_the_gap();
                                }
                                assert(KeyIterator::between(glb, ki, j)) by {
                                    K::cmp_properties();
                                };
                                assert(old(self)@[k] == old(self).lows@[*glb.get()]@);
                                // Directly prove that  self@[k] == self.lows@[i]
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert(old(self).lows@[*glb.get()]@ == self@[*hi.get()]);
                                assert(old(self)@[k] == self@[*hi.get()]);
                                assert(self@[k] == self@[*hi.get()]);
                                assert(*lo.get() != i) by {
                                    K::cmp_properties();
                                };
                                assert(self.lows@[i] == erased[i]);
                                assert(self@[*hi.get()] == self.lows@[i]@);
                                assert(self@[k] == self.lows@[i]@);
                            }
                        } else {
                            assert(old(self).lows@.contains_key(i));
                            assert(erased_vec.gap(KeyIterator::new_spec(i), j));
                            // Prove that we can't be in the second clause of erase's gap
                            // postcondition
                            assert_by_contradiction!(!(hi.geq_spec(j) ||
                                                       hi.is_end_spec() ||
                                                       !erased_vec@.contains_key(*hi.get())), {
                                K::cmp_properties();
                            });
                            // Therefore we must be in the first clause, and hence:
                            assert(pre_erase_vec.gap(KeyIterator::new_spec(i), j));
                            assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                        }
                    };
                    if ii != hi {
                        assert(erased.contains_key(i)) by {
                            K::cmp_properties();
                        };
                        assert(self.lows@[i] == erased[i]) by {
                            K::cmp_properties();
                        };
                        assert(pre_erase.contains_key(i)) by {
                            K::cmp_properties();
                        };
                        assert(erased[i] == pre_erase[i]);
                        assert(old(self).lows@.contains_key(i));
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(self.lows@[i] == old(self).lows@[i]);
                    }
                }
            }
        }
        assert forall|ki: KeyIterator<K>| 
            #[trigger]
            KeyIterator::between(*lo, ki, *hi) implies self@[*ki.get()] == dst@ by {
            K::cmp_properties();
        };
        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
        assert forall|ki: KeyIterator<K>| 
            !ki.is_end_spec() && !(#[trigger]
            KeyIterator::between(*lo, ki, *hi)) implies self@[*ki.get()] == old(
            self,
        )@[*ki.get()] by {
            K::cmp_properties();
        };
    }
    
    pub open spec fn range_consistent(
        self,
        lo: &KeyIterator<K>,
        hi: &KeyIterator<K>,
        dst: &ID,
    ) -> bool {
        forall|k| 
            KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) ==> (#[trigger]
            self@[k]) == dst@
    }
    
    proof fn not_range_consistent(
        self,
        lo: &KeyIterator<K>,
        hi: &KeyIterator<K>,
        dst: &ID,
        bad: &KeyIterator<K>,
    )
        requires
            KeyIterator::between(*lo, *bad, *hi),
            self@.contains_key(*bad.get()),
            self@[*bad.get()] != dst@,
        ensures
            !self.range_consistent(lo, hi, dst),
    {
    }
    
    proof fn extend_range_consistent(
        self,
        x: &KeyIterator<K>,
        y: &KeyIterator<K>,
        z: &KeyIterator<K>,
        dst: &ID,
    )
        requires
            self.range_consistent(x, y, dst),
            self.range_consistent(y, z, dst),
        ensures
            self.range_consistent(x, z, dst),
    {
    }
    
    proof fn range_consistent_subset(
        self,
        x: &KeyIterator<K>,
        y: &KeyIterator<K>,
        x_inner: &KeyIterator<K>,
        y_inner: &KeyIterator<K>,
        dst: &ID,
    )
        requires
            self.range_consistent(x, y, dst),
            x_inner.geq_spec(*x),
            !y.lt_spec(*y_inner),
        ensures
            self.range_consistent(x_inner, y_inner, dst),
    {
        K::cmp_properties();
    }
    
    proof fn empty_key_range_is_consistent(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, id: &ID)
        requires
            lo.geq_spec(*hi),
        ensures
            self.range_consistent(lo, hi, id),
    {
        K::cmp_properties();
    }
    
    proof fn all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall|i| #![auto] lo <= i <= hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(
                &KeyIterator::new_spec(self.lows.keys@[lo as int]),
                &KeyIterator::new_spec(self.lows.keys@[hi as int]),
                id,
            ),
        decreases hi - lo,
    {
        self.almost_all_keys_agree(lo, hi, id);
    }
    
    proof fn almost_all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall|i| #![auto] lo <= i < hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(
                &KeyIterator::new_spec(self.lows.keys@[lo as int]),
                &KeyIterator::new_spec(self.lows.keys@[hi as int]),
                id,
            ),
        decreases hi - lo,
    {
        let lo_k = self.lows.keys@[lo as int];
        let hi_k = self.lows.keys@[hi as int];
        let lo_ki = KeyIterator::new_spec(lo_k);
        let hi_ki = KeyIterator::new_spec(hi_k);
        if lo_ki.geq_spec(hi_ki) {
            self.empty_key_range_is_consistent(&lo_ki, &hi_ki, id);
        } else {
            assert(lo_ki.lt_spec(hi_ki) && lo < hi) by {
                K::cmp_properties();
            }
            let lo_next = (lo + 1) as usize;
            let lo_next_k = self.lows.keys@[lo_next as int];
            let lo_next_ki = KeyIterator::new_spec(lo_next_k);
            assert(self.lows.gap(lo_ki, lo_next_ki)) by {
                K::cmp_properties();
            }
            assert(self.range_consistent(&lo_ki, &lo_next_ki, id));
            self.almost_all_keys_agree(lo_next, hi, id);
            self.extend_range_consistent(&lo_ki, &lo_next_ki, &hi_ki, id);
        }
    }
    
    pub fn range_consistent_impl(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID) -> (b:
        bool)
        requires
            self.valid(),
        ensures
            b == self.range_consistent(lo, hi, dst),
    {
        if lo.lt(hi) {
            let lo_glb_index = self.lows.greatest_lower_bound_index(lo);
            let hi_glb_index = self.lows.greatest_lower_bound_index(hi);
            assert(lo_glb_index <= hi_glb_index) by {
                K::cmp_properties();
            };
            let ghost lo_glb = self.lows.keys@[lo_glb_index as int];
            let hi_glb = self.lows.keys.index(hi_glb_index);
            let ghost lo_glb_ki = KeyIterator::new_spec(lo_glb);
            let ghost hi_glb_ki = KeyIterator::new_spec(hi_glb);
            //let ret = self.lows.keys_agree(Ghost(&lo_glb), lo_glb_index, Ghost(&hi_glb), hi_glb_index, dst);
            let (agree, almost) = self.lows.keys_in_index_range_agree(
                lo_glb_index,
                hi_glb_index,
                dst,
            );
            let ret = if agree {
                // Simple case where everything agrees
                true
            } else if !agree && almost && !hi.is_end() && hi_glb.cmp(hi.get()).is_eq()  {
                // Corner case where almost everything agrees; the one disagreement
                // is exactly at the hi key, which isn't included in range_consistent
                true
            } else {
                // Simpler case where disagreement occurs before hi
                false
            };
            proof {
                let end_ki = KeyIterator::end_spec();
                if ret {
                    if agree {
                        self.all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        if hi_glb_index == self.lows.keys@.len() - 1 {
                            assert forall|k| 
                                KeyIterator::between(
                                    hi_glb_ki,
                                    KeyIterator::new_spec(k),
                                    end_ki,
                                ) implies (#[trigger]
                            self@[k]) == dst@ by {
                                K::cmp_properties();
                            }
                            assert(self.range_consistent(&hi_glb_ki, &end_ki, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &end_ki, dst);
                            self.range_consistent_subset(&lo_glb_ki, &end_ki, lo, hi, dst);
                        } else {
                            let hi_next_index = hi_glb_index + 1;
                            let hi_next = self.lows.keys@[hi_next_index];
                            let hi_next_ki = KeyIterator::new_spec(hi_next);
                            assert(self.lows.gap(hi_glb_ki, hi_next_ki)) by {
                                K::cmp_properties();
                            }
                            assert_by_contradiction!(!hi.above(hi_next), {
                                K::cmp_properties();
                                assert(self.lows@.contains_key(hi_next));   // Trigger conclusion of glb_spec
                            });
                            assert(!hi.is_end_spec()) by {
                                K::cmp_properties();
                            }
                            let upper = choose|u| 
                                #[trigger]
                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                    hi_glb_ki,
                                    *hi,
                                    u,
                                );
                            assert(self.range_consistent(&hi_glb_ki, &upper, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &upper, dst);
                            assert(!upper.lt_spec(*hi)) by {
                                K::cmp_properties();
                            }
                            self.range_consistent_subset(&lo_glb_ki, &upper, lo, hi, dst);
                        }
                    } else {
                        assert(!agree && almost && !hi.is_end() && hi_glb.cmp_spec(
                            *hi.get_spec(),
                        ).eq());
                        self.almost_all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        self.range_consistent(
                            &KeyIterator::new_spec(self.lows.keys@[lo_glb_index as int]),
                            &KeyIterator::new_spec(self.lows.keys@[hi_glb_index as int]),
                            dst,
                        );
                        assert(lo.geq_spec(lo_glb_ki));
                        self.range_consistent_subset(&lo_glb_ki, &hi_glb_ki, lo, hi, dst);
                    }
                } else {
                    assert(!agree);
                    let bad_index = choose|bad_index| 
                        #![auto]
                        lo_glb_index <= bad_index <= hi_glb_index
                            && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                    let bad = self.lows.keys@[bad_index];
                    let bad_ki = KeyIterator::new_spec(bad);
                    if bad_index == lo_glb_index {
                        let lo_k = *lo.get();
                        let upper = choose|u| 
                            #[trigger]
                            self.lows.gap(lo_glb_ki, u) && KeyIterator::between(
                                lo_glb_ki,
                                KeyIterator::new_spec(lo_k),
                                u,
                            );
                        assert(self.lows@.contains_key(lo_glb));
                        assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                        assert(KeyIterator::between(
                            KeyIterator::new_spec(lo_glb),
                            KeyIterator::new_spec(lo_k),
                            upper,
                        ));
                        assert(self@[lo_k] == self.lows@[lo_glb]@);
                        assert(self.lows@[lo_glb]@ == self.lows@[self.lows.keys@[bad_index]]@);
                        assert(self@[lo_k] != dst@);
                        assert(KeyIterator::between(*lo, *lo, *hi)) by {
                            K::cmp_properties();
                        }
                        self.not_range_consistent(lo, hi, dst, lo);
                    } else {
                        assert(hi.is_end_spec() ==> hi_glb_ki != hi);
                        assert(hi_glb_ki.cmp_spec(*hi).eq() == (hi_glb_ki == hi)) by {
                            K::cmp_properties();
                        };
                        assert(bad_index > lo_glb_index && !bad_ki.lt_spec(*lo)) by {
                            K::cmp_properties();
                            assert(self.lows@.contains_key(bad));  // Trigger conclusion of glb_spec
                        };
                        // almost == (self@[self.keys@[hi_glb_index as int]]@ != v@ &&
                        //            (forall |i| #![auto] lo_glb_index <= i < hi_glb_index ==> self@[self.keys@[i]]@ == v@)))
                        if almost {
                            assert(hi_glb_index == bad_index);
                            if !hi.is_end_spec()  {
                                if hi_glb_ki == hi {
                                    assert(ret);
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));
                                    let upper = choose|u| 
                                        #![auto]
                                        self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                            hi_glb_ki,
                                            *hi,
                                            u,
                                        );
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, upper)) by {
                                        K::cmp_properties();
                                    };
                                    assert(self@[bad] == self.lows@[bad]@);
                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            } else {
                                if hi_glb_ki == hi {
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));
                                    //let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                    };
                                    assert(self@[bad] == self.lows@[bad]@);
                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }
                        } else {
                            assert(self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ || !(
                            forall|i| 
                                #![auto]
                                lo_glb_index <= i < hi_glb_index ==> self.lows@[self.lows.keys@[i]]@
                                    == dst@));
                            if self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ {
                                if !hi.is_end_spec()  {
                                    if hi_glb_ki == hi {
                                        assert(bad_index < hi_glb_index);
                                        // Proof X
                                        let bad_next = self.lows.keys@[bad_index + 1];
                                        let bad_next_ki = KeyIterator::new_spec(bad_next);
                                        assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                            K::cmp_properties();
                                        }
                                        assert(self@[bad] != dst@) by {
                                            // Trigger DelegationMap::valid
                                            assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                K::cmp_properties();
                                            };
                                            assert(KeyIterator::between(
                                                bad_ki,
                                                bad_ki,
                                                bad_next_ki,
                                            )) by {
                                                K::cmp_properties();
                                            };
                                        }
                                        self.not_range_consistent(lo, hi, dst, &bad_ki);
                                    } else {
                                        // TODO: Duplicates entire Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X
                                            assert(bad_index + 1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index + 1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                                K::cmp_properties();
                                            }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                    K::cmp_properties();
                                                };
                                                assert(KeyIterator::between(
                                                    bad_ki,
                                                    bad_ki,
                                                    bad_next_ki,
                                                )) by {
                                                    K::cmp_properties();
                                                };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose|u| 
                                                #![auto]
                                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                                    hi_glb_ki,
                                                    *hi,
                                                    u,
                                                );
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper)
                                                    && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(
                                                    hi_glb_ki,
                                                    hi_glb_ki,
                                                    upper,
                                                )) by {
                                                    K::cmp_properties();
                                                };  // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }
                                    }
                                } else {
                                    if hi_glb_ki == hi {
                                        assert(false);
                                    } else {
                                        // Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X
                                            assert(bad_index + 1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index + 1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                                K::cmp_properties();
                                            }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                                    K::cmp_properties();
                                                };
                                                assert(KeyIterator::between(
                                                    bad_ki,
                                                    bad_ki,
                                                    bad_next_ki,
                                                )) by {
                                                    K::cmp_properties();
                                                };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose|u| 
                                                #![auto]
                                                self.lows.gap(hi_glb_ki, u) && KeyIterator::between(
                                                    hi_glb_ki,
                                                    *hi,
                                                    u,
                                                );
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper)
                                                    && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(
                                                    hi_glb_ki,
                                                    hi_glb_ki,
                                                    upper,
                                                )) by {
                                                    K::cmp_properties();
                                                };  // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }
                                    }
                                }
                            }
                            if !(forall|i: int| 
                                lo_glb_index <= i < hi_glb_index ==> #[trigger]
                                (self.lows@[self.lows.keys@[i]]@) == dst@)  {
                                // Choose a badder index
                                let bad_index = choose|bad_index| 
                                    #![auto]
                                    lo_glb_index <= bad_index < hi_glb_index
                                        && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                                let bad = self.lows.keys@[bad_index];
                                let bad_ki = KeyIterator::new_spec(bad);
                                if bad_index == lo_glb_index {
                                    // TODO: Duplicates proof above
                                    let lo_k = *lo.get();
                                    let upper = choose|u| 
                                        #[trigger]
                                        self.lows.gap(lo_glb_ki, u) && KeyIterator::between(
                                            lo_glb_ki,
                                            KeyIterator::new_spec(lo_k),
                                            u,
                                        );
                                    assert(self.lows@.contains_key(lo_glb));
                                    assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                                    assert(KeyIterator::between(
                                        KeyIterator::new_spec(lo_glb),
                                        KeyIterator::new_spec(lo_k),
                                        upper,
                                    ));
                                    assert(self@[lo_k] == self.lows@[lo_glb]@);
                                    assert(self.lows@[lo_glb]@
                                        == self.lows@[self.lows.keys@[bad_index]]@);
                                    assert(self@[lo_k] != dst@);
                                    assert(KeyIterator::between(*lo, *lo, *hi)) by {
                                        K::cmp_properties();
                                    }
                                    self.not_range_consistent(lo, hi, dst, lo);
                                } else {
                                    // TODO: This duplicates Proof X
                                    assert(bad_index + 1 < self.lows.keys@.len());
                                    let bad_next = self.lows.keys@[bad_index + 1];
                                    let bad_next_ki = KeyIterator::new_spec(bad_next);
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by {
                                        K::cmp_properties();
                                        assert(self.lows@.contains_key(bad));  // Trigger conclusion of glb_spec
                                    }
                                    assert(self@[bad] != dst@) by {
                                        // Trigger DelegationMap::valid
                                        assert(self.lows.gap(bad_ki, bad_next_ki)) by {
                                            K::cmp_properties();
                                        };
                                        assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki))
                                            by {
                                            K::cmp_properties();
                                        };
                                    }
                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }
                        }
                    }
                }
            }
            ret
        } else {
            proof {
                self.empty_key_range_is_consistent(lo, hi, dst);
            }
            true
        }
    }
}

impl DelegationMap<AbstractKey> {
    pub fn delegate_for_key_range_is_host_impl(
        &self,
        lo: &KeyIterator<AbstractKey>,
        hi: &KeyIterator<AbstractKey>,
        dst: &ID,
    ) -> (b: bool)
        requires
            self.valid(),
        ensures
            b == AbstractDelegationMap::delegate_for_key_range_is_host(
                AbstractDelegationMap(self@),
                KeyRange { lo: *lo, hi: *hi },
                dst@,
            ),
    {
        let ret = self.range_consistent_impl(lo, hi, dst);
        proof {
            let kr = KeyRange { lo: *lo, hi: *hi };
            if ret {
                assert forall|k| #[trigger] kr.contains(k) implies self@[k] == dst@ by {
                    assert(KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi));  // Trigger for range_consistent
                }
            } else {
                let k = choose|k| 
                    KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) && #[trigger]
                    self@[k] != dst@;
                assert(kr.contains(k));
            }
        }
        ret
    }
}

// Another waste of time because we missed an verifier::ext_equal on a struct. :eyeroll:
impl DelegationMap<CKey> {
    pub proof fn lemma_set_is_update(
        pre: Self,
        post: Self,
        lo: KeyIterator<CKey>,
        hi: KeyIterator<CKey>,
        dst: &ID,
    )
        requires
            pre.valid(),
            dst@.valid_physical_address(),
            // fn set postconditions
            post.valid(),
            forall|ki: KeyIterator<CKey>| 
                #[trigger]
                KeyIterator::between(lo, ki, hi) ==> post@[*ki.get()] == dst@,
            forall|ki: KeyIterator<CKey>| 
                !ki.is_end_spec() && !(#[trigger]
                KeyIterator::between(lo, ki, hi)) ==> post@[*ki.get()] == pre@[*ki.get()],
        ensures
            AbstractDelegationMap(post@) =~= AbstractDelegationMap(pre@).update(
                KeyRange { lo, hi },
                dst@,
            ),
    {
        //         let setted = AbstractDelegationMap(post@);
        //         let updated = AbstractDelegationMap(pre@).update(KeyRange{lo, hi}, dst@);
        //         assert forall |k| setted.0.contains_key(k) <==> updated.0.contains_key(k) by {}
        //         assert forall |k| setted.0.contains_key(k) implies setted.0[k] == updated.0[k] by {}
        //AbstractDelegationMap(self@.union_prefer_right(Map::new(|k| newkr.contains(k), |k| host)))
        //         assert( AbstractDelegationMap(post@) =~= AbstractDelegationMap(pre@).update(KeyRange{lo, hi}, dst@) );
    }
}

} // verus!
// end verus!

}

mod endpoint_hashmap_t{
#![verus::trusted]
//! Wrapper around Rust HashMap with Vec<u8> keys, with a Map view
//!
//! Due to trouble with generics this is a copy-paste of hashmap_t.rs but for HashMap<Vec<u8>, V>.

use std::collections;
use vstd::map::*;
use vstd::prelude::*;

use crate::abstract_end_point_t::AbstractEndPoint;
use crate::io_t::EndPoint;

verus! {

#[verifier(external_body)]
pub struct HashMap<
    #[verifier(strictly_positive)]
    V,
> {
    m: collections::HashMap<EndPoint, V>,
}

impl<V> HashMap<V> {
    /// The abstract contents of the HashMap.
    pub closed spec fn view(self) -> Map<AbstractEndPoint, V>;
    
    #[verifier(external_body)]
    pub fn new() -> (out: Self)
        ensures
            out@ == Map::<AbstractEndPoint, V>::empty(),
    {
        HashMap { m: collections::HashMap::new() }
    }
    
    #[verifier(external_body)]
    pub fn insert(&mut self, key: &EndPoint, value: V)
        ensures
            self@ == old(self)@.insert(key@, value),
    {
        let key_clone: EndPoint = key.clone_up_to_view();
        self.m.insert(key_clone, value);
    }
    
    pub open spec fn spec_index(self, key: &EndPoint) -> V
        recommends
            self@.contains_key(key@),
    {
        self@[key@]
    }
    
    pub open spec fn get_spec(map_v: Map<AbstractEndPoint, V>, key: AbstractEndPoint) -> (value:
        Option<V>) {
        if map_v.dom().contains(key) {
            Some(map_v[key])
        } else {
            None
        }
    }
    
    #[verifier(external_body)]
    pub fn get<'a>(&'a self, key: &EndPoint) -> (value: Option<&'a V>)
        ensures
            value == match Self::get_spec(self@, key@) {
                Some(v) => Some(&v),
                None => None,
            },
    {
        match self.m.get(&key) {
            std::option::Option::Some(v) => Some(v),
            std::option::Option::None => None,
        }
    }
    
    // TODO replace put_spec with insert spec
    pub open spec fn put_spec(
        old_map_v: Map<AbstractEndPoint, V>,
        new_map_v: Map<AbstractEndPoint, V>,
        key: AbstractEndPoint,
        value: V,
    ) -> bool {
        new_map_v == old_map_v.insert(key, value)//         &&& new_map_v.contains_key(key)
        //         &&& new_map_v[key] == value
        //         &&& forall |k| /*#![auto]*/ k != key ==> if old_map_v.contains_key(k) {
        //                 (#[trigger] new_map_v.contains_key(k)) && new_map_v[k] == old_map_v[k]
        //             } else {
        //                 !new_map_v.contains_key(k)
        //             }
    
    }
    
    //#[verifier(external_body)]
    //TODO: replace call sites with insert
    pub fn put(&mut self, key: &EndPoint, value: V)
        ensures
            Self::put_spec(old(self)@, self@, key@, value),
    {
        self.insert(key, value);
    }
    
    pub open spec fn swap_spec(
        old_map_v: Map<AbstractEndPoint, V>,
        new_map_v: Map<AbstractEndPoint, V>,
        key: AbstractEndPoint,
        input_value: V,
        output_value: V,
        default_value: V,
    ) -> bool {
        &&& match Self::get_spec(old_map_v, key) {
            Some(v) => output_value == v,
            None => output_value == default_value,
        }
        &&& Self::put_spec(old_map_v, new_map_v, key, input_value)
    }
    
    #[verifier(external_body)]
    pub fn swap<'a>(&'a mut self, key: &EndPoint, updated_value: &'a mut V, default_value: V)
        ensures
            Self::swap_spec(
                old(self)@,
                self@,
                key@,
                *old(updated_value),
                *updated_value,
                default_value,
            ),
    {
        match self.m.get_mut(key) {
            Some(v) => core::mem::swap(v, updated_value),
            None => {
                let mut swap_tmp = default_value;
                core::mem::swap(&mut swap_tmp, updated_value);
                self.put(key, swap_tmp);
            },
        }
    }
    
    #[verifier(external_body)]
    pub fn keys(&self) -> (out: Vec<EndPoint>)
        ensures
            out@.map_values(|e: EndPoint| e@).to_set() == self@.dom(),
    {
        self.m.keys().map(|k| k.clone_up_to_view()).collect()
    }
}

} // verus!

}

mod environment_t{
#![verus::trusted]
use vstd::prelude::*;

verus! {

pub struct LPacket<IdType, MessageType> {
    pub dst: IdType,
    pub src: IdType,
    pub msg: MessageType,
}

#[is_variant]
pub enum LIoOp<IdType, MessageType> {
    Send { s: LPacket<IdType, MessageType> },
    Receive { r: LPacket<IdType, MessageType> },
    TimeoutReceive {  },
    ReadClock { t: int },
}

#[is_variant]
pub enum LEnvStep<IdType, MessageType> {
    HostIos { actor: IdType, ios: Seq<LIoOp<IdType, MessageType>> },
    DeliverPacket { p: LPacket<IdType, MessageType> },
    AdvanceTime {  },
    Stutter {  },
}

pub struct LHostInfo<IdType, MessageType> {
    pub queue: Seq<LPacket<IdType, MessageType>>,
}

pub struct LEnvironment<
    #[verifier(maybe_negative)]
    IdType,
    #[verifier::maybe_negative]
    MessageType,
> {
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

}

mod hashmap_t{
#![verus::trusted]
//! Wrapper around Rust HashMap, with a Map view
//!
//! Due to trouble with generics this is a HashMap<u64, Vec<u8>>. We need the
//! key to be hashable, and the view uses the view of the values.
//!
//! TODO: we will also need some hashmaps with Vec<u8> as their keys.

// This thing is trusted because the corresponding Dafny code uses Dafny's built-in
// map types. Verus' map library isn't mature enough to export all the verification
// promises we need yet, so we're hacking those promises in here.
// (That, and some of the operations require assuming the inputs are immutable,
// which the values are not, so we need a clone-up-to-view sort of promise.)

use crate::host_protocol_t::*;
use crate::keys_t::*;
use std::collections;
use vstd::map::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    /// The abstract contents of the CKeyHashMap.
    pub closed spec fn view(self) -> Map<AbstractKey, Seq<u8>>;
    
    #[verifier(external_body)]
    pub fn new() -> (out: CKeyHashMap)
        ensures
            out@ == Map::<AbstractKey, Seq<u8>>::empty(),
    {
        CKeyHashMap { m: collections::HashMap::new() }
    }
    
    #[verifier::external_body]
    pub fn len(&self) -> (l: usize)
        ensures
            l as int == self@.len(),
    {
        self.m.len()
    }
    
    #[verifier(external_body)]
    pub fn insert(&mut self, key: CKey, value: Vec<u8>)
        ensures
            self@ == old(self)@.insert(key, value@),
    {
        //TODO(parno): think carefully of properties we must demand of Key for this ensures to be correct.
        // (If Key has a nondeterministic hash, this ensures will be a lie.)
        self.m.insert(key, value);
    }
    
    #[verifier(external_body)]
    pub fn remove(&mut self, key: &CKey)
        ensures
            self@ == old(self)@.remove(*key),
    {
        panic!()
    }
    
    #[verifier(external_body)]
    pub fn get(&self, key: &CKey) -> (value: Option<&Vec<u8>>)
        ensures
            (match value {
                Some(v) => self@.dom().contains(*key) && self@[*key] == v@,
                None => !self@.dom().contains(*key),
            }),
    {
        //TODO(parno): think carefully of properties we must demand of Key for this ensures to be correct.
        // (If Key has a nondeterministic hash, this ensures will be a lie.)
        match self.m.get(&key) {
            std::option::Option::Some(v) => Some(v),
            std::option::Option::None => None,
        }
    }
    
    #[verifier(external_body)]
    pub fn bulk_update(&mut self, kr: &KeyRange::<CKey>, other: &Self)
        ensures
            self@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey| 
                    (old(self)@.dom().contains(k) || other@.dom().contains(k)) && (kr.contains(k)
                        ==> other@.dom().contains(k)),
                |k: AbstractKey| 
                    if other@.dom().contains(k) {
                        other@[k]
                    } else {
                        old(self)@[k]
                    },
            ),
    {
        panic!()
    }
    
    #[verifier(external_body)]
    pub fn bulk_remove(&mut self, kr: &KeyRange::<CKey>)
        ensures
            self@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey| old(self)@.dom().contains(k) && !kr.contains(k),
                |k: AbstractKey| old(self)@[k],
            ),
    {
        panic!()
    }
    
    pub closed spec fn spec_to_vec(&self) -> Vec<CKeyKV>;
    
    pub closed spec fn spec_from_vec(v: Vec<CKeyKV>) -> Self;
    
    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>)
        ensures
            res == self.spec_to_vec(),
    {
        let mut v: std::vec::Vec<(u64, std::vec::Vec<u8>)> = self.m.iter().map(
            |(k, v)| (k.ukey, v.clone()),
        ).collect();
        v.sort();
        v.into_iter().map(|(k, v)| CKeyKV { k: CKey { ukey: k }, v }).collect()
    }
    
    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_from_vec))]
    pub fn from_vec(v: Vec<CKeyKV>) -> (res: Self)
        ensures
            res == Self::spec_from_vec(v),
    {
        let mut res = CKeyHashMap::new();
        for CKeyKV { k, v } in v {
            res.insert(k, v);
        }
        res
    }
    
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn lemma_to_vec(self)
        ensures
            #[trigger(self.spec_to_vec())]
            Self::spec_from_vec(self.spec_to_vec()) == self,
            self.spec_to_vec().len() == self@.dom().len(),
            spec_sorted_keys(self.spec_to_vec()),
            (forall|i: int| 
                #![trigger(self.spec_to_vec()[i])]
                0 <= i < self.spec_to_vec().len() ==> {
                    let (k, v) = self.spec_to_vec()[i]@;
                    self@.contains_pair(k, v)
                }),
    ;
    
    #[verifier(external_body)]
    pub proof fn lemma_to_vec_view(self, other: Self)
        ensures
            (self@ == other@ <==> self.spec_to_vec()@ == other.spec_to_vec()@) && (self@ == other@
                <==> (self.spec_to_vec().len() == other.spec_to_vec().len() && forall|i: int| 
                #![auto]
                0 <= i < self.spec_to_vec().len() ==> self.spec_to_vec()[i]@
                    == other.spec_to_vec()[i]@)),
    ;
    
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn lemma_from_vec(v: Vec<CKeyKV>)
        ensures
            #[trigger(Self::spec_from_vec(v))]
            spec_sorted_keys(v) ==> Self::spec_from_vec(v).spec_to_vec() == v,
    ;
    
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (out: Self)
        ensures
            out@ == self@,
    {
        Self::from_vec(self.to_vec())
    }
    
    #[verifier(external_body)]
    pub fn valid(&self) -> (b: bool)
        ensures
            b == valid_hashtable(self@),
    {
        panic!()
    }
    
    pub open spec fn filter_spec(self, fs: FnSpec(CKey) -> bool) -> Map<AbstractKey, Seq<u8>> {
        Map::<AbstractKey, Seq<u8>>::new(
            |k: AbstractKey| self@.dom().contains(k) && fs(k),
            |k: AbstractKey| self@[k],
        )
    }
    
    #[verifier(external_body)]
    // iter is not supported
    pub fn filter<F: Fn(CKey) -> bool>(&self, f: F) -> (res: Self)
        ensures
            res@ == self.filter_spec(|k| f.ensures((k,), true)),
    {
        let mut res = CKeyHashMap::new();
        let mut iter = self.m.iter();
        let cur: Option<(&CKey, &Vec<u8>)> = iter.next();
        while cur.is_some() {
            let Some((key, val)) = cur else {
                panic!()  /* covered by while condition */
            };
            res.insert(key.clone(), val.clone());
        }
        res
    }
}

// pub struct KeyIterator
// {
//     view: Set<CKey>,
//     iter: Keys<CKey, Vec<u8>>,
// }
pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

impl CKeyKV {
    pub open spec fn view(self) -> (AbstractKey, Seq<u8>) {
        (self.k, self.v@)
    }
}

pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    // ckeykvlt ensures that this forall does not create a trigger loop on
    // v@[i].k.ukey, v@[i+1].k.ukey, ...
    //
    // we weren't able to fix this by making the whole < the trigger
    forall|i: int, j: int| 
        0 <= i && i + 1 < v.len() && j == i + 1 ==> #[trigger]
        ckeykvlt(v@[i], v@[j])
}

} // verus!

}

mod host_impl_t{
#![verus::trusted]
//! Translates multiple files:
//!
//! Most of Common/Framework/Host.s.dfy
//!
//! Some parts of Common/Framework/Host.i.dfy (due to lack of an exact analogy
//! to module refinement)
//!
//! ConcreteConfiguration is not translated.
use builtin::*;
use builtin_macros::*;

use crate::abstract_end_point_t::*;
use crate::abstract_service_t::*;
use crate::args_t::*;
use crate::environment_t::*;
use crate::host_impl_v::abstractify_raw_log_to_ios; // TODO(jonh) dependency on _v
use crate::host_protocol_t;
use crate::host_protocol_t::*;
use crate::io_t::*;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_message_t::*;
use vstd::prelude::*;

// Note sleazy inclusion of untrusted file, since we can't yet set up the adversarial auditing
// separation with traits.
use crate::host_impl_v::*;

verus! {

type Ios = Seq<NetEvent>;

// Verus doesn't yet support associated types or trait type parameters, so we can't
// abstract the ConcreteConfiguration type as IronFleet does. Instead, our protocol
// init accepts the Args on the command line.
//
//pub trait ConcreteConfiguration {
//    open spec fn init(&self) -> bool;
//
//    open spec fn to_servers(&self) -> Set<EndPoint>;
//}
pub struct EventResults {
    // What netc actually observed:
    pub recvs: Seq<NetEvent>,
    pub clocks: Seq<NetEvent>,
    pub sends: Seq<NetEvent>,
    /// What we were trying to make happen:
    /// ios may claim an event that doesn't appear in event_seq() if, say, the netc socket broke on
    /// send. We already received, so the only way we can refine is by claiming we finished the
    /// corresponding send (in ios). In this case, the postcondition of next_ensures gives
    /// us the out because !netc.ok allows ios!=event_seq().
    pub ios: Ios,
}

impl EventResults {
    pub open spec fn event_seq(self) -> Seq<NetEvent> {
        self.recvs + self.clocks + self.sends
    }
    
    pub open spec fn well_typed_events(self) -> bool {
        &&& forall|i| 
            0 <= i < self.recvs.len() ==> self.recvs[i].is_Receive()
            &&& forall|i| 
                0 <= i < self.clocks.len() ==> self.clocks[i].is_ReadClock()
                    || self.clocks[i].is_TimeoutReceive()
                &&& forall|i| 
                    0 <= i < self.sends.len() ==> self.sends[i].is_Send()
                    &&& self.clocks.len() <= 1
    }
    
    pub open spec fn empty() -> Self {
        EventResults { recvs: seq!(), clocks: seq!(), sends: seq!(), ios: seq!() }
    }
}

/// Translates Common/Framework/Host.s
///
/// This changes the way NetClient/HostEnvironment is managed slightly - instead
/// of giving the host a reference to the NetClient to hold on to in init (as in
/// Ironfleet), we only let the host borrow it in each call to next_impl and it
/// is owned by the main loop.
// Obligations for the implementer's HostState implementation.
// We'd like to do this with a trait, so that the auditor could tell statically
// that this trusted file doesn't depend on any surprises from the verified file.
impl HostState {
    pub open spec fn init_ensures(netc: &NetClient, args: Args, rc: Option<Self>) -> bool {
        match rc {
            None => true,
            Some(host_state) => {
                &&& netc.ok()  // port of env.ok.ok()
                
                &&& host_state.invariants(&netc.my_end_point())
                &&& crate::host_protocol_t::init(
                    host_state@,
                    netc.my_end_point(),
                    abstractify_args(args),
                )
            },
        }
    }
    
    /// No longer takes a netclient and environment; a netclient is loaned to
    /// the HostState only for next_impl.
    pub fn init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
        requires
            netc.valid(),// IronFleet also gives us netc.IsOpen(), but it seems to be rotted, so we're ignoring it
    
        ensures
            Self::init_ensures(netc, *args, rc),
    {
        Self::real_init_impl(netc, args)
    }
    
    //    spec fn parse_command_line_configuration(args:Seq<Seq<u8>>) -> CC;
    //    spec fn concrete_config_init(cc: CC) -> bool;
    //    spec fn concrete_config_to_servers(cc: CC) -> Set<EndPoint>;
    pub open spec fn next_requires(self, netc: NetClient) -> bool {
        &&& self.invariants(&netc.my_end_point())
        &&& netc.state().is_Receiving()  // new wrt ironfleet because we're encoding reduction rules in NetClient interface instead of by reading the history.
    
    }
    
    pub open spec fn next_ensures(
        old_self: Self,
        old_netc: NetClient,
        new_self: Self,
        new_netc: NetClient,
        rc: (bool, Ghost<EventResults>),
    ) -> bool {
        let (ok, res) = rc;
        {
            &&& ok == new_netc.ok()
            &&& ok ==> new_self.invariants(&new_netc.my_end_point())
            &&& ok ==> Self::next(old_self.view(), new_self.view(), res@.ios)
            &&& ok ==> res@.event_seq() == res@.ios
            &&& (ok || res@.sends.len() > 0) ==> new_netc.history() == old_netc.history()
                + res@.event_seq()
            &&& res@.well_typed_events()
        }
    }
    
    // This ports Impl/LiveSHT/Host.i::HostNextImpl, riiiiight?
    pub fn next_impl(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
    {
        self.real_next_impl(netc)
    }
    
    // this ports Protocol/SHT/Host.i.dfy ::Host_Next
    pub open spec fn next(pre: AbstractHostState, post: AbstractHostState, ios: Ios) -> bool {
        host_protocol_t::next(pre, post, abstractify_raw_log_to_ios(ios))
    }
}

} // verus!

}

mod host_impl_v{
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
use vstd::map::*; // TODO(andrea): prelude doesn't give me the macros?
use vstd::prelude::*;
use vstd::seq_lib::*; // TODO(andrea): prelude doesn't give me the macros?
use vstd::set::*;
use vstd::set_lib::*; // TODO(andrea): prelude doesn't give me the macros?

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
    forall|i: int| 0 <= i && i < ios.len() ==> ios[i].is_Send()
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
        forall|i: int| 0 <= i && i < net_events@.len() ==> net_events@[i].is_Send(),
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
    assert(forall|i| 0 <= i < res.recvs.len() ==> res.recvs[i].is_Receive());
    assert(forall|i| 
        0 <= i < res.clocks.len() ==> res.clocks[i].is_ReadClock()
            || res.clocks[i].is_TimeoutReceive());
    assert(forall|i| 0 <= i < res.sends.len() ==> res.sends[i].is_Send());
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
    requires//h@.valid_key_range() // (See Distributed/Services/SHT/AppInterface.i.dfy: ValidKey() == true)

        forall|k| 
            h@.contains_key(k) ==>   /*#[trigger] valid_key(k) &&*/
            #[trigger]
            valid_value(h@[k]),
    ensures
        ext@ =~= extract_range(h@, *kr),
{
    let lambda = |key| -> (b: bool) 
        ensures
            b == kr.contains(key),
        { kr.contains_exec(&key) };
    assert forall|ak| #[trigger] kr.contains(ak) implies lambda.ensures((ak,), true) by {
        assume(false);  // seems to be a Verus gap?
    }
    h.filter(lambda)
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
        &&& self.delegation_map.valid()// TODO why no valid_key?
        
        &&& (forall|k| 
            self.h@.dom().contains(k) ==> #[trigger]
            valid_value(self.h@[k]))
        &&& self.sd.valid()
        &&& match &self.received_packet {
            Some(v) => v.abstractable() && v.msg.is_Message() && v.dst@ == self.constants.me@,
            None => true,
        }
        &&& self.constants.valid()
        &&& self.num_delegations
            < self.constants.params.max_delegations// TODO why no delegation_map.lows
    
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
                None => host_protocol_t::parse_args(abstractify_args(*args)).is_None(),
                Some(vec) => {
                    &&& host_protocol_t::parse_args(abstractify_args(*args)).is_Some()
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
            if !end_point.valid_physical_address()  {
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
    // Not sure why it's okay that this is now entirely verified, not part of
    // the trusted application spec.
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
        if !unique  {
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
        let zero_key = SHTKey::zero();
          //SHTKey{ukey: 0};   // for some reason we can't make this call inside the ::new method below
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
    pub fn deliver_packet_seq(&self, netc: &mut NetClient, packets: &Vec<CPacket>) -> (rc: (
        bool,
        Ghost<Seq<NetEvent>>,
        Ghost<Seq<LSHTIo>>,
    ))
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
                            0 <= i && i < net_events.len() ==> net_events[i].is_Send())
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
        if !ok  {
            (ok, Ghost(Seq::<NetEvent>::empty()), Ghost(Seq::<LSHTIo>::empty()))
        } else {
            let ghost ios: Seq<LSHTIo> = map_sent_packet_seq_to_ios(packets@);
            proof {
                assert(abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@)
                    == extract_packets_from_abstract_ios(ios)) by {
                    lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(
                        ios,
                        |io: LSHTIo| io.is_Send(),
                    );
                    assert(ios.filter(|io: LSHTIo| io.is_Send()) == ios);
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
                            0 <= idx && idx < seq1.len() && #[trigger]
                            seq1[idx] == x;
                        assert(seq2[idx] == x);
                        assert(set2.contains(x));
                    };
                    assert forall|x| set2.contains(x) implies set1.contains(x) by {
                        let idx: int = choose|idx: int| 
                            0 <= idx && idx < seq2.len() && #[trigger]
                            seq2[idx] == x;
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
                        |io: LSHTIo| io.is_Send(),
                    );
                    assert(ios.filter(|io: LSHTIo| io.is_Send()) == ios);
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
                assert forall|i| 
                    0 <= i < ios.len() && #[trigger]
                    ios[i].is_Send() implies !ios[i].get_Send_s().msg.is_InvalidMessage() by {
                    let msg = ios[i].get_Send_s().msg;
                    assert(msg == abstractify_cpacket_to_lsht_packet(packets[i]).msg);
                    assert(outbound_packet_is_valid(&packets[i]));
                };
                assert forall|i: int| 0 <= i && i < events@.len() implies events@[i].is_Send() by {
                    assert(send_log_entry_reflects_packet(events@[i], &packets[i]));
                };
            }
            (ok, events, Ghost(ios))
        }
    }
    
    // Translates Impl/LiveSHT/SchedulerImpl.i.dfy :: DeliverOutboundPackets
    pub fn deliver_outbound_packets(&self, netc: &mut NetClient, packets: &Vec<CPacket>) -> (rc: (
        bool,
        Ghost<Seq<NetEvent>>,
        Ghost<Seq<LSHTIo>>,
    ))
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
                            0 <= i && i < net_events.len() ==> net_events[i].is_Send())
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
                    clocks: seq![ iop ],
                    sends: seq![],
                    ios: seq![ iop ],
                };
                proof {
                    old_self.delegation_map.valid_implies_complete();
                    assert(next_step(
                        old_self@,
                        self@,
                        abstractify_raw_log_to_ios(res.ios),
                        Step::ReceivePacket,
                    ));
                }
                return (true, Ghost(res));  // iop should also appear as a clock?
            },
            ReceiveResult::Packet { cpacket } => {
                match cpacket.msg {
                    CSingleMessage::InvalidMessage {  } => {
                        let ghost res = EventResults {
                            recvs: seq![ net_event@ ],
                            clocks: seq![],
                            sends: seq![],
                            ios: seq![ net_event@ ],
                        };
                        proof {
                            old_self.delegation_map.valid_implies_complete();
                            let ios = abstractify_raw_log_to_ios(res.ios);
                            let r = ios[0].get_Receive_r();
                            let pkt = Packet { dst: r.dst, src: r.src, msg: r.msg };
                            let sent_packets = extract_packets_from_abstract_ios(ios);
                            lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty(
                                ios,
                                |io: LSHTIo| io.is_Send(),
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
                        }
                        return (true, Ghost(res));
                    },
                    _ => {
                        assert(*old(self) == *self);
                        let ghost mid_netc = *netc;
                        let (ok, Ghost(event_results), Ghost(ios)) = self.host_next_receive_packet(
                            netc,
                            Ghost(old(netc).history()),
                            cpacket,
                            Ghost(net_event@),
                        );
                        if !ok  {
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
    
    // Jon and Jay L found a bug in the Ironfleet spec, in Host.s.dfy. It says:
    // ```
    // ensures  (ok || |sends| > 0) ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
    // ``
    // but this isn't strong enough. Indeed, in Dafny we were able to unwittingly
    // ``trick'' it by just setting the sends to empty. What it should say is that
    // if ok was false, then the env history reflects a prefix of the receives,
    // clocks, and sends we intended to perform, and the HostNext holds on the
    // full list of receives, clocks, and sends we intended to perform.
    //
    // So here we have to trick the spec in the same way that the Ironfleet Dafny
    // code did.
    proof fn empty_event_results() -> (event_results: EventResults)
        ensures
            event_results.well_typed_events(),
            event_results.ios == event_results.event_seq(),
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
                receive_event.get_Receive_r(),
            ),
        ensures
            ({
                let (ok, Ghost(event_results), Ghost(ios)) = rc;
                &&& self.invariants(&netc.my_end_point())
                &&& self@.constants == old(self)@.constants
                &&& ok
                    == netc.ok()// Because all `net_events` are sends, the condition "even if ok is false, if we sent at least one
                // packet..." is implied by "even if ok is false, if `net_events` has length > 0...".
                
                &&& (ok || event_results.sends.len() > 0) ==> netc.history() == old_netc_history
                    + event_results.ios// There's supposed to be a distinction between the ios that we intended to do and the
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
                // TODO(andrea): wow, .map and .to_set are pretty poorly automated. :vP
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
        if !ok  {
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
            lemma_filter_skip_rejected(ios, |io: LSHTIo| io.is_Send(), 1);
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
        }
        (ok, Ghost(event_results), Ghost(ios))
    }
    
    /// Impl/SHT/HostModel.i HostModelReceivePacket
    ///
    /// In Dafny, ack (rc.1) isn't an Option, it is an InvalidPacket that didn't have any ensures
    /// obligations. That is confusing (surprising) to read, but changing it to an Option would
    /// entail making the corresponding change in the host_protocol so that abstraction stays
    /// parallel. That's too big of a change; we're going to stay true to the original lyrics.
    fn host_model_receive_packet(&mut self, cpacket: CPacket) -> (rc: (
        Vec<CPacket>,
        Ghost<CPacket>,
    ))
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
                )// The Dafny Ironfleet "common preconditions" take an explicit cpacket, but we need to talk
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
        &&& pre.received_packet.is_Some()
        &&& pre.received_packet.get_Some_0().msg.is_Message()
        &&& match pre.received_packet.get_Some_0().msg.get_Message_m() {
            Message::Delegate { range: range, h: h } => !({
                // no need to check for valid_key_range(range)
                &&& valid_hashtable(h)
                &&& !range.is_empty()
                &&& pre.received_packet.get_Some_0().msg.get_Message_dst().valid_physical_address()
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
        &&& self.received_packet.is_Some()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg.is_Message()
                &&& cpacket.msg.get_Message_m().is_GetRequest()
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
        &&& self.received_packet.is_None()
    }
    
    // Translates Impl/SHT/HostState.i.dfy :: NextSetRequestPreconditions
    pub closed spec fn next_set_request_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg.is_Message()
                &&& cpacket.msg.get_Message_m().is_SetRequest()
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
        &&& self.received_packet.is_None()
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
                &&& cpacket.msg.is_Message()
                &&& cpacket.msg.get_Message_m().is_Delegate()
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
        &&& self.received_packet.is_None()
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
                &&& cpacket.msg.is_Message()
                &&& cpacket.msg.get_Message_m().is_Shard()
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
        &&& self.received_packet.is_None()
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
            0 <= i && i < sent_packets.len() ==> (#[trigger]
            sent_packets[i].msg).is_Message() || sent_packets[i].msg.is_Ack())
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
                    assert(v.is_some() ==> valid_value(v.get_Some_0()@));
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
                                pkt.msg.get_Message_seqno(),
                                pkt.msg.get_Message_m().get_GetRequest_key(),
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
                                pkt.msg.get_Message_seqno(),
                                pkt.msg.get_Message_m().get_GetRequest_key(),
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
                                    pkt.msg.get_Message_seqno(),
                                    pkt.msg.get_Message_m(),
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
                                            pkt.msg.get_Message_seqno(),
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
                                        assert(seq![abstractify_cpacket_to_lsht_packet(p)].map_values(
                                        |lp: LSHTPacket| extract_packet_from_lsht_packet(lp))[0]
                                            == Packet {
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
                                            pkt.msg.get_Message_seqno(),
                                            pkt.msg.get_Message_m(),
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
            forall|ki: KeyIterator<CKey>| 
                #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> post@[*ki.get()] == dst@,
            forall|ki: KeyIterator<CKey>| 
                !ki.is_end_spec() && !(#[trigger]
                KeyIterator::between(*lo, ki, *hi)) ==> post@[*ki.get()] == pre@[*ki.get()],
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
            forall|k| 
                pre@.dom().contains(k) ==> #[trigger]
                valid_value(pre@[k]),
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
            forall|k| 
                post@.dom().contains(k) ==> #[trigger]
                valid_value(post@[k]),
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
                        } else if !endpoints_contain(&self.constants.host_ids, &cpacket.src)  {
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
                            if !this_host_owns_range  {
                                self.received_packet = None;
                                return sent_packets;
                            }
                            let h = extract_range_impl(&self.h, kr);
                            if h.len() >= 62 {
                                self.received_packet = None;
                                return sent_packets;
                            }// assert( !next_shard_wrapper_must_reject(old(self)@, m@) );
                            // Comically, the Dafny code called ExtractRange twice!
                            
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
                                        // (jonh/lorch) we couldn't figure out why this lemma proof
                                        // consists entirely of a =~=, yet playing that same
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
                                    // sure would be nice to not copy-paste this stuff, but
                                    // we're borrowing kr.
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
                                        )
                                            =~= seq![extract_packet_from_lsht_packet(abstractify_cpacket_to_lsht_packet(p))]);  // twiddle
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
    fn process_received_packet_next_impl(&mut self, netc: &mut NetClient) -> (rc: (
        bool,
        Ghost<EventResults>,
    ))
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
                &&& (ok || res@.sends.len() > 0) ==> (*netc).history() == (*old(netc)).history()
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
        if !self.should_process_received_message_impl()  {
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
            return (true, res)
        }// Second, check if this is something other than a CSingleMessage::Message (e.g., an ack)
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
        assert(self.received_packet.is_Some());
        assert(self.received_packet.get_Some_0().msg.is_Message());
        assert(self.host_state_common_preconditions());
        let sent_packets = self.host_model_next_receive_message();
        let (ok, net_event_log, ios) = self.deliver_outbound_packets(netc, &sent_packets);
        if !ok  {
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
    pub fn host_noreceive_noclock_next(&mut self, netc: &mut NetClient) -> (rc: (
        bool,
        Ghost<EventResults>,
    ))
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
        if !ok  {
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
            assert forall|i| 
                #![auto]
                0 <= i < aios.len()
                    && aios[i].is_Send() implies !aios[i].get_Send_s().msg.is_InvalidMessage() by {
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
                |io: LSHTIo| io.is_Send(),
            );
            // Reach into an inconvenient trigger
            assert forall|i| 0 <= i < extract_seq.len() implies extract_seq[i] == view_seq[i] by {
                assert(send_log_entry_reflects_packet(event_results@.ios[i], &sent_packets@[i]));
            }
            assert(view_seq =~= extract_seq);  // prompt ext equality
            assert(next_step(old(self)@, self@, aios, Step::SpontaneouslyRetransmit));  // witness
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
        if !rc.0  {
            return rc;
        }
        assert(self.invariants(&netc.my_end_point()));
        self.next_action_index = (self.next_action_index + 1) % 3;
        rc
    }
}

} // verus!

}

mod host_protocol_t{
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
    >,// We decided to elide resendCount and nextActionIndex from this translated spec
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
    &&& (forall|k| 
        h.dom().contains(k) ==> valid_key(k) && #[trigger]
        valid_value(h[k]))
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
    
    }
    ||| {
        // internal buffer full or okay to ignore packets; drop this message and wait for it to be retransmitted.
        &&& pre.received_packet is Some || okay_to_ignore_packets()
        &&& post == pre
        &&& out == Set::<Packet>::empty()
    }
}

// Translates Protocol/LiveSHT/Scheduler.i.dfy :: ExtractSentPacketsFromIos
pub open spec fn extract_sent_packets_from_ios(ios: Seq<LSHTIo>) -> Seq<LSHTPacket> {
    ios.filter(|io: LSHTIo| io.is_Send()).map_values(|io: LSHTIo| io.get_Send_s())
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
        ios[0].is_Receive(),
        pre.delegation_map.is_complete(),
{
    let r = ios[0].get_Receive_r();
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
    &&& if ios[0].is_TimeoutReceive() {
        &&& post == pre
        &&& ios.len() == 1
    } else {
        &&& pre.delegation_map.is_complete()
        &&& ios[0].is_Receive()
        &&& forall|i| 
            1 <= i < ios.len() ==>   /*#[trigger]*/
            ios[i].is_Send()
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
        &&& sm.get_Message_dst() == src
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.get_Message_m().is_GetRequest()
    &&& post.delegation_map == pre.delegation_map
    &&& post.h == pre.h
    &&& post.num_delegations == pre.num_delegations
    &&& (exists|sm, m, b| 
        next_get_request_reply(
            pre,
            post,
            pkt.src,
            pkt.msg.get_Message_seqno(),
            pkt.msg.get_Message_m().get_GetRequest_key(),
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
        reqm.is_SetRequest(),
{
    let k = reqm.get_SetRequest_key();
    let ov = reqm.get_SetRequest_value();
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
        &&& sm.get_Message_dst() == src
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.get_Message_m().is_SetRequest()
    &&& exists|sm: SingleMessage<Message>, replym: Message, should_send: bool| 
        next_set_request_complete(
            pre,
            post,
            pkt.src,
            pkt.msg.get_Message_seqno(),
            pkt.msg.get_Message_m(),
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.get_Message_m().is_Delegate()
    &&& if pre.constants.host_ids.contains(pkt.src) {
        let m = pkt.msg.get_Message_m();
        &&& post.delegation_map == pre.delegation_map.update(
            m.get_Delegate_range(),
            pre.constants.me,
        )
        &&& post.h == bulk_update_hashtable(pre.h, m.get_Delegate_range(), m.get_Delegate_h())
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
    &&& should_send ==> recipient == sm.get_Message_dst()
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
    let recipient = m.get_Shard_recipient();
    let kr = m.get_Shard_range();
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    let m: Message = pkt.msg.get_Message_m();
    let recipient = m.get_Shard_recipient();
    let kr = m.get_Shard_range();
    &&& m.is_Shard()
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.get_Message_m().is_Reply()
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
        pkt.msg.is_Message(),
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.get_Message_m().is_Redirect()
    &&& out == Set::<Packet>::empty()
    &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
}

pub open spec(checked) fn should_process_received_message(pre: AbstractHostState) -> bool {
    &&& pre.received_packet.is_some()
    &&& pre.received_packet.get_Some_0().msg.is_Message()
    &&& {
        ||| pre.received_packet.get_Some_0().msg.get_Message_m().is_Delegate()
        ||| pre.received_packet.get_Some_0().msg.get_Message_m().is_Shard()
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
        let packet = pre.received_packet.get_Some_0();
        &&& {
            ||| next_get_request(pre, post, packet, out)
            ||| next_set_request(pre, post, packet, out)
            ||| next_delegate(pre, post, packet, out)
            ||| next_shard_wrapper(pre, post, packet, out)
            ||| next_reply(pre, post, packet, out)
            ||| next_redirect(pre, post, packet, out)
        }
        &&& post.received_packet.is_None()
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
    &&& forall|i| 
        0 <= i < ios.len() ==> ios[i].is_Send()
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
            &&& forall|i| 
                0 <= i < ios.len() ==> ios[i].is_Send()
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
    &&& ios[0].is_Receive()
    &&& ios[0].get_Receive_r().msg.is_InvalidMessage()
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
    &&& pre.received_packet.get_Some_0().msg.is_Message()
    &&& match pre.received_packet.get_Some_0().msg.get_Message_m() {
        Message::Delegate { range: range, h: h } => !({
            // no need to check for valid_key_range(range)
            // (See Distributed/Services/SHT/AppInterface.i.dfy: ValidKey() == true)
            &&& valid_hashtable(h)
            &&& !range.is_empty()
            &&& pre.received_packet.get_Some_0().msg.get_Message_dst().valid_physical_address()
        }),
        _ => false,
    }
    &&& if should_process_received_message(pre) {
        post == AbstractHostState { received_packet: None, ..pre }
    } else {
        post == pre
    }
}

#[is_variant]
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
    if end_points.is_None() || end_points.unwrap().len() == 0 {
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
        0 <= i < ios.len() && ios[i].is_Send() ==> !ios[i].get_Send_s().msg.is_InvalidMessage()
}

pub open spec(checked) fn next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.wf()
    &&& pre.constants == post.constants
    &&& exists|step| 
        next_step(pre, post, ios, step)
        &&& no_invalid_sends(
            ios,
        )  // A double check that our trusted translation of Host satisfies OnlySentMarshallableData

}

} // verus!

}

mod io_t{
#![verus::trusted]
use builtin::*;
use builtin_macros::*;

use crate::environment_t::*;
use vstd::prelude::*;
use vstd::prelude::*;
//
use crate::abstract_end_point_t::*;
use crate::args_t::*;
use vstd::slice::*;
// for clone_vec placeholder

// For DuctTapeProfiler
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use std::net::UdpSocket;

verus! {

/// NOTE: no longer need HostEnvironment, its state is inlined in NetClient
///
/// - OkState is replaced with State
/// - NetState is history
/// - NowState is not (yet) implemented
/// - files was empty in Ironfleet
pub struct HostEnvironment {}

//pub struct Environment {
//    ok: bool
//}
// #[derive(Copy, Clone)]
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

//impl Clone for EndPoint {
//    fn clone(&self) -> (res: EndPoint)
//        ensures res@ == self@
//    {
//        EndPoint{id: clone_vec_u8(&self.id)}
//    }
//}
impl EndPoint {
    // Verus unimpl: Can't call clone through the trait
    pub fn clone_up_to_view(&self) -> (res: EndPoint)
        ensures
            res@ == self@,
    {
        EndPoint { id: clone_vec_u8(&self.id) }
    }
    
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
    
    // EndPointIsAbstractable
    // (this has generally been unused)
    #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }
    
    // TODO: actually call this everywhere IronFleet calls it.
    pub open spec fn valid_public_key(&self) -> bool {
        self@.valid_physical_address()
    }
    
    // Translates Common/Native/Io.s.dfy
    pub fn valid_physical_address(&self) -> (out: bool)
        ensures
            out == self@.valid_physical_address(),
    {
        self.id.len() < 0x100000
    }
}

pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint> {
    end_points@.map(|i, end_point: EndPoint| end_point@)
}

pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;

pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;

pub type History = Seq<NetEvent>;

#[is_variant]
pub enum State {
    Receiving,
    Sending,
    Error,
}

#[is_variant]
pub enum NetcReceiveResult {  // Not to be confused with Ironfleet's ReceiveResult type, which contains a parsed message
    Received { sender: EndPoint, message: Vec<u8> },
    TimedOut,
    Error,
}

pub struct IronfleetIOError {
    pub message: String,
}

pub closed spec fn from_trusted_code() -> bool {
    true
}

#[verifier(external_body)]
pub struct NetClientCPointers {
    get_time_func: extern "C" fn () -> u64,
    receive_func: extern "C" fn (
        i32,
        *mut bool,
        *mut bool,
        *mut *mut std::vec::Vec<u8>,
        *mut *mut std::vec::Vec<u8>,
    ),
    send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
}

#[verifier::external_body]
pub struct DuctTapeProfiler {
    last_event: SystemTime,
    last_report: SystemTime,
    event_counter: HashMap<std::string::String, u64>,
}

impl DuctTapeProfiler {
    #[verifier(external)]
    fn new() -> Self {
        println!("Report-ready");
        DuctTapeProfiler {
            last_event: SystemTime::now(),
            last_report: SystemTime::now(),
            event_counter: HashMap::new(),
        }
    }
    
    #[verifier(external)]
    fn duration_as_ns(duration: &Duration) -> u64 {
        duration.as_secs() * 1_000_000_000 + duration.subsec_nanos() as u64
    }
    
    #[verifier(external)]
    fn mark_duration(&mut self, label: &str) {
        let now = SystemTime::now();
        let duration_ns = Self::duration_as_ns(
            &now.duration_since(self.last_event).expect("arrow of time"),
        );
        self.increment_event(label, duration_ns);
        self.last_event = now;
        self.maybe_report(&now);
    }
    
    #[verifier(external)]
    fn record_event(&mut self, label: &str) {
        self.increment_event(label, 1);
    }
    
    #[verifier(external)]
    fn increment_event(&mut self, label: &str, incr: u64) {
        if let Some(entry) = self.event_counter.get_mut(label) {
            *entry += incr;
        } else {
            self.event_counter.insert(label.to_string(), incr);
        }
    }
    
    #[verifier(external)]
    fn maybe_report(&mut self, now: &SystemTime) {
        let report_period = 1 * 1_000_000_000;
        let report_duration_ns = Self::duration_as_ns(
            &now.duration_since(self.last_report).expect("arrow of time"),
        );
        if report_duration_ns > report_period {
            self.increment_event("report-duration-ns", report_duration_ns);
            self.report();
            self.last_report = now.clone();
            self.event_counter = HashMap::new();
        }
    }
    
    #[verifier(external)]
    fn report(&self) {
        for (key, value) in &self.event_counter {
            if key.ends_with("-ns") {
                let ms = *value as f64 / 1e6;
                println!("{key}: {ms} ms");
            } else {
                println!("{key}: {value} count");
            }
        }
        println!("");
    }
}

pub struct NetClient {
    state: Ghost<State>,
    history: Ghost<History>,
    end_point: EndPoint,
    c_pointers: NetClientCPointers,
    profiler: DuctTapeProfiler,
}

impl NetClient {
    //////////////////////////////////////////////////////////////////////////////
    // player-1 accessible interfaces (note requires from_trusted_code())
    //////////////////////////////////////////////////////////////////////////////
    #[verifier(external)]
    pub fn new(
        end_point: EndPoint,
        get_time_func: extern "C" fn () -> u64,
        receive_func: extern "C" fn (
            i32,
            *mut bool,
            *mut bool,
            *mut *mut std::vec::Vec<u8>,
            *mut *mut std::vec::Vec<u8>,
        ),
        send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
    ) -> (net_client: Self)
        requires
            from_trusted_code(),
        ensures
            net_client.state().is_Receiving(),
            net_client.history() == Seq::<NetEvent>::empty(),
            net_client.my_end_point() == end_point,
    {
        //TODO(chris): thread 'rustc' panicked at 'The verifier does not yet support the following Rust feature: non_struct_ctor', rust_verify/src/rust_to_vir_expr.rs:2796:21
        //Self{state: State::Receiving, history: todo!(), end_point}
        NetClient {
            state: Ghost(State::Receiving),
            history: Ghost(seq![]),
            end_point,
            c_pointers: NetClientCPointers {
                get_time_func: get_time_func,
                receive_func: receive_func,
                send_func: send_func,
            },
            profiler: DuctTapeProfiler::new(),
        }
    }
    
    // Main loop (Player 1 audited code) resets the state after having seen Player 2
    // complete a proof of refinement to an atomic protocol step.
    pub fn reset(&mut self)
        requires
            from_trusted_code(),
        ensures
            self.state().is_Receiving(),
            self.my_end_point() == old(
                self,
            ).my_end_point(),// TODO: surely something needs to be said about history?
    
    {
        self.state = Ghost(State::Receiving);
    }
    
    //////////////////////////////////////////////////////////////////////////////
    // player-2 accessible interfaces
    //////////////////////////////////////////////////////////////////////////////
    // This state field is how Player 2 proves that it calls receive before send.
    pub closed spec fn state(&self) -> State {
        self.state@
    }
    
    /// Translates calls to env.ok.ok().
    pub open spec fn ok(&self) -> bool {
        !self.state().is_Error()
    }
    
    /// translates NetClient.NetClientIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.ok()
        &&& self.my_end_point().abstractable()
    }
    
    pub closed spec fn history(&self) -> History {
        self.history@
    }
    
    /// Translates MyPublicKey()
    pub closed spec fn my_end_point(&self) -> AbstractEndPoint {
        self.end_point@
    }
    
    pub fn get_my_end_point(&self) -> (ep: EndPoint)
        ensures
            ep@ == self.my_end_point(),
    {
        self.end_point.clone_up_to_view()
    }
    
    #[verifier(external)]
    pub fn get_time_internal(&self) -> (time: u64)
        requires
            from_trusted_code(),
    {
        (self.c_pointers.get_time_func)()
    }
    
    #[verifier(external_body)]
    pub fn get_time(&mut self) -> (time: u64)
        requires
            old(self).state().is_Receiving(),
        ensures
            ({
                &&& self.state().is_Sending()
                &&& self.history() == old(self).history() + seq![LIoOp::ReadClock{t: time as int}]
            }),
    {
        let time: u64 = self.get_time_internal();
        self.state = Ghost(State::Sending);
        self.history = Ghost(
            self.history@ + seq![LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock{t: time as int}],
        );
        time
    }
    
    #[verifier(external)]
    pub unsafe fn receive_internal(&mut self, time_limit_s: i32) -> (result: NetcReceiveResult) {
        let mut ok: bool = true;
        let mut timed_out: bool = true;
        let mut remote = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();
        let mut buffer = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();
        self.profiler.mark_duration("processing-ns");
        (self.c_pointers.receive_func)(
            time_limit_s,
            &mut ok,
            &mut timed_out,
            remote.as_mut_ptr(),
            buffer.as_mut_ptr(),
        );
        self.profiler.mark_duration("awaiting-receive-ns");
        if ok {
            if timed_out {
                self.profiler.record_event("receive-timedout");
                NetcReceiveResult::TimedOut {  }
            } else {
                self.profiler.record_event("receive-ok");
                let remote_ptr: *mut std::vec::Vec<u8> = remote.assume_init();
                let buffer_ptr: *mut std::vec::Vec<u8> = buffer.assume_init();
                let remote_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
                    remote_ptr,
                );
                let buffer_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
                    buffer_ptr,
                );
                let remote_vec: std::vec::Vec<u8> = *remote_box;
                let buffer_vec: std::vec::Vec<u8> = *buffer_box;
                let mut remote_verus_vec: Vec<u8> = Vec::new();
                remote_verus_vec = remote_vec;
                let mut buffer_verus_vec: Vec<u8> = Vec::new();
                buffer_verus_vec = buffer_vec;
                NetcReceiveResult::Received {
                    sender: EndPoint { id: remote_verus_vec },
                    message: buffer_verus_vec,
                }
            }
        } else {
            self.profiler.record_event("receive-error");
            NetcReceiveResult::Error {  }
        }
    }
    
    #[verifier(external_body)]
    pub fn receive(&mut self, time_limit_s: i32) -> (result: NetcReceiveResult)
        requires// TODO(verus:jonh): start a discussion about demanding old(self) in requires
    
            old(self).state().is_Receiving(),
        ensures
            self.my_end_point() == old(self).my_end_point(),
            match result {
                NetcReceiveResult::Received { sender, message } => {
                    &&& self.state().is_Receiving()
                    &&& sender.abstractable()
                    &&& self.history() == old(self).history()
                        + seq![
                    LIoOp::Receive{
                        r: LPacket{
                            dst: self.my_end_point(),
                            src: sender@,
                            msg: message@}
                    }]
                },
                NetcReceiveResult::TimedOut {  } => {
                    &&& self.state().is_Sending()
                    &&& self.history() == old(self).history()
                        + seq![LIoOp/*TODO(verus) fix name when qpath fix*/::TimeoutReceive{}]
                },
                NetcReceiveResult::Error {  } => { self.state().is_Error() },
            },
    {
        let result: NetcReceiveResult = unsafe { self.receive_internal(time_limit_s) };
        match result {
            NetcReceiveResult::Received { ref sender, ref message } => {
                self.history = Ghost(
                    self.history@
                        + seq![LIoOp::Receive { r: LPacket::<AbstractEndPoint, Seq<u8>> { dst: self.my_end_point(), src: sender@, msg: message@ } } ],
                );
            },
            NetcReceiveResult::TimedOut {  } => {
                self.history = Ghost(self.history@ + seq![LIoOp::TimeoutReceive{}]);
            },
            NetcReceiveResult::Error {  } => {
                self.state = Ghost(State::Error {  });
            },
        }
        result
    }
    
    #[verifier(external)]
    pub unsafe fn send_internal(&mut self, remote: &EndPoint, message: &Vec<u8>) -> (result: Result<
        (),
        IronfleetIOError,
    >) {
        let remote_raw: *const u8 = remote.id.as_ptr();
        let message_raw: *const u8 = message.as_ptr();
        let b: bool = (self.c_pointers.send_func)(
            remote.id.len() as u64,
            remote_raw,
            message.len() as u64,
            message_raw,
        );
        if b {
            Ok(())
        } else {
            Err(
                IronfleetIOError {
                    message: String::from_rust_string("Failed to send".to_string()),
                },
            )
        }
    }
    
    #[verifier(external_body)]
    pub fn send_internal_wrapper(&mut self, remote: &EndPoint, message: &Vec<u8>) -> (result:
        Result<(), IronfleetIOError>)
        ensures
            *self == *old(self),
    {
        unsafe { self.send_internal(remote, message) }
    }
    
    pub fn send(&mut self, recipient: &EndPoint, message: &Vec<u8>) -> (result: Result<
        (),
        IronfleetIOError,
    >)
        requires
            !old(self).state().is_Error(),
        ensures
            self.my_end_point() == old(self).my_end_point(),
            self.state().is_Error() <==> result.is_Err(),
            result.is_Ok() ==> self.state().is_Sending(),
            result.is_Ok() ==> self.history() == old(self).history()
                + seq![LIoOp::Send{s: LPacket{dst: recipient@, src: self.my_end_point(), msg: message@}}],
    {
        let result: Result<(), IronfleetIOError> = self.send_internal_wrapper(recipient, message);
        match result {
            Ok(_) => {
                self.state = Ghost(State::Sending {  });
                self.history = Ghost(
                    self.history@
                        + seq![LIoOp::Send{s: LPacket{dst: recipient@, src: self.my_end_point(), msg: message@}}],
                );
            },
            Err(_) => {
                self.state = Ghost(State::Error {  });
            },
        };
        result
    }
}

} // verus!

}

mod keys_t{
#![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::*;

use crate::app_interface_t::*;
use crate::verus_extra::clone_v::*;

verus! {

// TODO(chris): Want to write KeyTrait : VerusClone, but "The verifier does not yet support the following Rust feature: trait generic bounds"
pub trait KeyTrait: Sized {
    spec fn zero_spec() -> Self where Self: std::marker::Sized;
    
    proof fn zero_properties()
        ensures
            forall|k: Self| 
                k != Self::zero_spec() ==> (#[trigger]
                Self::zero_spec().cmp_spec(k)).lt(),
    ;
    
    spec fn cmp_spec(self, other: Self) -> Ordering;
    
    proof fn cmp_properties()
        ensures// Equality is eq  --- TODO: Without this we need to redefine Seq, Set, etc. operators that use ==
    
            forall|a: Self, b: Self| #![auto] a == b <==> a.cmp_spec(b).eq(),
            // Reflexivity of equality
            forall|a: Self| #![auto] a.cmp_spec(a).eq(),
            // Commutativity of equality
            forall|a: Self, b: Self| 
                (#[trigger]
                a.cmp_spec(b)).eq() == b.cmp_spec(a).eq(),
            // Transitivity of equality
            forall|a: Self, b: Self, c: Self| 
                #[trigger]
                a.cmp_spec(b).eq() && #[trigger]
                b.cmp_spec(c).eq() ==> a.cmp_spec(c).eq(),
            // Inequality is asymmetric
            forall|a: Self, b: Self| #[trigger] a.cmp_spec(b).lt() <==> b.cmp_spec(a).gt(),
            // Connected
            forall|a: Self, b: Self| 
                #![auto]
                a.cmp_spec(b).ne() ==> a.cmp_spec(b).lt() || b.cmp_spec(a).lt(),
            // Transitivity of inequality
            forall|a: Self, b: Self, c: Self| 
                #[trigger]
                a.cmp_spec(b).lt() && #[trigger]
                b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
            forall|a: Self, b: Self, c: Self| 
                #[trigger]
                a.cmp_spec(b).lt() && #[trigger]
                b.cmp_spec(c).le() ==> a.cmp_spec(c).lt(),
            forall|a: Self, b: Self, c: Self| 
                #[trigger]
                a.cmp_spec(b).le() && #[trigger]
                b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
    ;
    
    // zero should be smaller than all other keys
    fn zero() -> (z: Self)
        ensures
            z == Self::zero_spec(),
    ;
    
    fn cmp(&self, other: &Self) -> (o: Ordering)
        requires
            true,
        ensures
            o == self.cmp_spec(*other),
    ;
}

// Based on Rust's Ordering
#[derive(Structural, PartialEq, Eq)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }
    
    pub open spec fn cmp_spec(self, other: Self) -> Ordering {
        match (self.k, other.k) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(i), Some(j)) => { i.cmp_spec(j) },
        }
    }
    
    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None()) || (!self.k.is_None() && !other.k.is_None()
            && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }
    
    // TODO: Use the name `spec_ge` instead of `geq_spec` to enable Verus magic overloading
    pub open spec fn geq_spec(self, other: Self) -> bool {
        !self.lt_spec(other)  //|| self == other
    
    }
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

impl<K: KeyTrait + VerusClone> KeyRange<K> {
    pub open spec fn contains(self, k: K) -> bool {
        KeyIterator::<K>::between(self.lo, KeyIterator::<K>::new_spec(k), self.hi)
    }
    
    pub open spec fn is_empty(self) -> bool {
        self.lo.geq_spec(self.hi)
    }
}

impl<K: KeyTrait + VerusClone  /*+ PartialOrd*/ > KeyRange<K> {
    pub fn contains_exec(&self, k: &K) -> (b: bool)
        ensures
            b == self.contains(*k),
    {
        let ki = KeyIterator { k: Some(k.clone()) };
        !ki.lt(&self.lo) && ki.lt(&self.hi)
    }
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyIterator<K> {
    fn clone(&self) -> Self {
        KeyIterator {
            k: match &self.k {
                Some(v) => Some(v.clone()),
                None => None,
            },
        }
    }
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyRange<K> {
    fn clone(&self) -> Self {
        KeyRange { lo: self.lo.clone(), hi: self.hi.clone() }
    }
}

#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub  // workaround
     ukey: u64,
}

impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
        ensures
            out == self,
    {
        SHTKey { ukey: self.ukey }
    }
}

/*
impl std::hash::Hash for SHTKey {
}

impl std::cmp::PartialEq for SHTKey {
}

impl std::cmp::Eq for SHTKey {
}
*/
impl KeyTrait for SHTKey {
    fn zero() -> (z: Self) {
        // This assert is necessary due to https://github.com/verus-lang/verus/issues/885
        assert(SHTKey { ukey: 0 } == Self::zero_spec());
        SHTKey { ukey: 0 }
    }
    
    open spec fn zero_spec() -> Self {
        SHTKey { ukey: 0 }
    }
    
    proof fn zero_properties() {
        // Maybe this should not be necessary
        assert(forall|k: Self| 
            k != Self::zero_spec() ==> (#[trigger]
            Self::zero_spec().cmp_spec(k)).lt());
    }
    
    open spec fn cmp_spec(self, other: Self) -> Ordering {
        if self.ukey < other.ukey {
            Ordering::Less
        } else if self.ukey == other.ukey {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
    
    proof fn cmp_properties()//        ensures
    //        // Equality is eq  --- TODO: Without this we need to redefine Seq, Set, etc. operators that use ==
    //        forall |a:Self, b:Self| #![auto] a == b <==> a.cmp_spec(b).eq(),
    //        // Reflexivity of equality
    //        forall |a:Self| #![auto] a.cmp_spec(a).eq(),
    //        // Commutativity of equality
    //        forall |a:Self, b:Self| (#[trigger] a.cmp_spec(b)).eq() == b.cmp_spec(a).eq(),
    //        // Transitivity of equality
    //        forall |a:Self, b:Self, c:Self|
    //            #[trigger] a.cmp_spec(b).eq() && #[trigger] b.cmp_spec(c).eq() ==> a.cmp_spec(c).eq(),
    //        // Inequality is asymmetric
    //        forall |a:Self, b:Self|
    //            #[trigger] a.cmp_spec(b).lt() <==> b.cmp_spec(a).gt(),
    //        // Connected
    //        forall |a:Self, b:Self|
    //            #![auto] a.cmp_spec(b).ne() ==> a.cmp_spec(b).lt() || b.cmp_spec(a).lt(),
    //        // Transitivity of inequality
    //        forall |a:Self, b:Self, c:Self|
    //            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
    //        forall |a:Self, b:Self, c:Self|
    //            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).le() ==> a.cmp_spec(c).lt(),
    //        forall |a:Self, b:Self, c:Self|
    //            #[trigger] a.cmp_spec(b).le() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt()
    {
    }
    
    fn cmp(&self, other: &Self) -> (o: Ordering)//        requires true,
    //        ensures o == self.cmp_spec(*other)
    {
        if self.ukey < other.ukey {
            Ordering::Less
        } else if self.ukey == other.ukey {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl VerusClone for SHTKey {
    fn clone(&self) -> (o: Self)//ensures o == self
    {
        SHTKey { ukey: self.ukey }
    }
}

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

} // verus!

}

mod main_t{
#![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::abstract_end_point_t::*;
use crate::abstract_parameters_t::*;
use crate::abstract_service_t::*;
use crate::app_interface_t::*;
use crate::args_t::*;
use crate::delegation_map_t::*;
use crate::environment_t::*;
use crate::host_impl_t::*;
use crate::host_impl_v::*;
use crate::host_protocol_t::*;
use crate::io_t::*;
use crate::keys_t::*;
use crate::message_t::*;
use crate::network_t::*;
use crate::single_delivery_t::*;
use crate::single_message_t::*;

verus! {

// io::Error is not supported yet. Placeholder.
pub struct IronError {}

// net_impl comes from outside so this function can be verified.
pub fn sht_main(netc: NetClient, args: Args) -> Result<(), IronError>
    requires
        netc.valid(),
        netc.state().is_Receiving(),
        crate::io_t::from_trusted_code(),
{
    let mut netc = netc;  // Verus does not support `mut` arguments
    //    let mut host_c: host_protocol_t::Constants;
    //    let mut host: host_protocol_t::Variables;
    let opt_host_state: Option<HostState> = HostState::init_impl(&netc, &args);
    let mut host_state = match opt_host_state {
        None => { return Err(IronError {  }) },
        Some(thing) => thing,
    };
    let mut ok: bool = true;
    //    let config = HostState::parse_command_line_configuration(args);
    let end_point = netc.get_my_end_point();
    // This init function in Dafny is in Impl/LiveSHT/Host.i.
    // It calls LScheduler_Init, which does some scheduly stuff (which I'm hoping
    // we can ignore) and then calls Protocol/SHT/Host.i/Host_Init.
    assert(crate::host_protocol_t::init(host_state@, end_point@, abstractify_args(args)));
    while (ok) 
        invariant
            crate::io_t::from_trusted_code(),  // this predicate's value cannot change, but has to be explicitly imported into the loop invariant
            ok ==> host_state.invariants(&netc.my_end_point()),
            ok == netc.ok(),
            ok ==> netc.state().is_Receiving(),
    {
        // no need for decreases * because exec functions don't termination-check
        let old_net_history: Ghost<History> = Ghost(netc.history());
        let old_state: Ghost<HostState> = Ghost(host_state);
        let (shadow_ok, event_results) = host_state.next_impl(&mut netc);
        ok = shadow_ok;
        if ok {
            assert(host_state.invariants(&netc.my_end_point()));
            //NB these assertions are just here to help the spec auditor see we're
            //doing the right thing. They duplicate the ensures on the next_impl trait method in
            //host_impl_t.
            // Correctly executed one action
            assert(HostState::next(old_state@@, host_state@, event_results@.ios));
            // Connect the low-level IO events to the spec-level IO events
            assert(event_results@.event_seq() == event_results@.ios);
            // The event_seq obligation enable us to apply reduction. But we shouldn't need to separate these
            // events out anymore (relative to ironfleet) now that we're enforcing this ordering in the
            // NetClient interface.
            assert(netc.history() == old_net_history@ + event_results@.event_seq());
            assert(event_results@.well_typed_events());
            // Reset to allow receiving for the next atomic step.
            netc.reset();
        }
    }
    Ok(())
}

} // verus!
// verus

}

mod marshal_ironsht_specific_v{
//! All the marshalable types specific to IronSHT are stored in this file. All the types themselves
//! are defined in different modules, but the marshaling implementations (using functionality
//! provided by `marshal_v`) are written in this module.
// TODO FIXME Probably need a better name for this
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::function::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::slice::*;

use vstd::*;

use crate::args_t::clone_vec_u8;
use crate::hashmap_t::ckeykvlt;

use crate::marshal_v::*;
use crate::verus_extra::seq_lib_v::*;

verus! {

use crate::keys_t::{SHTKey, CKey, KeyRange, KeyIterator};
use crate::io_t::EndPoint;
use crate::hashmap_t::{CKeyHashMap, CKeyKV};
use crate::cmessage_v::CMessage;

/* $line_count$Proof$ */
marshalable_by_bijection! {
    /* $line_count$Proof$ */     [SHTKey] <-> [u64];
    /* $line_count$Proof$ */     forward(self) self.ukey;
    /* $line_count$Proof$ */     backward(x) SHTKey { ukey: x };
    /* $line_count$Proof$ */ }

impl SHTKey {
    /// Document that view_equal is definitionally to ==, with no explicit proof required.
    pub proof fn view_equal_spec()
        ensures
            forall|x: &SHTKey, y: &SHTKey| #[trigger] x.view_equal(y) <==> x == y,
    {
    }
}

/* $line_count$Proof$}$ */
marshalable_by_bijection! {
    /* $line_count$Proof$}$ */    [EndPoint] <-> [Vec::<u8>];
    /* $line_count$Proof$}$ */    forward(self) self.id;
    /* $line_count$Proof$}$ */    backward(x) EndPoint { id: x };
    /* $line_count$Proof$}$ */ }

impl EndPoint {
    /// Document that view_equal is definitially x@ == y@, with no explicit proof required.
    pub proof fn view_equal_spec()
        ensures
            forall|x: &EndPoint, y: &EndPoint| #[trigger] x.view_equal(y) <==> x@ == y@,
    {
    }
}

/* $line_count$Proof$ */
marshalable_by_bijection! {
    /* $line_count$Proof$ */     [KeyRange::<CKey>] <-> [(Option::<u64>, Option::<u64>)];
    /* $line_count$Proof$ */     forward(self) {
    /* $line_count$Proof$ */         (
    /* $line_count$Proof$ */             match &self.lo.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             match &self.hi.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         )
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */     backward(x) {
    /* $line_count$Proof$ */         KeyRange {
    /* $line_count$Proof$ */             lo: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.0 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             hi: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.1 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         }
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */ }

/* $line_count$Proof$ */
derive_marshalable_for_struct! {
    /* $line_count$Proof$ */     pub struct CKeyKV {
    /* $line_count$Proof$ */         pub k: CKey,
    /* $line_count$Proof$ */         pub v: Vec::<u8>,
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */ }

pub exec fn sorted_keys(v: &Vec<CKeyKV>) -> (res: bool)
    ensures
        res == crate::hashmap_t::spec_sorted_keys(*v),
{
    if v.len() <= 1 {
        true
    } else {
        let mut idx = 1;
        while idx < v.len() 
            invariant
                (0 < idx <= v.len()),
                (forall|i: int, j: int| 
                    0 <= i && i + 1 < idx && j == i + 1 ==> #[trigger]
                    ckeykvlt(v@[i], v@[j])),
        {
            if v[idx - 1].k.ukey >= v[idx].k.ukey {
                assert(!ckeykvlt(v@[idx as int - 1], v@[idx as int]));
                return false;
            } else {
                idx = idx + 1;
            }
        }
        assert forall|i: int| 0 <= i && i + 1 < v.len() implies #[trigger]
        v@[i].k.ukey < v@[i + 1].k.ukey by {
            assert(ckeykvlt(v@[i], v@[i + 1]));  // OBSERVE
            // reveal(ckeykvlt); // TODO: this should be illegal since ckeykvlt is open
        }
        true
    }
}

// NOTE: This is an arbitrary upper limit, set up because the hashmap axiomatization isn't
// powerful enough to easily otherwise prove marshalability; the `valid_value` function already
// basically guarantees us this (in fact, it guarantees a smaller size than even this), but
// yeah, placing this arbitrary upper limit allows things to go through for the hash table.
#[verifier::opaque]
pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
    0x100000
}

pub fn ckeyhashmap_max_serialized_size_exec() -> (r: usize)
    ensures
        r == ckeyhashmap_max_serialized_size(),
{
    reveal(ckeyhashmap_max_serialized_size);
    0x100000
}

impl Marshalable for CKeyHashMap {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
    }
    
    open spec fn is_marshalable(&self) -> bool {
        self.to_vec().is_marshalable() && crate::hashmap_t::spec_sorted_keys(self.to_vec())
            && self.to_vec().ghost_serialize().len() <= (ckeyhashmap_max_serialized_size() as int)
    }
    
    exec fn _is_marshalable(&self) -> (res: bool)// req, ens from trait
    {
        let v = self.to_vec();
        let a = sorted_keys(&self.to_vec());
        v._is_marshalable() && a && self.to_vec().serialized_size()
            <= ckeyhashmap_max_serialized_size_exec()
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8>// req, ens from trait
     {
        self.to_vec().ghost_serialize()
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        self.to_vec().serialized_size()
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        self.to_vec().serialize(data)
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        match <Vec<CKeyKV>>::deserialize(data, start) {
            None => { None },
            Some((x, end)) => {
                if !sorted_keys(&x)  {
                    None
                } else {
                    let res = CKeyHashMap::from_vec(x);
                    if end - start > ckeyhashmap_max_serialized_size_exec() {
                        None
                    } else {
                        Some((res, end))
                    }
                }
            },
        }
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        self.lemma_to_vec_view(*other);
        assert(self.to_vec()@ != other.to_vec()@);
        if self.to_vec().len() != other.to_vec().len() {
            self.to_vec().lemma_serialization_is_not_a_prefix_of(&other.to_vec());
        } else {
            assert(exists|i: int| 
                #![auto]
                0 <= i < self.spec_to_vec().len() && self.spec_to_vec()[i]@
                    != other.spec_to_vec()[i]@);
            let i = choose|i: int| 
                #![auto]
                0 <= i < self.spec_to_vec().len() && self.spec_to_vec()[i]@
                    != other.spec_to_vec()[i]@;
            assert(self.to_vec()[i]@ != other.to_vec()[i]@);
            assert(!self.to_vec()[i].view_equal(&other.to_vec()[i]));
            assert(!self.to_vec().view_equal(&other.to_vec()));
            self.to_vec().lemma_serialization_is_not_a_prefix_of(&other.to_vec());
        }
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        self.lemma_to_vec_view(*other);
        self.to_vec().lemma_same_views_serialize_the_same(&other.to_vec());
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        if !self.view_equal(other)  {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());  // OBSERVE
        }
    }
}

#[allow(non_snake_case)]
pub proof fn lemma_is_marshalable_CKeyHashMap(h: CKeyHashMap)
    requires
        crate::host_protocol_t::valid_hashtable(h@),
    ensures
        h.is_marshalable(),
{
    lemma_auto_spec_u64_to_from_le_bytes();
    assert(h@.dom().len() < 62);
    h.lemma_to_vec();
    let vec = h.spec_to_vec();
    assert(vec.len() < 62);
    let max_len: int = 10_000;
    assert forall|i: int| 0 <= i < vec.len() implies (#[trigger]
    vec[i].is_marshalable() && vec[i].ghost_serialize().len() < max_len) by {
        let (k, v) = vec[i]@;
        assert(h@.contains_pair(k, v));
        assert(h@.dom().contains(k));
        assert(crate::app_interface_t::valid_key(k));
        assert(crate::app_interface_t::valid_value(h@[k]));
        assert(vec[i].is_marshalable());
        assert(vec[i].ghost_serialize().len() < max_len);
    }
    reveal(crate::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size);
    assert((vec@.len() as usize).ghost_serialize().len() + vec@.fold_left(
        0,
        |acc: int, x: CKeyKV| acc + x.ghost_serialize().len(),
    ) <= 0x100000) by {
        let f = |x: CKeyKV| x.ghost_serialize().len() as int;
        let ag = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len();
        let af = |acc: int, x: CKeyKV| acc + f(x);
        assert forall|i: int| 0 <= i < vec@.len() implies f(vec@[i]) <= max_len by {
            let (k, v) = vec[i]@;
            assert(h@.contains_pair(k, v));
            assert(h@.dom().contains(k));
            assert(crate::app_interface_t::valid_key(k));
            assert(crate::app_interface_t::valid_value(h@[k]));
            assert(vec[i].is_marshalable());
            assert(vec[i].ghost_serialize().len() < max_len);
        }
        lemma_seq_fold_left_sum_le(vec@, 0, max_len, f);
        fun_ext_2(ag, af);
    }
    assert((vec@.len() as usize).ghost_serialize().len() + vec@.fold_left(
        Seq::<u8>::empty(),
        |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize(),
    ).len() <= 0x100000) by {
        let emp = Seq::<u8>::empty();
        let s = |x: CKeyKV| x.ghost_serialize();
        let agl = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len() as int;
        let asl = |acc: int, x: CKeyKV| acc + s(x).len() as int;
        let sg = |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize();
        let sa = |acc: Seq<u8>, x: CKeyKV| acc + s(x);
        lemma_seq_fold_left_append_len_int(vec@, emp, s);
        assert(vec@.fold_left(emp, sa).len() as int == vec@.fold_left(0, asl));
        fun_ext_2(sa, sg);
        assert(vec@.fold_left(emp, sg).len() as int == vec@.fold_left(0, asl));
        fun_ext_2(agl, asl);
        assert(vec@.fold_left(emp, sg).len() == vec@.fold_left(0, agl));
    }
    assert(vec.is_marshalable()) by {
        assert(vec@.len() <= usize::MAX);
        assert(forall|x: CKeyKV| 
            vec@.contains(x) ==> #[trigger]
            x.is_marshalable());
    }
    assert(crate::hashmap_t::spec_sorted_keys(vec));
    assert(h.is_marshalable());
}

/* $line_count$Proof$ */
derive_marshalable_for_enum! {
    /* $line_count$Proof$ */     pub enum CMessage {
    /* $line_count$Proof$ */         #[tag = 0]
    /* $line_count$Proof$ */         GetRequest{ #[o=o0] k: CKey},
    /* $line_count$Proof$ */         #[tag = 1]
    /* $line_count$Proof$ */         SetRequest{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec<u8>>},
    /* $line_count$Proof$ */         #[tag = 2]
    /* $line_count$Proof$ */         Reply{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec::<u8>> },
    /* $line_count$Proof$ */         #[tag = 3]
    /* $line_count$Proof$ */         Redirect{ #[o=o0] k: CKey, #[o=o1] id: EndPoint },
    /* $line_count$Proof$ */         #[tag = 4]
    /* $line_count$Proof$ */         Shard{ #[o=o0] kr: KeyRange::<CKey>, #[o=o1] recipient: EndPoint },
    /* $line_count$Proof$ */         #[tag = 5]
    /* $line_count$Proof$ */         Delegate{ #[o=o0] range: KeyRange::<CKey>, #[o=o1] h: CKeyHashMap},
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */     [rlimit attr = verifier::rlimit(20)]
    /* $line_count$Proof$ */ }

} // verus!

}

mod marshal_v{
//! Translates file Distributed/Impl/Common/GenericMarshalling.i.dfy
//!
//! Not really a translation so much as a re-implementation
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::function::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::slice::*;

use crate::verus_extra::choose_v::*;
use crate::verus_extra::clone_v::VerusClone;
use crate::verus_extra::seq_lib_v;
use crate::verus_extra::seq_lib_v::*;

// FIXME:
//
// + [2023-02-10] `&[u8]` doesn't have a usable `.len()` in pervasive(??), so we end up using
//   `Vec<u8>` instead, which is not necessarily ideal for performance.
//
// + [2023-02-10] "expected struct `builtin::int`, found struct `builtin::nat`" annoying and
//   requires `as int` annotations; maybe this should be something that Verus automatically infers?
//
// + [2023-02-10] Verus doesn't have a higher performance Vec constructor; need to do repeated
//   pushes right now.
//
// + [2023-03-31] There is no convenient support for overflow/underflow checking (for example,
//   `checked_add`), would be nice to have them.

verus! {

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;
    
    exec fn _is_marshalable(&self) -> (res: bool)
        ensures
            res == self.is_marshalable(),
    ;
    
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    ;
    
    exec fn serialized_size(&self) -> (res: usize)
        requires
            self.is_marshalable(),
        ensures
            res as int == self.ghost_serialize().len(),
    ;
    
    exec fn serialize(&self, data: &mut Vec<u8>)
        requires
            self.is_marshalable(),
        ensures
            data@.len() >= old(data).len(),
            data@.subrange(0, old(data)@.len() as int) == old(data)@,
            data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize(),
    ;
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
        ensures
            match res {
                Some((x, end)) => {
                    &&& x.is_marshalable()
                    &&& start <= end <= data.len()
                    &&& data@.subrange(start as int, end as int) == x.ghost_serialize()
                },
                None => true,
            },
    ;
    
    // since Verus doesn't have a trait for `View` or such yet, also defining as a separate trait
    // doesn't work, because Verus doesn't support trait generic bounds, we place `view_equal` within
    // this trait itself.
    spec fn view_equal(&self, other: &Self) -> bool;
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)
        ensures
            self.view_equal(other) == other.view_equal(self),
    ;
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
        requires
            !self.view_equal(other),
            self.ghost_serialize().len() <= other.ghost_serialize().len(),
        ensures
            self.ghost_serialize() != other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ),
    ;
    
    proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
        requires
            self.view_equal(other),
        ensures
            self.is_marshalable() == other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
    ;
    
    proof fn lemma_serialize_injective(&self, other: &Self)
        requires
            self.is_marshalable(),
            other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
        ensures
            self.view_equal(other),
    ;
}

#[allow(unused)]
macro_rules! ext_equalities_aux {
  ($s:expr $(,)?) => {};
  ($s1:expr, $s2:expr, $($rest:expr,)* $(,)?) => {verus_proof_expr!{{
    assert($s1 =~= $s2);
    ext_equalities_aux!($s2, $($rest,)*);
  }}};
}

#[allow(unused)]
macro_rules! ext_equalities {
  ($($tt:tt)*) => {
    verus_proof_macro_exprs!(ext_equalities_aux!($($tt)*))
  };
}

impl Marshalable for u64 {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
    }
    
    open spec fn is_marshalable(&self) -> bool {
        true
    }
    
    exec fn _is_marshalable(&self) -> (res: bool)// req, ens from trait
    {
        true
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        8
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        let s = u64_to_le_bytes(*self);
        let mut i: usize = 0;
        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.ghost_serialize().subrange(0, i as int));
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        while i < 8 
            invariant
                0 <= i <= 8,
                s.len() == 8,
                s@ == self.ghost_serialize(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i as int),
                data@.len() == old(data)@.len() + i as int,
        {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) == data@.subrange(
                old(data)@.len() as int,
                old(data)@.len() + i as int,
            ));
            let x: u8 = s[i];
            data.push(x);
            i = i + 1;
            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i as int)) by {
                    assert(self.ghost_serialize().subrange(0, (i - 1) as int).push(x)
                        =~= self.ghost_serialize().subrange(0, i as int));
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize().subrange(0, (i - 1) as int).push(x));
                }
            }
        }
        proof {
            assert(self.ghost_serialize().subrange(0, i as int) =~= self.ghost_serialize());
        }
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        if data.len() < 8 {
            return None;
        }
        if start > data.len() - 8 {
            return None;
        }
        let end = start + 8;
        let v = u64_from_le_bytes(slice_subrange(data.as_slice(), start, end));
        Some((v, end))
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
            =~= other.ghost_serialize());
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
    }
}

impl Marshalable for usize {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
    }
    
    open spec fn is_marshalable(&self) -> bool {
        &&& *self as int <= u64::MAX
    }
    
    exec fn _is_marshalable(&self) -> (res: bool)// req, ens from trait
    {
        *self as u64 <= u64::MAX
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        (*self as u64).serialized_size()
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        (*self as u64).serialize(data)
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        let (r, end) = match u64::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        if r <= usize::MAX as u64 {
            let res = r as usize;
            // assert(res.0 as int <= u64::MAX);
            // assert(r.0 as int <= u64::MAX);
            // assert(res.0 as int <= usize::MAX);
            // assert(r.0 as int <= usize::MAX);
            // assert(res.0 as int == r.0 as int);
            Some((res, end))
        } else {
            None
        }
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        (*self as u64).lemma_serialization_is_not_a_prefix_of(&(*other as u64));
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        (*self as u64).lemma_same_views_serialize_the_same(&(*other as u64));
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        (*self as u64).lemma_serialize_injective(&(*other as u64));
    }
}

impl Marshalable for Vec<u8> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
    }
    
    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }
    
    exec fn _is_marshalable(&self) -> (res: bool)// req, ens from trait
    {
        self.len() <= usize::MAX && self.len().serialized_size() <= usize::MAX - self.len()
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        self.len().serialized_size() + self.len()
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        let self_len = self.len();
        self_len.serialize(data);
        let init: Ghost<int> = Ghost(self_len.ghost_serialize().len() as int);
        let mut i: usize = 0;
        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.ghost_serialize().subrange(0, i + init@));
        }
        while i < self.len() 
            invariant
                0 <= i <= self.len(),
                self.is_marshalable(),
                self.ghost_serialize().len() == init@ + self.len(),
                0 <= i + init@ <= self.ghost_serialize().len(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i + init@),
                data@.len() == old(data)@.len() + i + init@,
        {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) == data@.subrange(
                old(data)@.len() as int,
                old(data)@.len() + i + init@,
            ));
            let x: u8 = self[i];
            data.push(x);
            i = i + 1;
            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.ghost_serialize().subrange(0, i + init@)) by {
                    assert(self.ghost_serialize().subrange(0, (i + init@ - 1) as int).push(x)
                        =~= self.ghost_serialize().subrange(0, i + init@));
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize().subrange(0, (i + init@ - 1) as int).push(x));
                }
            }
        }
        proof {
            assert(self.ghost_serialize().subrange(0, i + init@) =~= self.ghost_serialize());
        }
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        let (len, mid) = match usize::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let len = len as usize;
        // assert(mid <= data.len());
        // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());
        let end = if usize::MAX - mid >= len {
            mid + len
        } else {
            return None;
        };
        if end > data.len() {
            return None;
        }// assert(0 <= mid);
        // assert(len >= 0);
        // assert(mid <= end);
        // assert(end <= data.len());
        
        let res_slice = slice_subrange(data.as_slice(), mid, end);
        let res = slice_to_vec(res_slice);
        // assert(res_slice@ == data@.subrange(mid as int, end as int));
        // assert(res@ == res_slice@);
        // assert(res.ghost_serialize() == usize(len).ghost_serialize() + res@);
        // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());
        // assert(data@.subrange(mid as int, end as int) == res@);
        // assert(0 <= start);
        // assert(start <= mid);
        // assert(mid <= end);
        // assert(end <= data.len());
        proof {
            // For performance reasons, we need to split this into a lemma.
            // Weirdly, if we inline the lemma, the proof fails.
            //
            // This is especially weird because the lemma just has a call to the `assert_seqs_equal!`
            // macro. which itself is supposed to do things via `assert by` which should not cause a
            // blow-up in the solver time.
            seq_lib_v::lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
        }
        Some((res, end))
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self.ghost_serialize().subrange(0, 8) =~= (self@.len() as usize).ghost_serialize());
        assert(other.ghost_serialize().subrange(0, 8) =~= (
        other@.len() as usize).ghost_serialize());
        if self.ghost_serialize().len() == other.ghost_serialize().len() {
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());
            assert(self.ghost_serialize().subrange(8, self.ghost_serialize().len() as int)
                =~= self@);
            assert(other.ghost_serialize().subrange(8, self.ghost_serialize().len() as int)
                =~= other@);
        } else {
            assert(other.len() > self.len());  // OBSERVE
            assert(other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
        }
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self@ =~= self.ghost_serialize().subrange(
            (self@.len() as usize).ghost_serialize().len() as int,
            self.ghost_serialize().len() as int,
        ));
        assert(other@ =~= other.ghost_serialize().subrange(
            (other@.len() as usize).ghost_serialize().len() as int,
            other.ghost_serialize().len() as int,
        ));
    }
}

impl<T: Marshalable> Marshalable for Option<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(s), Some(o)) => s.view_equal(o),
            _ => false,
        }
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
        match (self, other) {
            (None, None) => (),
            (Some(s), Some(o)) => s.lemma_view_equal_symmetric(o),
            _ => (),
        }
    }
    
    open spec fn is_marshalable(&self) -> bool {
        match self {
            None => true,
            Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
        }
    }
    
    exec fn _is_marshalable(&self) -> (res: bool)// req, ens from trait
    {
        match self {
            None => true,
            Some(x) => x._is_marshalable() && x.serialized_size() <= usize::MAX - 1,
        }
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8>// req, ens from trait
     {
        match self {
            None => seq![0],
            Some(x) => seq![1] + x.ghost_serialize(),
        }
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        match self {
            None => 1,
            Some(x) => 1 + x.serialized_size(),
        }
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        match self {
            None => {
                data.push(0);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize());
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
            },
            Some(x) => {
                data.push(1);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![1]);
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
                x.serialize(data);
                proof {
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.ghost_serialize());
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
            },
        }
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        if data.len() == 0 || start > data.len() - 1 {
            return None;
        }
        let tag = data[start];
        let (x, end) = if tag == 0 {
            let mid = start + 1;
            (None, mid)
        } else if tag == 1 {
            let mid = start + 1;
            let (x, mid) = match T::deserialize(data, mid) {
                None => {
                    return None;
                },
                Some(x) => x,
            };
            (Some(x), mid)
        } else {
            return None;
        };
        proof {
            assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());
        }
        Some((x, end))
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        match (self, other) {
            (None, None) => {},
            (Some(_), None) | (None, Some(_)) => {
                assert(self.ghost_serialize()[0] != other.ghost_serialize()[0]);  // OBSERVE
            },
            (Some(s), Some(o)) => {
                s.lemma_serialization_is_not_a_prefix_of(o);
                assert(s.ghost_serialize() =~= self.ghost_serialize().subrange(
                    1,
                    self.ghost_serialize().len() as int,
                ));
                assert(o.ghost_serialize().subrange(0, s.ghost_serialize().len() as int)
                    =~= other.ghost_serialize().subrange(
                    0,
                    self.ghost_serialize().len() as int,
                ).subrange(1, self.ghost_serialize().len() as int));
            },
        }
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        match (self, other) {
            (Some(s), Some(o)) => s.lemma_same_views_serialize_the_same(o),
            _ => (),
        }
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        match (self, other) {
            (Some(s), Some(o)) => {
                assert(s.ghost_serialize() =~= self.ghost_serialize().subrange(
                    1,
                    self.ghost_serialize().len() as int,
                ));
                assert(o.ghost_serialize() =~= other.ghost_serialize().subrange(
                    1,
                    other.ghost_serialize().len() as int,
                ));
                s.lemma_serialize_injective(o);
            },
            (None, None) => {},
            (Some(s), None) => {
                assert(other.ghost_serialize()[0] == 0);  // OBSERVE
            },
            (None, Some(o)) => {
                assert(self.ghost_serialize()[0] == 0);  // OBSERVE
            },
        }
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        let s = self@;
        let o = other@;
        s.len() == o.len() && (forall|i: int| 
            0 <= i < s.len() ==> #[trigger]
            s[i].view_equal(&o[i]))
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
        let s = self@;
        let o = other@;
        if self.view_equal(other) {
            assert forall|i: int| 0 <= i < o.len() implies #[trigger]
            o[i].view_equal(&s[i]) by {
                s[i].lemma_view_equal_symmetric(&o[i]);
            }
        } else {
            if s.len() != o.len() {
                // trivial
            } else {
                let i = choose|i: int| 
                    0 <= i < s.len() && !#[trigger]
                    s[i].view_equal(&o[i]);
                s[i].lemma_view_equal_symmetric(&o[i]);
            }
        }
    }
    
    open spec fn is_marshalable(&self) -> bool {
        &&& self@.len() <= usize::MAX
        &&& (forall|x: T| 
            self@.contains(x) ==> #[trigger]
            x.is_marshalable())
        &&& (self@.len() as usize).ghost_serialize().len() + self@.fold_left(
            0,
            |acc: int, x: T| acc + x.ghost_serialize().len(),
        ) <= usize::MAX
    }
    
    exec fn _is_marshalable(&self) -> bool {
        let mut res = true;
        let mut i = 0;
        let mut total_len = self.len().serialized_size();
        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }
        while res && i < self.len() 
            invariant
                0 <= i <= self.len(),
                res ==> total_len as int == (self@.len() as usize).ghost_serialize().len()
                    + self@.subrange(0, i as int).fold_left(
                    0,
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                ),
                res ==> (forall|x: T| 
                    self@.subrange(0, i as int).contains(x) ==> #[trigger]
                    x.is_marshalable()),
                res ==> total_len as int <= usize::MAX,
                !res ==> !self.is_marshalable(),
        {
            assert(res);
            res =
            res && self[i]._is_marshalable() && (usize::MAX - total_len
                >= self[i].serialized_size());
            if res {
                let old_total_len = total_len;
                total_len = total_len + self[i].serialized_size();
                i = i + 1;
                proof {
                    assert forall|x: T| 
                        #[trigger]
                        self@.subrange(0, i as int).contains(x) implies x.is_marshalable() by {
                        if (exists|j: int| 
                            0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(
                                0,
                                i as int,
                            )[j] == x) {
                            let j = choose|j: int| 
                                0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(
                                    0,
                                    i as int,
                                )[j] == x;
                            assert(self@.subrange(0, i as int - 1)[j] == x);  // OBSERVE
                        }
                    };
                    let sl = |x: T| x.ghost_serialize().len() as int;
                    fun_ext_2::<int, T, int>(
                        |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                        |acc: int, x: T| acc + sl(x),
                    );
                    let s = self@.subrange(0 as int, i as int);
                    seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                    assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i - 1 as int));
                }
            } else {
                proof {
                    if usize::MAX < total_len + self@[i as int].ghost_serialize().len() {
                        assert(((self@.len() as usize).ghost_serialize().len() + self@.fold_left(
                            0,
                            |acc: int, x: T| acc + x.ghost_serialize().len(),
                        )) >= (total_len + self@[i as int].ghost_serialize().len())) by {
                            let f = |x: T| x.ghost_serialize();
                            let sl = |x: T| x.ghost_serialize().len() as int;
                            let s = self@.subrange(0 as int, i as int + 1);
                            fun_ext_2::<int, T, int>(
                                |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                                |acc: int, x: T| acc + sl(x),
                            );
                            seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                            assert(s.subrange(0, s.len() - 1) =~= self@.subrange(
                                0 as int,
                                i as int,
                            ));
                            seq_lib_v::lemma_seq_fold_left_append_len_int_le(
                                self@,
                                i as int + 1,
                                0,
                                f,
                            );
                            fun_ext_2(
                                |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                                |acc: int, x: T| acc + f(x).len(),
                            );
                        };
                    } else {
                        assert(!self@[i as int].is_marshalable());
                    }
                }
            }
        }
        res
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@.fold_left(
            Seq::<u8>::empty(),
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        )
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        let mut res = self.len().serialized_size();
        let mut i = 0;
        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }
        while i < self.len() 
            invariant
                0 <= i <= self.len(),
                (forall|x: T| 
                    self@.contains(x) ==> #[trigger]
                    x.is_marshalable()),
                (self@.len() as usize).ghost_serialize().len() + self@.subrange(
                    0 as int,
                    self@.len() as int,
                ).fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) <= usize::MAX,
                res == (self@.len() as usize).ghost_serialize().len() + self@.subrange(
                    0 as int,
                    i as int,
                ).fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()),
        {
            proof {
                let f = |x: T| x.ghost_serialize();
                fun_ext_2::<int, T, int>(
                    |acc: int, x: T| acc + f(x).len(),
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                );
                seq_lib_v::lemma_seq_fold_left_append_len_int_le::<T, u8>(
                    self@,
                    i + 1 as int,
                    0,
                    f,
                );
                let sl = |x: T| x.ghost_serialize().len() as int;
                let accl = |acc: int, x: T| acc + x.ghost_serialize().len() as int;
                fun_ext_2::<int, T, int>(accl, |acc: int, x: T| acc + sl(x));
                let s = self@.subrange(0 as int, i + 1 as int);
                seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                assert(s.subrange(0, s.len() - 1 as int) =~= self@.subrange(0 as int, i as int));
                assert(self@.subrange(0 as int, self@.len() as int) =~= self@);
            }
            let old_res: Ghost<usize> = Ghost(res);
            res = res + self[i].serialized_size();
            i = i + 1;
            proof {
                let sl = |x: T| x.ghost_serialize().len() as int;
                fun_ext_2::<int, T, int>(
                    |acc: int, x: T| acc + x.ghost_serialize().len() as int,
                    |acc: int, x: T| acc + sl(x),
                );
                let s = self@.subrange(0 as int, i as int);
                seq_lib_v::lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
                assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i - 1 as int));
            }
        }
        proof {
            let f = |x: T| x.ghost_serialize();
            seq_lib_v::lemma_seq_fold_left_append_len_int::<T, u8>(self@, Seq::<u8>::empty(), f);
            fun_ext_2::<Seq<u8>, T, Seq<u8>>(
                |acc: Seq<u8>, x: T| acc + f(x),
                |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
            );
            fun_ext_2::<int, T, int>(
                |acc: int, x: T| acc + f(x).len(),
                |acc: int, x: T| acc + x.ghost_serialize().len(),
            );
            assert(self@.subrange(0 as int, i as int) =~= self@);
        }
        res
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        let self_len = self.len();
        self_len.serialize(data);
        let init: Ghost<int> = Ghost(self_len.ghost_serialize().len() as int);
        let mut i: usize = 0;
        proof {
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                Seq::<u8>::empty(),
                |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
            ));
        }
        while i < self.len() 
            invariant
                i <= self.len(),
                data@.subrange(0, old(data)@.len() as int) == old(data)@,
                data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                    Seq::<u8>::empty(),
                    |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
                ),
                forall|x: T| 
                    self@.contains(x) ==> #[trigger]
                    x.is_marshalable(),
                data@.len() >= old(data)@.len(),
        {
            self[i].serialize(data);
            i = i + 1;
            proof {
                assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                    == self.len().ghost_serialize() + self@.subrange(0, i as int).fold_left(
                    Seq::<u8>::empty(),
                    |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
                )) by {
                    let s = self@;
                    let emp = Seq::<u8>::empty();
                    let accf = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
                    let f = |x: T| x.ghost_serialize();
                    let t = s.subrange(0, i as int);
                    fun_ext_2(accf, |acc: Seq<u8>, x: T| acc + f(x));
                    assert(t.subrange(0, t.len() - 1) =~= s.subrange(0, i - 1));
                    seq_lib_v::lemma_seq_fold_left_append_right(t, emp, f);
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.len().ghost_serialize() + s.subrange(0, (i - 1) as int).fold_left(
                        emp,
                        accf,
                    ) + s.index((i - 1) as int).ghost_serialize());
                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                        =~= self.len().ghost_serialize() + t.fold_left(emp, accf));
                }
            }
        }
        proof {
            assert(self@ =~= self@.subrange(0, self@.len() as int));
        }
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        let (len, mid) = match usize::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let len = len as usize;
        let mut res: Vec<T> = Vec::with_capacity(len);
        let mut i: usize = 0;
        let mut end = mid;
        let emp: Ghost<Seq<u8>> = Ghost(Seq::<u8>::empty());
        let accf: Ghost<FnSpec(Seq<u8>, T) -> Seq<u8>> = Ghost(
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        );
        proof {
            assert(data@.subrange(mid as int, end as int) =~= emp@);
            // assert(emp == seq_lib_v::seq_fold_left(res@, emp@, accf@));
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        while i < len 
            invariant
                0 <= i <= len,
                res.is_marshalable(),
                start <= mid <= end <= data@.len(),
                data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@),
                res@.len() == i,
                len.ghost_serialize().len() + res@.fold_left(
                    0,
                    |acc: int, x: T| acc + x.ghost_serialize().len(),
                ) == end - start,
                accf@ == |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        {
            let (x, end1) = match T::deserialize(data, end) {
                None => {
                    return None;
                },
                Some(x) => x,
            };
            let old_end: Ghost<int> = Ghost(end as int);
            let old_res: Ghost<Seq<T>> = Ghost(res@);
            res.push(x);
            end = end1;
            i = i + 1;
            assert(data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@)) by {
                let f = |x: T| x.ghost_serialize();
                // assert(data@.subrange(mid as int, old_end@) == seq_lib_v::seq_fold_left(old_res@, emp@, accf@));
                seq_lib_v::lemma_seq_add_subrange::<u8>(data@, mid as int, old_end@, end as int);
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + data@.subrange(old_end@, end as int));
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + x.ghost_serialize());
                // assert(f(x) == x.ghost_serialize());
                // assert(data@.subrange(mid as int, end as int) ==
                //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + f(x));
                seq_lib_v::lemma_seq_fold_left_append_right(res@, emp@, f);
                assert(accf@ == (|acc: Seq<u8>, x: T| acc + f(x))) by {
                    fun_ext_2(accf@, |acc: Seq<u8>, x: T| acc + f(x));
                }
                assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
                // assert(data@.subrange(mid as int, end as int) == seq_lib_v::seq_fold_left(res@, emp@, accf@));
            }
            assert(len.ghost_serialize().len() + res@.fold_left(
                0,
                |acc: int, x: T| acc + x.ghost_serialize().len(),
            ) == end - start) by {
                let l = |x: T| x.ghost_serialize().len() as int;
                let suml = |acc: int, x: T| acc + l(x);
                seq_lib_v::lemma_seq_fold_left_sum_right(res@, 0, l);
                fun_ext_2(|acc: int, x: T| acc + x.ghost_serialize().len(), suml);
                assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
            }
            assert(len.ghost_serialize().len() == (res@.len() as usize).ghost_serialize().len())
                by {
                lemma_auto_spec_u64_to_from_le_bytes();
            }
        }
        assert(data@.subrange(start as int, end as int) == res.ghost_serialize()) by {
            seq_lib_v::lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
        }
        Some((res, end))
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        if self.len() != other.len() {
            assert(other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
            assert(self.ghost_serialize().subrange(0, 8) =~= (
            self.len() as usize).ghost_serialize());
            assert(other.ghost_serialize().subrange(0, 8) =~= (
            other.len() as usize).ghost_serialize());
        } else {
            let not_view_equal_at_idx = |i: int| !self@[i].view_equal(&other@[i]);
            let idx = {
                let temp = choose|i: int| 
                    0 <= i < self@.len() && !#[trigger]
                    self@[i].view_equal(&other@[i]);
                assert(not_view_equal_at_idx(temp));  // OBSERVE
                choose_smallest(0, self@.len() as int, not_view_equal_at_idx)
            };
            let emp = Seq::<u8>::empty();
            let g = |x: T| x.ghost_serialize();
            let accg = |acc: Seq<u8>, x: T| acc + g(x);
            let accgs = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
            let gs = |s: Seq<T>, start: int, end: int| s.subrange(start, end).fold_left(emp, accg);
            fun_ext_2(accg, accgs);
            assert(self.ghost_serialize() =~= ((self@.len() as usize).ghost_serialize() + gs(
                self@,
                0,
                idx,
            )) + g(self@[idx]) + gs(self@, idx + 1, self.len() as int)) by {
                assert(gs(self@, 0, self.len() as int) == gs(self@, 0, idx) + gs(
                    self@,
                    idx,
                    self.len() as int,
                )) by {
                    let s1 = self@.subrange(0, idx);
                    let s2 = self@.subrange(idx, self.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(self@.subrange(0, self.len() as int) =~= s1 + s2);
                }
                assert(gs(self@, idx, self.len() as int) == g(self@[idx]) + gs(
                    self@,
                    idx + 1,
                    self.len() as int,
                )) by {
                    let s1 = self@.subrange(idx, idx + 1);
                    let s2 = self@.subrange(idx + 1, self.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(self@.subrange(idx, self.len() as int) =~= s1 + s2);
                    assert(self@.subrange(idx, idx + 1) =~= seq![self@[idx]]);
                    reveal_with_fuel(Seq::fold_left, 2);
                    assert(emp + g(self@[idx]) =~= g(self@[idx]));
                }
                assert((self@.len() as usize).ghost_serialize() + gs(self@, 0, self.len() as int)
                    == self.ghost_serialize()) by {
                    assert(self@.subrange(0, self.len() as int) =~= self@);
                }
            }
            assert(other.ghost_serialize() =~= ((other@.len() as usize).ghost_serialize() + gs(
                other@,
                0,
                idx,
            )) + g(other@[idx]) + gs(other@, idx + 1, other.len() as int)) by {
                assert(gs(other@, 0, other.len() as int) == gs(other@, 0, idx) + gs(
                    other@,
                    idx,
                    other.len() as int,
                )) by {
                    let s1 = other@.subrange(0, idx);
                    let s2 = other@.subrange(idx, other.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(other@.subrange(0, other.len() as int) =~= s1 + s2);
                }
                assert(gs(other@, idx, other.len() as int) == g(other@[idx]) + gs(
                    other@,
                    idx + 1,
                    other.len() as int,
                )) by {
                    let s1 = other@.subrange(idx, idx + 1);
                    let s2 = other@.subrange(idx + 1, other.len() as int);
                    lemma_fold_left_append_merge(s1, s2, g);
                    assert(other@.subrange(idx, other.len() as int) =~= s1 + s2);
                    assert(other@.subrange(idx, idx + 1) =~= seq![other@[idx]]);
                    reveal_with_fuel(Seq::fold_left, 2);
                    assert(emp + g(other@[idx]) =~= g(other@[idx]));
                }
                assert((other@.len() as usize).ghost_serialize() + gs(other@, 0, other.len() as int)
                    == other.ghost_serialize()) by {
                    assert(other@.subrange(0, other.len() as int) =~= other@);
                }
            }
            assert((self@.len() as usize).ghost_serialize() == (
            other@.len() as usize).ghost_serialize());
            assert(gs(self@, 0, idx) == gs(other@, 0, idx)) by {
                assert forall|i: int| 0 <= i < idx implies g(self@.subrange(0, idx)[i]) == g(
                    other@.subrange(0, idx)[i],
                ) by {
                    assert(self@.subrange(0, idx)[i] == self@[i] && other@.subrange(0, idx)[i]
                        == other@[i]);
                    assert(!not_view_equal_at_idx(i));
                    self@[i].lemma_same_views_serialize_the_same(&other@[i]);
                }
                lemma_fold_left_on_equiv_seqs(
                    self@.subrange(0, idx),
                    other@.subrange(0, idx),
                    |x: T, y: T| g(x) == g(y),
                    emp,
                    accg,
                );
            }
            assert(((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)) == ((
            other@.len() as usize).ghost_serialize() + gs(other@, 0, idx)));
            let prefix_len = ((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)).len();
            let i = if g(self@[idx]).len() <= g(other@[idx]).len() {
                self@[idx].lemma_serialization_is_not_a_prefix_of(&other@[idx]);
                some_differing_index_for_unequal_seqs(
                    g(self@[idx]),
                    g(other@[idx]).subrange(0, g(self@[idx]).len() as int),
                )
            } else {
                self@[idx].lemma_view_equal_symmetric(&other@[idx]);
                other@[idx].lemma_serialization_is_not_a_prefix_of(&self@[idx]);
                some_differing_index_for_unequal_seqs(
                    g(other@[idx]),
                    g(self@[idx]).subrange(0, g(other@[idx]).len() as int),
                )
            };
            assert(g(self@[idx])[i] != g(other@[idx])[i]);
            assert(self.ghost_serialize()[prefix_len + i] != other.ghost_serialize()[prefix_len
                + i]);
            assert(self.ghost_serialize() != other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            ));
        }
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(self@.len() == other@.len());
        assert forall|i: int| 0 <= i < self@.len() implies #[trigger]
        self@[i].is_marshalable() == other@[i].is_marshalable() && #[trigger]
        self@[i].ghost_serialize() == other@[i].ghost_serialize() by {
            self@[i].lemma_same_views_serialize_the_same(&other@[i]);
        }
        let veq = |x: T, y: T| x.view_equal(&y);
        assert(self.is_marshalable() == other.is_marshalable()) by {
            assert((self@.len() <= usize::MAX) == (other@.len() <= usize::MAX));
            if (forall|x: T| 
                self@.contains(x) ==> #[trigger]
                x.is_marshalable()) {
                assert forall|y: T| other@.contains(y) implies #[trigger]
                y.is_marshalable() by {
                    let i = choose|i: int| 0 <= i < other@.len() && other@[i] == y;
                    self@[i].lemma_same_views_serialize_the_same(&other@[i]);
                }
            } else {
                let i = choose|i: int| 
                    0 <= i < self@.len() && !(#[trigger]
                    self@[i].is_marshalable());
                self@[i].lemma_same_views_serialize_the_same(&other@[i]);
            }
            assert((self@.len() as usize).ghost_serialize().len() == (
            other@.len() as usize).ghost_serialize().len());
            let f = |acc: int, x: T| acc + x.ghost_serialize().len();
            assert forall|b: int, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger]
            f(b, a1) == f(b, a2) by {
                a1.lemma_same_views_serialize_the_same(&a2);
            }
            seq_lib_v::lemma_fold_left_on_equiv_seqs(self@, other@, veq, 0, f);
            assert(self@.fold_left(0, f) == other@.fold_left(0, f));
        };
        assert(self.ghost_serialize() == other.ghost_serialize()) by {
            let f = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
            assert forall|b: Seq<u8>, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger]
            f(b, a1) == f(b, a2) by {
                a1.lemma_same_views_serialize_the_same(&a2);
            }
            seq_lib_v::lemma_fold_left_on_equiv_seqs(self@, other@, veq, Seq::<u8>::empty(), f);
        }
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self)// req, ens from trait
    {
        if !self.view_equal(other)  {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());  // OBSERVE
        }
    }
}

// NOTE: This can be replaced with a `define_struct_and_derive_marshalable` invocation
impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self.0.view_equal(&other.0) && self.1.view_equal(&other.1)
    }
    
    proof fn lemma_view_equal_symmetric(&self, other: &Self)// req, ens from trait
    {
        self.0.lemma_view_equal_symmetric(&other.0);
        self.1.lemma_view_equal_symmetric(&other.1);
    }
    
    open spec fn is_marshalable(&self) -> bool {
        &&& self.0.is_marshalable()
        &&& self.1.is_marshalable()
        &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
    }
    
    exec fn _is_marshalable(&self) -> bool// req, ens from trait
     {
        self.0._is_marshalable() && self.1._is_marshalable() && self.0.serialized_size()
            <= usize::MAX - self.1.serialized_size()
    }
    
    open spec fn ghost_serialize(&self) -> Seq<u8> {
        self.0.ghost_serialize() + self.1.ghost_serialize()
    }
    
    exec fn serialized_size(&self) -> (res: usize)// req, ens from trait
    {
        self.0.serialized_size() + self.1.serialized_size()
    }
    
    exec fn serialize(&self, data: &mut Vec<u8>)// req, ens from trait
    {
        self.0.serialize(data);
        // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);
        let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
        self.1.serialize(data);
        proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= data@.subrange(
                0,
                mid_data_len@,
            ).subrange(0, old(data)@.len() as int));
            // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);
            assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= data@.subrange(
                0,
                mid_data_len@,
            ).subrange(old(data)@.len() as int, mid_data_len@));
            // assert(data@.subrange(old(data)@.len() as int, mid_data_len@) == self.0.ghost_serialize());
            // assert(data@.subrange(mid_data_len@, data@.len() as int) == self.1.ghost_serialize());
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int)
                =~= self.0.ghost_serialize() + self.1.ghost_serialize());
        }
    }
    
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<
        (Self, usize),
    >)// req, ens from trait
    {
        let (t, mid) = match T::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let (u, end) = match U::deserialize(data, mid) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let p = (t, u);
        proof {
            assert(data@.subrange(start as int, end as int) =~= p.ghost_serialize());
        }
        Some((p, end))
    }
    
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)// req, ens from trait
    {
        let si = self.ghost_serialize();
        let so = other.ghost_serialize();
        let mid: int = 0;
        if !self.0.view_equal(&other.0)  {
            let (x0, x1) = (self.0, other.0);
            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
            x0.lemma_view_equal_symmetric(&x1);
            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
            } else {
                (x1, x0, s1, s0)
            };
            x0.lemma_serialization_is_not_a_prefix_of(&x1);
            assert(!(s0 =~= s1.subrange(0, s0.len() as int)));  // OBSERVE
            let idx = choose|i: int| 0 <= i < s0.len() as int && s0[i] != s1[i];
            if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]);  // OBSERVE
            }
            return ;
        } else {
            self.0.lemma_same_views_serialize_the_same(&other.0);
        }
        let mid = mid + self.0.ghost_serialize().len();
        if !self.1.view_equal(&other.1)  {
            let (x0, x1) = (self.1, other.1);
            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
            x0.lemma_view_equal_symmetric(&x1);
            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
            } else {
                (x1, x0, s1, s0)
            };
            x0.lemma_serialization_is_not_a_prefix_of(&x1);
            assert(!(s0 =~= s1.subrange(0, s0.len() as int)));  // OBSERVE
            let idx = choose|i: int| 0 <= i < s0.len() as int && s0[i] != s1[i];
            if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]);  // OBSERVE
            }
            return ;
        } else {
            self.1.lemma_same_views_serialize_the_same(&other.1);
        }
    }
    
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)// req, ens from trait
    {
        self.0.lemma_same_views_serialize_the_same(&other.0);
        self.1.lemma_same_views_serialize_the_same(&other.1);
    }
    
    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        if !self.view_equal(other)  {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                =~= other.ghost_serialize());  // OBSERVE
        }
    }
}

/// A convenience macro to produce the triangle necessary to confirm that there are no overflows
/// that occur when adding up a bunch of different expressions together.
#[allow(unused_macros)]
macro_rules! no_usize_overflows {
  ($e:expr,) => {
    true
  };
  ($($e:expr),*) => {
    no_usize_overflows!(@@internal 0, $($e),*)
  };
  (@@internal $total:expr,) => {
    true
  };
  (@@internal $total:expr, $a:expr) => {
    usize::MAX - $total >= $a
  };
  (@@internal $total:expr, $a:expr, $($rest:expr),*) => {
    usize::MAX - $total >= $a
      &&
    no_usize_overflows!(@@internal ($total + $a), $($rest),*)
  };
}

pub(crate) use no_usize_overflows;

/// `derive_marshalable_for_struct` is a macro that implements [`Marshalable`] for a struct. You
/// probably want to use [`define_struct_and_derive_marshalable`] wherever possible instead, since
/// it prevents code duplication. However, if you are (for some reason) unable to define at the
/// struct definition site, then this macro lets you derive the macro by simply (textually)
/// copy-pasting the struct.
#[allow(unused_macros)]
macro_rules! derive_marshalable_for_struct {
  {
    $( #[$attr:meta] )*
    $pub:vis
    struct $newstruct:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        $fieldvis:vis $field:ident : $fieldty:ty
      ),+
      $(,)?
    }
  } => {
    ::builtin_macros::verus! {
      impl $(< $($poly: Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? {
        open spec fn view_equal(&self, other: &Self) -> bool {
          $(
            &&& self.$field.view_equal(&other.$field)
          )*
        }
        proof fn lemma_view_equal_symmetric(&self, other: &Self)
        // req, ens from trait
        {
          $(
            self.$field.lemma_view_equal_symmetric(&other.$field);
          )*
        }
        open spec fn is_marshalable(&self) -> bool {
          $(
            &&& self.$field.is_marshalable()
          )*
          &&& 0 $(+ self.$field.ghost_serialize().len())* <= usize::MAX
        }
        exec fn _is_marshalable(&self) -> bool
          // req, ens from trait
        {
          $(
            &&& self.$field._is_marshalable()
          )*
          &&& no_usize_overflows!($((self.$field.serialized_size())),*)
        }
        open spec fn ghost_serialize(&self) -> Seq<u8> {
          Seq::empty() $(+ self.$field.ghost_serialize())*
        }
        exec fn serialized_size(&self) -> (res: usize)
          // req, ens from trait
        {
          0 $(+ self.$field.serialized_size())*
        }
        exec fn serialize(&self, data: &mut Vec<u8>)
          // req, ens from trait
        {
          $(self.$field.serialize(data);)*
          proof {
            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());
          }
        }
        exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
          // req, ens from trait
        {
          let mid = start;
          $(
            let ($field, mid) = match $fieldty::deserialize(data, mid) { None => {
              return None;
            }, Some(x) => x, };
          )*
          let end = mid;
          let res = $newstruct {
            $($field),+
          };
          proof {
            assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());
          }
          Some((res, end))
        }
        proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
        // req, ens from trait
        {
          let si = self.ghost_serialize();
          let so = other.ghost_serialize();
          let mid: int = 0;
          $(
            if !self.$field.view_equal(&other.$field) {
              let (x0, x1) = (self.$field, other.$field);
              let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
              x0.lemma_view_equal_symmetric(&x1);
              let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                (x0, x1, s0, s1)
              } else {
                (x1, x0, s1, s0)
              };
              x0.lemma_serialization_is_not_a_prefix_of(&x1);
              assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE
              let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];
              if si == so.subrange(0, si.len() as int) {
                assert(si[mid + idx] == so[mid + idx]); // OBSERVE
              }
              return;
            } else {
              self.$field.lemma_same_views_serialize_the_same(&other.$field);
            }
            let mid = mid + self.$field.ghost_serialize().len();
          )*
        }
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
        // req, ens from trait
        {
          $(
            self.$field.lemma_same_views_serialize_the_same(&other.$field);
          )*
        }
        proof fn lemma_serialize_injective(self: &Self, other: &Self) {
          if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                   =~= other.ghost_serialize()); // OBSERVE
          }
        }
      }
    }
  };
}

pub(crate) use derive_marshalable_for_struct;

/// `define_struct_and_derive_marshalable` is a macro that, well, defines an struct, and implements
/// [`Marshalable`] on it. This is intended to make it easier to produce serializers and
/// deserializers for arbitrary types (including polymorphic ones).
///
/// See also [`define_enum_and_derive_marshalable`] for the equivalent enum-based macro.
///
/// Example usage:
///
/// ```
/// define_struct_and_derive_marshalable! {
///   struct Example<T: Marshalable, U: Marshalable> {
///     t: T,
///     u: U,
///     v: Vec::<u8>,
///   }
/// }
/// ```
#[allow(unused_macros)]
macro_rules! define_struct_and_derive_marshalable {
  {
    $( #[$attr:meta] )*
    $pub:vis
    struct $newstruct:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        $fieldvis:vis $field:ident : $fieldty:ty
      ),+
      $(,)?
    }
  } => {

    // We first re-generate the struct definition itself, so that the struct exists
    ::builtin_macros::verus! {
    $( #[$attr] )*
    $pub
    struct $newstruct $(< $($poly : Marshalable),+ >)? {
      $($fieldvis $field : $fieldty),+
    }
    }

    // ..and then implement `Marshalable` on it.
    derive_marshalable_for_struct! {
      $( #[$attr] )*
      $pub
      struct $newstruct $(< $($poly : Marshalable),+ >)? {
        $($fieldvis $field : $fieldty),+
      }
    }

  };
}

pub(crate) use define_struct_and_derive_marshalable;

/// `derive_marshalable_for_enum` is a macro that implements [`Marshalable`] for a enum. You
/// probably want to use [`define_enum_and_derive_marshalable`] wherever possible instead, since it
/// prevents code duplication. However, if you are (for some reason) unable to define at the enum
/// definition site, then this macro lets you derive the macro by simply (textually) copy-pasting
/// the enum.
macro_rules! derive_marshalable_for_enum {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
    $( [rlimit attr = $rlimitattr:meta] )?
  } => {
    ::builtin_macros::verus! {
      impl $(< $($poly : Marshalable),+ >)? Marshalable for $newenum $(< $($poly),+ >)? {
        open spec fn view_equal(&self, other: &Self) -> bool {
          &&& match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $(&&& $member.view_equal($memother))* )?
                &&& true
              }
            ),+
            _ => false,
          }
        }
        proof fn lemma_view_equal_symmetric(&self, other: &Self)
        // req, ens from trait
        {
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $($member.lemma_view_equal_symmetric($memother);)* )?
              }
            ),+
            _ => (),
          }
        }
        open spec fn is_marshalable(&self) -> bool {
          &&& match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                $( $(&&& $member.is_marshalable())* )?
                &&& 1 $( $(+ $member.ghost_serialize().len())* )? <= usize::MAX
              }
            ),+
          }
        }
        exec fn _is_marshalable(&self) -> bool {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                &&& true
                $( $(&&& $member._is_marshalable())* )?
                $( &&& no_usize_overflows!(1, $($member.serialized_size()),*) )?
              }
            ),+
          }
        }
        open spec fn ghost_serialize(&self) -> Seq<u8> {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                seq![$tag] $( $(+ $member.ghost_serialize())* )?
              }
            ),*
          }
        }
        exec fn serialized_size(&self) -> (res: usize)
          // req, ens from trait
        {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                1 $( $(+ $member.serialized_size())* )?
              }
            ),*
          }
        }
        exec fn serialize(&self, data: &mut Vec<u8>)
          // req, ens from trait
        {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                data.push($tag);
                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);
                $( $(
                  proof {
                    assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![$tag]);
                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                  }
                  $member.serialize(data);
                )* )?
                proof {
                  assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());
                  assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
                }
              }
            ),*
          }
        }
        $( #[$rlimitattr] )?
        exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
          // req, ens from trait
        {
          if data.len() == 0 || start >= data.len() - 1 {
            return None;
          }
          let tag = data[start];
          let (x, end) = $(
            if tag == $tag {
              let mid = start + 1;
              $( $(
                let ($member, mid) = match $memberty::deserialize(data, mid) { None => {
                  return None;
                }, Some(x) => x, };
              )* )?
              ($newenum::$variant $( { $($member),* } )?, mid)
            } else
          )* {
            return None;
          };
          proof {
            assert(data@.subrange(start as int, end as int) == x.ghost_serialize()) by {
                assert(data@.subrange(start as int, end as int).len() == x.ghost_serialize().len());
                assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());
            }
          }
          Some((x, end))
        }
        proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
        // req, ens from trait
        {
          let si = self.ghost_serialize();
          let so = other.ghost_serialize();
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                let mid: int = 1;
                $($(
                  if !$member.view_equal(&$memother) {
                    let (x0, x1) = ($member, $memother);
                    let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());
                    x0.lemma_view_equal_symmetric(&x1);
                    let (x0, x1, s0, s1) = if s0.len() <= s1.len() {
                      (x0, x1, s0, s1)
                    } else {
                      (x1, x0, s1, s0)
                    };
                    x0.lemma_serialization_is_not_a_prefix_of(&x1);
                    assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE
                    let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];
                    if si == so.subrange(0, si.len() as int) {
                      assert(si[mid + idx] == so[mid + idx]); // OBSERVE
                    }
                    return;
                  } else {
                    $member.lemma_same_views_serialize_the_same(&$memother);
                  }
                  let mid = mid + $member.ghost_serialize().len();
                )*)?
              }
            ),+
            _ => {
              if si == so.subrange(0, si.len() as int) {
                assert(si[0] == so[0]); // OBSERVE
              }
            },
          }
        }
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
        // req, ens from trait
        {
          match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $($member.lemma_same_views_serialize_the_same($memother);)* )?
              }
            ),+
            _ => (),
          }
        }
        proof fn lemma_serialize_injective(self: &Self, other: &Self)
          // req, ens from trait
        {
          if !self.view_equal(other) {
            self.lemma_serialization_is_not_a_prefix_of(other);
            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                   =~= other.ghost_serialize()); // OBSERVE
          }
        }
      }
    }
  };
}

pub(crate) use derive_marshalable_for_enum;

/// `define_enum_and_derive_marshalable` is a macro that, well, defines an enum, and implements
/// [`Marshalable`] on it. This is intended to make it easier to produce serializers and
/// deserializers for arbitrary types (including polymorphic ones).
///
/// It currently supports enums that have a maximum of 256 variants, since it uses a 1-byte tag to
/// pick between the variants.
///
/// See also [`define_struct_and_derive_marshalable`] for the equivalent struct-based macro.
///
/// Example usage:
///
/// ```
/// define_enum_and_derive_marshalable! {
///   enum Example<T: Marshalable, U: Marshalable> {
///     #[tag = 0]
///     U { u: u64, v: u64, x: Vec::<u8>, z: T },
///     #[tag = 1]
///     V { zz: U },
///   }
/// }
/// ```
///
/// Note: Currently due to https://github.com/verus-lang/verus/issues/444, passingly only a
/// single-variant enum will cause Verus to panic. But if you wanted just one variant, why are you
/// wasting a byte in the serialized output? Just use [`define_struct_and_derive_marshalable`]
/// instead!
#[allow(unused_macros)]
macro_rules! define_enum_and_derive_marshalable {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
  } => {

    // We first re-generate the enum definition itself, so that the enum exists
    ::builtin_macros::verus! {
    $( #[$attr] )*
    $pub
    enum $newenum $(< $($poly : Marshalable),+ >)? {
      $($variant $( { $($member : $memberty),* } )?),+
    }
    }

    // ..and then implement `Marshalable` on it.
    derive_marshalable_for_enum! {
      $( #[$attr] )*
      $pub
      enum $newenum $(< $($poly : Marshalable),+ >)? {
        $(
          #[tag = $tag]
          $variant $( { $(#[o=$memother] $member : $memberty),* } )?
        ),+
      }

    }
  };
}

pub(crate) use define_enum_and_derive_marshalable;

/// A macro that conveniently lets one produce a marshaler for a type `$type` by showing a
/// bijection to another (already known to be marshalable) type `$marshalable`.
///
/// This macro only needs to be provided with a forward and backward function (and a few new
/// identifiers, just to keep things distinct from things already known) and it'll produce
/// everything necessary to make the type marshalable.
#[allow(unused_macros)]
macro_rules! marshalable_by_bijection {
    {
        [$type:ty] <-> [$marshalable:ty];
        forward ($self:ident) $forward:expr;
        backward ($m:ident) $backward:expr;
    }
    =>
    {
        ::builtin_macros::verus! {
            impl $type {
                 pub open spec fn forward_bijection_for_view_equality_do_not_use_for_anything_else($self: Self) -> $marshalable {
                  $forward
                }
            }
            impl Marshalable for $type {
                open spec fn view_equal(&self, other: &Self) -> bool {
                    self.forward_bijection_for_view_equality_do_not_use_for_anything_else().view_equal(
                      &other.forward_bijection_for_view_equality_do_not_use_for_anything_else())
                }
                proof fn lemma_view_equal_symmetric(&self, other: &Self)
                  // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_view_equal_symmetric(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else())
                }
                open spec fn is_marshalable($self: &Self) -> bool {
                    $forward.is_marshalable()
                }
                exec fn _is_marshalable($self: &Self) -> (res: bool)
                // req, ens from trait
                {
                    $forward._is_marshalable()
                }
                open spec fn ghost_serialize($self: &Self) -> Seq<u8>
                // req, ens from trait
                {
                    $forward.ghost_serialize()
                }
                exec fn serialized_size($self: &Self) -> (res: usize)
                // req, ens from trait
                {
                    $forward.serialized_size()
                }
                exec fn serialize($self: &Self, data: &mut Vec<u8>)
                // req, ens from trait
                {
                    $forward.serialize(data)
                }
                exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
                // req, ens from trait
                {
                    match <$marshalable>::deserialize(data, start) {
                        None => None,
                        Some(($m, end)) => {
                            Some(($backward, end))
                        }
                    }
                }
                proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)
                // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_serialization_is_not_a_prefix_of(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else()
                  );
                }
                proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
                // req, ens from trait
                {
                  self.forward_bijection_for_view_equality_do_not_use_for_anything_else().lemma_same_views_serialize_the_same(
                    &other.forward_bijection_for_view_equality_do_not_use_for_anything_else()
                  );
                }
                proof fn lemma_serialize_injective(self: &Self, other: &Self)
                // req, ens from trait
                {
                  if !self.view_equal(other) {
                    self.lemma_serialization_is_not_a_prefix_of(other);
                    assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
                           =~= other.ghost_serialize()); // OBSERVE
                  }
                }
            }
        }
    };
}

pub(crate) use marshalable_by_bijection;

} // verus!

}

mod message_t{
#![verus::trusted]
//! Translates file Distributed/Protocol/SHT/Message.i.dfy
use builtin::*;
use builtin_macros::*;

use crate::abstract_end_point_t::*;
use crate::app_interface_t::*;
use crate::keys_t::*;
use crate::network_t::*;

verus! {

#[is_variant]
pub enum Message {
    GetRequest { key: AbstractKey },
    SetRequest { key: AbstractKey, value: Option<AbstractValue> },
    Reply { key: AbstractKey, value: Option<AbstractValue> },
    Redirect { key: AbstractKey, id: AbstractEndPoint },
    Shard { range: KeyRange<AbstractKey>, recipient: AbstractEndPoint },
    Delegate { range: KeyRange<AbstractKey>, h: Hashtable },
}

} // verus!

}

mod net_sht_v{
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

#[is_variant]
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
    forall|i: int| 
        0 <= i && i < rawlog.len() ==> #[trigger]
        net_event_is_abstractable(rawlog[i])
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
                    if !dst.valid_physical_address()  {
                        return CSingleMessage::InvalidMessage;
                    }
                    match m {
                        CMessage::Redirect { id, .. } => {
                            if !id.valid_physical_address()  {
                                return CSingleMessage::InvalidMessage;
                            }
                        },
                        CMessage::Shard { recipient, .. } => {
                            if !recipient.valid_physical_address()  {
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
        old(netc).state().is_Receiving(),
        local_addr.abstractable(),
    ensures
        ({
            let (rr, net_event) = rc;
            &&& netc.my_end_point() == old(netc).my_end_point()
            &&& netc.ok() == !rr.is_Fail()
            &&& !rr.is_Fail() ==> netc.ok() && netc.history() == old(netc).history()
                + seq!( net_event@ )
            &&& rr.is_Timeout() ==> net_event@.is_TimeoutReceive()
            &&& (rr.is_Packet() ==> {
                &&& net_event@.is_Receive()
                &&& true  // NetPacketIsAbstractable is true
                
                &&& rr.get_Packet_cpacket().abstractable()  // can parse u8s up to NetEvent.
                
                &&& true  // EndPointIsValidPublicKey
                
                &&& !(rr.get_Packet_cpacket()@.msg is InvalidMessage) ==> {
                    &&& rr.get_Packet_cpacket()@ == abstractify_net_packet_to_sht_packet(
                        net_event@.get_Receive_r(),
                    )
                    &&& rr.get_Packet_cpacket().msg@ == sht_demarshal_data(
                        net_event@.get_Receive_r().msg,
                    )@
                }
                &&& rr.get_Packet_cpacket().dst@ == local_addr@
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
                if !(gsinglemessage is InvalidMessage)  {
                    let lp = LPacket {
                        dst: local_addr@,
                        src: src_ep@,
                        msg: (sht_demarshal_data(message@))@,
                    };
                    assert(lp == abstractify_net_packet_to_lsht_packet(net_event.get_Receive_r()));
                    let p = Packet { dst: lp.dst, src: lp.src, msg: lp.msg };
                    assert(p == abstractify_net_packet_to_sht_packet(net_event.get_Receive_r()));
                    assert(!(gsinglemessage is InvalidMessage));
                    assert(gsinglemessage@ == (sht_demarshal_data(message@))@);
                    assert(cpacket@.dst =~= p.dst);
                    assert(cpacket@.src =~= p.src);
                    assert(cpacket@.msg =~= p.msg);
                    assert(cpacket@ =~= p);
                    assert(cpacket@ == abstractify_net_packet_to_sht_packet(
                        net_event.get_Receive_r(),
                    ));
                    assert(gsinglemessage is Message ==> cpacket.msg@ == sht_demarshal_data(
                        net_event.get_Receive_r().msg,
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
    
    &&& (
    !cpacket.msg.is_InvalidMessage())  // (out.msg.CSingleMessage? || out.msg.CAck?)

}

pub open spec fn send_log_entry_reflects_packet(event: NetEvent, cpacket: &CPacket) -> bool {
    &&& event.is_Send()
    &&& true  // NetPacketIsAbstractable == EndPointIsAbstractable == true
    
    &&& cpacket.abstractable()
    &&& cpacket@ == abstractify_net_packet_to_sht_packet(event.get_Send_s())
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
                &&& ok ==> net_event.is_Some()
                &&& ok ==> netc.history() == old(netc).history() + seq![net_event.unwrap()]
                &&& ok ==> rc.1@.is_Some() && send_log_entry_reflects_packet(
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
    forall|i| 
        0 <= i < cpackets.len() ==> #[trigger]
        outbound_packet_is_valid(&cpackets[i])
}

pub open spec fn outbound_packet_seq_has_correct_srcs(
    cpackets: Seq<CPacket>,
    end_point: AbstractEndPoint,
) -> bool {
    // TODO(chris): Why doesn't this trigger attribute satisfy Verus!?
    forall|i| #![auto] 0 <= i < cpackets.len() ==> cpackets[i].src@ == end_point
}

pub open spec fn net_packet_bound(data: Seq<u8>) -> bool {
    data.len() <= 0xffff_ffff_ffff_ffff
}

pub open spec fn is_marshalable_data(event: NetEvent) -> bool
    recommends
        event.is_Send(),
{
    &&& net_packet_bound(event.get_Send_s().msg)
    &&& sht_demarshal_data(event.get_Send_s().msg).is_marshalable()
}

pub open spec fn only_sent_marshalable_data(rawlog: Seq<NetEvent>) -> bool {
    forall|i| 
        0 <= i < rawlog.len() && rawlog[i].is_Send() ==> #[trigger]
        is_marshalable_data(rawlog[i])
}

/// translates SendLogReflectsPacket
pub open spec fn send_log_entries_reflect_packets(
    net_event_log: Seq<NetEvent>,
    cpackets: Seq<CPacket>,
) -> bool {
    &&& net_event_log.len() == cpackets.len()
    &&& (forall|i| 
        0 <= i < cpackets.len() ==> #[trigger]
        send_log_entry_reflects_packet(net_event_log[i], &cpackets[i]))
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
        if !ok  {
            return (false, Ghost(Seq::<NetEvent>::empty()));
        }
        i = i + 1;
        proof {
            let net_event = net_event.unwrap();
            let net_events0 = net_events;
            net_events = net_events + seq![net_event];
            let cpackets_prefix = cpackets@.subrange(0, i as int);
            assert forall|j| 0 <= j < i as int implies #[trigger]
            send_log_entry_reflects_packet(net_events[j], &cpackets_prefix[j]) by {
                if j == i - 1 {
                    assert(net_events[j] == net_event);
                } else {
                    assert(cpackets_prefix[j] == cpackets@.subrange(0, i - 1 as int)[j]);
                }
            }
            assert forall|j| 0 <= j < net_events.len() && net_events[j].is_Send() implies #[trigger]
            is_marshalable_data(net_events[j]) by {
                assert(send_log_entry_reflects_packet(net_events[j], &cpackets_prefix[j]));
                if j == i - 1 {
                    assert(net_events[j] == net_event);
                } else {
                    assert(net_events[j] == net_events0[j]);
                }
            }
        }
    }
    proof {
        assert_seqs_equal!(cpackets@.subrange(0, cpackets@.len() as int), cpackets@);
    }
    (true, Ghost(net_events))
}

} // verus!

}

mod network_t{
#![verus::trusted]
//! Translates Distributed/Protocol/SHT/Network.i.dfy

use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;

use crate::abstract_end_point_t::*;
use crate::message_t::*;
use crate::single_message_t::*;

verus! {

pub type PMsg = SingleMessage<Message>;

/// A Packet is an abstract version of a `CPacket`.
///
/// It's isomorphic to an `LSHTPacket = LPacket<AbstractEndPoint,
/// SingleMessage<Message>>`.
pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
}

} // verus!

}

mod seq_is_unique_v{
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::set_lib::*;

use crate::abstract_end_point_t::*;
use crate::args_t::*;
use crate::io_t::*;
use builtin::*;
use builtin_macros::*;

verus! {

// Translates Impl/Common/SeqIsUniqueDef.i.dfy :: SeqIsUnique
#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
}

pub fn do_vec_u8s_match(e1: &Vec<u8>, e2: &Vec<u8>) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    if e1.len() != e2.len() {
        assert(e1@.len() != e2@.len());
        assert(e1@ != e2@);
        return false;
    }
    let mut i: usize = 0;
    while i < e1.len() 
        invariant
            0 <= i,
            i <= e1.len(),
            e1.len() == e2.len(),
            forall|j: int| 0 <= j && j < i ==> e1@[j] == e2@[j],
    {
        if e1[i] != e2[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert_seqs_equal!(e1@, e2@);
    }
    return true;
}

pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    do_vec_u8s_match(&e1.id, &e2.id)
}

// Translates Impl/Common/CmdLineParser.i.dfy :: test_unique
pub fn test_unique(endpoints: &Vec<EndPoint>) -> (unique: bool)
    ensures
        unique == seq_is_unique(abstractify_end_points(*endpoints)),
{
    let mut i: usize = 0;
    while i < endpoints.len() 
        invariant
            0 <= i,
            i <= endpoints.len(),
            forall|j: int, k: int| 
                #![trigger endpoints@[j]@, endpoints@[k]@]
                0 <= j && j < endpoints.len() && 0 <= k && k < i && j != k ==> endpoints@[j]@
                    != endpoints@[k]@,
    {
        let mut j: usize = 0;
        while j < endpoints.len() 
            invariant
                0 <= i,
                i < endpoints.len(),
                forall|j: int, k: int| 
                    #![trigger endpoints@[j]@, endpoints@[k]@]
                    0 <= j && j < endpoints.len() && 0 <= k && k < i && j != k ==> endpoints@[j]@
                        != endpoints@[k]@,
                0 <= j,
                j <= endpoints.len(),
                forall|k: int| 
                    #![trigger endpoints@[k]@]
                    0 <= k && k < j && k != i ==> endpoints@[i as int]@ != endpoints@[k]@,
        {
            if i != j && do_end_points_match(&endpoints[i], &endpoints[j]) {
                assert(!seq_is_unique(abstractify_end_points(*endpoints))) by {
                    reveal(seq_is_unique::<AbstractEndPoint>);
                    let aeps = abstractify_end_points(*endpoints);
                    assert(aeps[i as int] == endpoints@[i as int]@);
                    assert(aeps[j as int] == endpoints@[j as int]@);
                    assert(endpoints@[i as int]@ == endpoints@[j as int]@ && i != j);
                }
                return false;
            }
            j = j + 1;
        }
        i = i + 1;
    };
    assert(seq_is_unique(abstractify_end_points(*endpoints))) by {
        reveal(seq_is_unique::<AbstractEndPoint>);
    }
    return true;
}

pub fn endpoints_contain(endpoints: &Vec<EndPoint>, endpoint: &EndPoint) -> (present: bool)
    ensures
        present == abstractify_end_points(*endpoints).contains(endpoint@),
{
    let mut j: usize = 0;
    while j < endpoints.len() 
        invariant
            0 <= j && j <= endpoints.len(),
            forall|k: int| 
                #![trigger endpoints@[k]@]
                0 <= k && k < j ==> endpoint@ != endpoints@[k]@,
    {
        if do_end_points_match(endpoint, &endpoints[j]) {
            assert(abstractify_end_points(*endpoints)[j as int] == endpoint@);
            return true;
        }
        j = j + 1;
    }
    return false;
}

pub fn clone_option_vec_u8(ov: Option<&Vec<u8>>) -> (res: Option<Vec<u8>>)
    ensures
        match ov {
            Some(e1) => res.is_some() && e1@ == res.get_Some_0()@,
            None => res.is_None(),
        },
{
    match ov {
        Some(e1) => Some(clone_vec_u8(e1)),
        None => None,
    }
}

pub fn clone_end_point(ep: &EndPoint) -> (cloned_ep: EndPoint)
    ensures
        cloned_ep@ == ep@,
{
    EndPoint { id: clone_vec_u8(&ep.id) }
}

pub fn clone_option_end_point(oep: &Option<EndPoint>) -> (cloned_oep: Option<EndPoint>)
    ensures
        match oep {
            Some(ep) => cloned_oep.is_some() && ep@ == cloned_oep.get_Some_0()@,
            None => cloned_oep.is_None(),
        },
{
    match oep.as_ref() {
        Some(ep) => Some(clone_end_point(ep)),
        None => None,
    }
}

pub proof fn singleton_seq_to_set_is_singleton_set<T>(x: T)
    ensures
        seq![x].to_set() == set![x],
{
    let seq1 = seq![x];
    let set1 = seq1.to_set();
    let set2 = set![x];
    assert forall|y| set1.contains(y) <==> set2.contains(y) by {
        if y == x {
            assert(seq1[0] == y);
            assert(set1.contains(y));
        }
    }
    assert_sets_equal!(seq![x].to_set(), set![x]);
}

} // verus!

}

mod single_delivery_model_v{
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
    ) -> CPacket// we rely on get_ack(AckOrInvalid) returning something about which
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
        forall|i| 
            0 <= i < packets.len() ==> #[trigger]
            packets[i].msg is Message
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
            assert forall|ep: AbstractEndPoint| 
                #[trigger]
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
                    let opt_ack = Some(p_ack);  // Fresh or Duplicate
                    opt_ack
                } else {
                    None
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        }// When ReceiveSingleMessageImpl calls MaybeAckPacketImpl(acct'), the returned b must be true,
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
    /// TODO: Andrea points out that this postcondition is unachievable. So we should probably
    /// go back to the Ironfleet Dafny approach of returning a `sm: CSingleMessage` and a `should_send: bool`.
    /// The issue is that even in the `!should_send` case we still need a field of the (dummy) `sm`, namely
    /// its `dst`.
    #[verifier::rlimit(15)]
    pub fn send_single_cmessage(&mut self, m: &CMessage, dst: &EndPoint) -> (sm: Option<
        CSingleMessage,
    >)
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
                    &&& sm.is_Message()
                    &&& sm.get_Message_dst()@ == dst@
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
            },// TODO: capture the part of send_single_message when should_send == false
    
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
        assert forall|ep: EndPoint| 
            #[trigger]
            self.send_state@.contains_key(ep@) implies ep.abstractable()
            && self.send_state.epmap[&ep].abstractable() by {
            if ep@ != dst@ {
                assert(old(self).send_state@.contains_key(ep@));
            }
        }
        assert forall|ep: AbstractEndPoint| 
            #[trigger]
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

}

mod single_delivery_state_v{
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
        }//         let e = CAckState{ num_packets_acked: 0, un_acked: vec![] };
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
                    0 <= j < i as nat ==> #[trigger]
                    (un_acked@[j]@) == self.un_acked@[j]@,
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
        forall|i: int| 
            0 <= i < self.un_acked.len() ==> #[trigger]
            self.un_acked[i].abstractable()
    }
    
    pub open spec fn no_acks_in_unacked(list: Seq<CSingleMessage>) -> bool {
        forall|i: int| 
            0 <= i < list.len() ==> #[trigger]
            list[i].is_Message()
    }
    
    pub open spec fn un_acked_list_sequential(list: Seq<CSingleMessage>) -> bool
        recommends
            Self::no_acks_in_unacked(list),
    {
        forall|i: int, j: int| 
            #![auto]
            0 <= i && j == i + 1 && j < list.len() ==> list[i].get_Message_seqno() as int + 1
                == list[j].get_Message_seqno() as int
    }
    
    pub open spec fn un_acked_valid(msg: &CSingleMessage) -> bool {
        &&& msg.is_Message()
        &&& msg.abstractable()
        &&& msg.is_marshalable()
    }
    
    pub open spec fn un_acked_list_valid(list: Seq<CSingleMessage>) -> bool {
        &&& forall|i: int| 
            0 <= i < list.len() ==> #[trigger]
            Self::un_acked_valid(&list[i])
            &&& Self::un_acked_list_sequential(list)
    }
    
    pub open spec fn un_acked_list_valid_for_dst(
        list: Seq<CSingleMessage>,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid(list)
        &&& forall|i: int| 
            0 <= i < list.len() ==> (#[trigger]
            list[i].get_Message_dst())@ == dst
    }
    
    pub open spec fn valid_list(
        msgs: Seq<CSingleMessage>,
        num_packets_acked: int,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid_for_dst(msgs, dst)
        &&& num_packets_acked as int + msgs.len() as int
            <= AbstractParameters::static_params().max_seqno
        &&& (msgs.len() > 0 ==> msgs[0].get_Message_seqno() == num_packets_acked + 1)
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
            self.un_acked@[k].get_Message_seqno() == self.num_packets_acked + k + 1,
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
            self.un_acked@.len() > 0 ==> self.un_acked[0]@.get_Message_seqno() == seqno_acked + 1,
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
                i < self.un_acked.len() ==> self.un_acked[i as int].get_Message_seqno()
                    <= seqno_acked + 1,
                forall|j: int| 
                    #![auto]
                    0 <= j < i ==> self.un_acked[j].get_Message_seqno() <= seqno_acked,
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
        assert(forall|k: AbstractEndPoint| 
            #[trigger]
            self@.contains_key(k) ==> old(self)@.contains_key(k) || k == src@);
    }
}

pub struct CSendState {
    pub epmap: endpoint_hashmap_t::HashMap<CAckState>,
}

impl CSendState {
    /// CSendStateIsAbstractable
    pub open spec fn abstractable(&self) -> bool {
        forall|ep: EndPoint| 
            #[trigger]
            self@.contains_key(ep@) ==> ep.abstractable()
                && self.epmap[&ep].abstractable()// NB ignoring the "ReverseKey" stuff from GenericRefinement.MapIsAbstractable
    
    }
    
    // AbstractifyCSendStateToSendState is implied by the second type argument to HashMap. A
    // consequence is that you don't get recommends on view.
    /// CSendStateIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& forall|ep: AbstractEndPoint| 
            #[trigger]
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
        assert(un_acked_at[i as int].is_Message());
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

}

mod single_delivery_t{
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

pub open spec(checked) fn truncate_un_ack_list<MT>(un_acked: AckList<MT>, seqno_acked: nat) -> Seq<
    SingleMessage<MT>,
>
    decreases un_acked.len(),
{
    if un_acked.len() > 0 && un_acked[0] is Message && un_acked[0].get_Message_seqno()
        <= seqno_acked {
        truncate_un_ack_list(un_acked.skip(1), seqno_acked)
    } else {
        un_acked
    }
}

#[verifier::ext_equal]  // effing INSAASAAAAANNE
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
#[verifier::ext_equal]  // effing INSAASAAAAANNE
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
        &&& pkt.msg.get_Message_seqno() == last_seqno + 1
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
            if pkt.msg.get_Ack_ack_seqno() > old_ack_state.num_packets_acked {
                let new_ack_state = AckState {
                    num_packets_acked: pkt.msg.get_Ack_ack_seqno(),
                    un_acked: truncate_un_ack_list(
                        old_ack_state.un_acked,
                        pkt.msg.get_Ack_ack_seqno(),
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
            pkt.msg.get_Message_seqno() <= last_seqno
        }
    }
    
    /// Protocol/SHT/SingleDelivery.i.dfy SendAck
    pub open spec(checked) fn send_ack(self, pkt: Packet, ack: Packet, acks: Set<Packet>) -> bool
        recommends
            self.should_ack_single_message(pkt),
    {
        &&& ack.msg is Ack
        &&& ack.msg.get_Ack_ack_seqno() == pkt.msg.get_Message_seqno()
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
                            &&& self.send_state[dst].un_acked[i].is_Message()
                            &&& p.msg == self.send_state[dst].un_acked[i]
                            &&& p.dst == p.msg.get_Message_dst()
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

}

mod single_message_t{
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

#[is_variant]
pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },  // I have received everything up to and including seqno
    InvalidMessage {},  // ... what parse returns for raw messages we can't otherwise parse into a valid message above
}

} // verus!

}

mod verus_extra{
pub mod choose_v{
use vstd::prelude::*;

verus! {

/// Equivalent to `choose |i:int| low <= i < high && p(i)` except it guarantees to pick the smallest
/// such value `i` where `p(i)` is true.
pub proof fn choose_smallest(low: int, high: int, p: FnSpec(int) -> bool) -> (res: int)
    requires
        exists|i: int| #![trigger(p(i))] low <= i < high && p(i),
    ensures
        low <= res < high,
        p(res),
        forall|i: int| #![trigger(p(i))] low <= i < res ==> !p(i),
    decreases high - low,
{
    if p(low) {
        low
    } else {
        choose_smallest(low + 1, high, p)
    }
}

} // verus!

}

pub mod clone_v{
use vstd::prelude::*;

verus! {

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;  // this is way too restrictive; it kind of demands Copy. But we don't have a View trait yet. :v(

}

} // verus!

}

pub mod seq_lib_v{
use builtin::*;
use builtin_macros::*;
use vstd::function::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub proof fn lemma_subrange_subrange<A>(s: Seq<A>, start: int, midsize: int, endsize: int)
    requires
        0 <= start <= s.len(),
        0 <= midsize <= endsize <= s.len() - start,
    ensures
        s.subrange(start, start + endsize).subrange(0, midsize) == s.subrange(
            start,
            start + midsize,
        ),
{
    assert(s.subrange(start, start + endsize).subrange(0, midsize) =~= s.subrange(
        start,
        start + midsize,
    ));
}

pub proof fn lemma_seq_add_subrange<A>(s: Seq<A>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        s.subrange(i, j) + s.subrange(j, k) == s.subrange(i, k),
{
    assert_seqs_equal!{s.subrange(i, j) + s.subrange(j, k), s.subrange(i, k)}
}

pub proof fn lemma_seq_fold_left_merge_right_assoc<A, B>(
    s: Seq<A>,
    init: B,
    f: FnSpec(A) -> B,
    g: FnSpec(B, B) -> B,
)
    requires
        s.len() > 0,
        forall|x, y, z| #[trigger g(x, y)] g(g(x, y), z) == g(x, g(y, z)),
    ensures
        g(s.subrange(0, s.len() - 1).fold_left(init, |b: B, a: A| g(b, f(a))), f(s[s.len() - 1]))
            == s.fold_left(init, |b: B, a: A| g(b, f(a))),
    decreases s.len(),
{
    let emp = Seq::<B>::empty();
    let len: int = s.len() as int;
    let i = len - 1;
    let s1 = s.subrange(0, len - 1);
    let last = s[len - 1];
    let accf = |b: B, a: A| g(b, f(a));
    let start = s1.fold_left(init, accf);
    let all = s.fold_left(init, accf);
    if s1.len() == 0 {
        assert(s.len() == 1);
        reveal_with_fuel(Seq::fold_left, 2);
        reveal_with_fuel(Seq::fold_left, 2);
    } else {
        reveal_with_fuel(Seq::fold_left, 2);
        let head = s[0];
        let tail = s.subrange(1, len);
        let p = accf(init, s[0]);
        // assert(tail.len() > 0);
        // assert(all == tail.fold_left(p, accf));
        // assert(start == s1.fold_left(init, accf));
        // assert(s1.len() > 0);
        // assert(start == s1.subrange(1, s1.len() as int).fold_left(p, accf));
        // assert(start == s1.subrange(1, len - 1).fold_left(p, accf));
        assert_seqs_equal!(tail.subrange(0, len - 2) == s1.subrange(1, len - 1));
        // assert(start == tail.subrange(0, tail.len() - 1).fold_left(p, accf));
        // assert(all == tail.fold_left(p, accf));
        lemma_seq_fold_left_merge_right_assoc::<A, B>(tail, p, f, g);
        // assert(all == g(start, f(last)));
    }
}

pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: FnSpec(A) -> int)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
            == s.fold_left(low, |b: int, a: A| b + f(a)),
{
    let g = |x: int, y: int| x + y;
    fun_ext_2::<int, A, int>(|b: int, a: A| b + f(a), |b: int, a: A| g(b, f(a)));
    lemma_seq_fold_left_merge_right_assoc::<A, int>(s, low, f, g);
}

pub proof fn lemma_seq_fold_left_append_right<A, B>(
    s: Seq<A>,
    prefix: Seq<B>,
    f: FnSpec(A) -> Seq<B>,
)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)) + f(
            s[s.len() - 1],
        ) == s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)),
{
    let g = |x: Seq<B>, y: Seq<B>| x + y;
    assert forall|x, y, z| #[trigger g(x,y)] g(g(x, y), z) == g(x, g(y, z)) by {
        assert_seqs_equal!(g(g(x, y), z) == g(x, g(y, z)));
    };
    fun_ext_2::<Seq<B>, A, Seq<B>>(|b: Seq<B>, a: A| b + f(a), |b: Seq<B>, a: A| g(b, f(a)));
    lemma_seq_fold_left_merge_right_assoc::<A, Seq<B>>(s, prefix, f, g);
}

pub proof fn lemma_seq_fold_left_append_len_int<A, B>(
    s: Seq<A>,
    prefix: Seq<B>,
    f: FnSpec(A) -> Seq<B>,
)
    ensures
        s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)).len() as int == s.fold_left(
            prefix.len() as int,
            |i: int, a: A| i + f(a).len() as int,
        ),
    decreases s.len(),
{
    s.lemma_fold_left_alt(prefix, |sb: Seq<B>, a: A| sb + f(a));
    s.lemma_fold_left_alt(prefix.len() as int, |i: int, a: A| i + f(a).len() as int);
    if s.len() != 0 {
        lemma_seq_fold_left_append_len_int::<A, B>(
            s.subrange(1, s.len() as int),
            prefix + f(s[0]),
            f,
        );
        s.subrange(1, s.len() as int).lemma_fold_left_alt(
            prefix + f(s[0]),
            |sb: Seq<B>, a: A| sb + f(a),
        );
        s.subrange(1, s.len() as int).lemma_fold_left_alt(
            prefix.len() as int + f(s[0]).len() as int,
            |i: int, a: A| i + f(a).len() as int,
        );
    }
}

pub proof fn lemma_seq_fold_left_sum_len_int_positive<A, B>(
    s: Seq<A>,
    low: nat,
    f: FnSpec(A) -> Seq<B>,
)
    ensures
        s.fold_left(low as int, |acc: int, x: A| acc + f(x).len()) >= 0,
    decreases s.len(),
{
    s.lemma_fold_left_alt(low as int, |acc: int, x: A| acc + f(x).len());
    if s.len() != 0 {
        lemma_seq_fold_left_sum_len_int_positive::<A, B>(
            s.subrange(1, s.len() as int),
            low + f(s[0]).len(),
            f,
        );
        s.subrange(1, s.len() as int).lemma_fold_left_alt(
            low + f(s[0]).len() as int,
            |acc: int, x: A| acc + f(x).len(),
        );
    }
}

pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(
    s: Seq<A>,
    i: int,
    low: int,
    f: FnSpec(A) -> Seq<B>,
)
    requires
        0 <= i <= s.len() as int,
        0 <= low,
    ensures
        s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
        s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <= s.fold_left(
            low,
            |acc: int, x: A| acc + f(x).len(),
        ),
    decreases (2 * s.len() - i),
{
    lemma_seq_fold_left_sum_len_int_positive::<A, B>(s, low as nat, f);
    let accfl = |acc: int, x: A| acc + f(x).len();
    if s.len() == 0 {
        // done
    } else if i == s.len() {
        assert_seqs_equal!(s.subrange(0, i) == s);
        lemma_seq_fold_left_append_len_int_le::<A, B>(
            s.subrange(1, s.len() as int),
            i - 1,
            low + f(s[0]).len() as int,
            f,
        );
    } else if i == s.len() - 1 {
        let fl = |x| f(x).len() as int;
        fun_ext_2::<int, A, int>(accfl, |acc: int, x: A| acc + fl(x));
        lemma_seq_fold_left_sum_right::<A>(s, low, fl);
    } else {
        lemma_seq_fold_left_append_len_int_le::<A, B>(s.subrange(0, s.len() - 1), i, low, f);
        lemma_seq_fold_left_append_len_int_le::<A, B>(s, s.len() - 1, low, f);
        assert_seqs_equal!(s.subrange(0, s.len() - 1).subrange(0, i) == s.subrange(0, i));
    }
}

pub proof fn lemma_seq_fold_left_sum_le<A>(s: Seq<A>, init: int, high: int, f: FnSpec(A) -> int)
    requires
        forall|i: int| 0 <= i < s.len() ==> f(s[i]) <= high,
    ensures
        s.fold_left(init, |acc: int, x: A| acc + f(x)) <= init + s.len() * high,
    decreases s.len(),
{
    if s.len() != 0 {
        lemma_seq_fold_left_sum_le(s.drop_last(), init, high, f);
        assert(init + (s.len() - 1) * high + high <= init + s.len() * high) by (nonlinear_arith);
    }
}

pub proof fn lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity<A>(
    s: Seq<A>,
    pred: FnSpec(A) -> bool,
)
    requires
        forall|i: int| 0 <= i && i < s.len() ==> pred(s[i]),
    ensures
        s.filter(pred) == s,
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(subseq, pred);
        assert_seqs_equal!(s, subseq.push(s.last()));
    }
}

pub proof fn lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty<A>(
    s: Seq<A>,
    pred: FnSpec(A) -> bool,
)
    requires
        forall|i: int| 0 <= i && i < s.len() ==> !pred(s[i]),
    ensures
        s.filter(pred) =~= Seq::<A>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty(subseq, pred);
        assert_seqs_equal!(s, subseq.push(s.last()));
    }
}

pub proof fn lemma_filter_skip_rejected<A>(s: Seq<A>, pred: FnSpec(A) -> bool, i: int)
    requires
        0 <= i <= s.len(),
        forall|j| 0 <= j < i ==> !pred(s[j]),
    ensures
        s.filter(pred) == s.skip(i).filter(pred),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() == 0 {
        assert(s.skip(i) =~= s);
    } else if i < s.len() {
        assert(s.skip(i).drop_last() =~= s.drop_last().skip(i));
        lemma_filter_skip_rejected(s.drop_last(), pred, i);
    } else {
        assert(s.skip(i) =~= s.drop_last().skip(i - 1));
        lemma_filter_skip_rejected(s.drop_last(), pred, i - 1);
    }
}

pub proof fn lemma_fold_left_on_equiv_seqs<A, B>(
    s1: Seq<A>,
    s2: Seq<A>,
    eq: FnSpec(A, A) -> bool,
    init: B,
    f: FnSpec(B, A) -> B,
)
    requires
        s1.len() == s2.len(),
        (forall|i: int| 0 <= i < s1.len() ==> eq(s1[i], s2[i])),
        (forall|b: B, a1: A, a2: A| 
            #[trigger]
            eq(a1, a2) ==> #[trigger]
            f(b, a1) == f(b, a2)),
    ensures
        s1.fold_left(init, f) == s2.fold_left(init, f),
    decreases s1.len(),
{
    reveal(Seq::fold_left);
    if s1.len() != 0 {
        lemma_fold_left_on_equiv_seqs(s1.drop_last(), s2.drop_last(), eq, init, f);
    }
}

pub proof fn lemma_fold_left_append_merge<A, B>(s1: Seq<A>, s2: Seq<A>, f: FnSpec(A) -> Seq<B>)
    ensures
        (s1 + s2).fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a)) == s1.fold_left(
            Seq::empty(),
            |acc: Seq<B>, a: A| acc + f(a),
        ) + s2.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a)),
    decreases s1.len() + s2.len(),
{
    let e = Seq::<B>::empty();
    let af = |acc: Seq<B>, a: A| acc + f(a);
    let fl = |s: Seq<A>| s.fold_left(e, af);
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
        assert(fl(s1) =~= fl(s1) + e);
    } else {
        lemma_fold_left_append_merge(s1, s2.drop_last(), f);
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        assert((fl(s1) + fl(s2.drop_last())) + f(s2.last()) =~= fl(s1) + (fl(s2.drop_last()) + f(
            s2.last(),
        )));
    }
}

pub proof fn some_differing_index_for_unequal_seqs<A>(s1: Seq<A>, s2: Seq<A>) -> (i: int)
    requires
        s1 != s2,
        s1.len() == s2.len(),
    ensures
        0 <= i < s1.len(),
        s1[i] != s2[i],
{
    if forall|i| 0 <= i < s1.len() ==> s1[i] == s2[i] {
        assert(s1 =~= s2);
    }
    choose|i: int| 0 <= i < s1.len() && s1[i] != s2[i]
}

} // verus!

}

pub mod set_lib_ext_v{
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

verus! {

/// This fold uses a fixed zero rather than accumulating results in that
/// argument. This means proofs don't need to generalize over the accumulator,
/// unlike the Set::fold currently in Verus.
pub open spec fn set_fold<A, B>(s: Set<A>, zero: B, f: FnSpec(B, A) -> B) -> B
    recommends
        s.finite(),
    decreases s.len(),
{
    if s.finite() {
        if s.len() == 0 {
            zero
        } else {
            let a = s.choose();
            f(set_fold(s.remove(a), zero, f), a)
        }
    } else {
        zero
    }
}

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    // extra parens are for rust-analyzer
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

pub proof fn flatten_sets_spec<A>(sets: Set<Set<A>>)
    ensures
        (forall|e| 
            #[trigger]
            flatten_sets(sets).contains(e) ==> exists|s| sets.contains(s) && s.contains(e)),
        (forall|s: Set<A>| #[trigger] sets.contains(s) ==> s.subset_of(flatten_sets(sets))),
{
}

pub proof fn lemma_flatten_sets_insert<A>(sets: Set<Set<A>>, s: Set<A>)
    ensures
        flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s),
{
    assert_sets_equal!(flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s));
}

pub proof fn lemma_flatten_sets_union<A>(sets1: Set<Set<A>>, sets2: Set<Set<A>>)
    ensures
        flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
    assert_sets_equal!(flatten_sets(sets1.union(sets2)) ==
        flatten_sets(sets1).union(flatten_sets(sets2)));
}

pub proof fn lemma_flatten_sets_union_auto<A>()
    ensures
        forall|sets1: Set<Set<A>>, sets2: Set<Set<A>>| 
            #[trigger]
            flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
    assert forall|sets1: Set<Set<A>>, sets2: Set<Set<A>>| 
        #[trigger]
        flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)) by {
        lemma_flatten_sets_union(sets1, sets2);
    }
}

pub proof fn set_map_union<A, B>(s1: Set<A>, s2: Set<A>, f: FnSpec(A) -> B)
    ensures
        (s1 + s2).map(f) == s1.map(f) + s2.map(f),
{
    assert_sets_equal!((s1 + s2).map(f) == s1.map(f) + s2.map(f), y => {
        if s1.map(f).contains(y) {
            let x = choose |x| s1.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        } else if s2.map(f).contains(y) {
            let x = choose |x| s2.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        }
    });
}

pub proof fn set_map_union_auto<A, B>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, f: FnSpec(A) -> B| 
            #[trigger]
            (s1 + s2).map(f) == s1.map(f) + s2.map(f),
{
    assert forall|s1: Set<A>, s2: Set<A>, f: FnSpec(A) -> B| 
        #[trigger]
        ((s1 + s2).map(f)) == s1.map(f) + s2.map(f) by {
        set_map_union(s1, s2, f);
    }
}

pub proof fn seq_map_values_concat<A, B>(s1: Seq<A>, s2: Seq<A>, f: FnSpec(A) -> B)
    ensures
        (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f),
{
    assert_seqs_equal!((s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f), i => {
        if i < s1.len() {
            assert((s1+s2)[i] == s1[i]);
        } else {
            assert((s1+s2)[i] == s2[i - s1.len()]);
        }
    });
}

pub proof fn seq_map_values_concat_auto<A, B>()
    ensures
        forall|s1: Seq<A>, s2: Seq<A>, f: FnSpec(A) -> B| 
            #[trigger]
            (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f),
{
    assert forall|s1: Seq<A>, s2: Seq<A>, f: FnSpec(A) -> B| 
        #[trigger]
        ((s1 + s2).map_values(f)) == s1.map_values(f) + s2.map_values(f) by {
        seq_map_values_concat(s1, s2, f);
    }
}

pub open spec fn flatten_set_seq<A>(sets: Seq<Set<A>>) -> Set<A> {
    sets.fold_left(Set::<A>::empty(), |s1: Set<A>, s2: Set<A>| s1.union(s2))
}

pub proof fn lemma_flatten_set_seq_spec<A>(sets: Seq<Set<A>>)
    ensures
        (forall|x: A| 
            #[trigger]
            flatten_set_seq(sets).contains(x) ==> exists|i: int| 
                0 <= i < sets.len() && #[trigger]
                sets[i].contains(x)),
        (forall|x: A, i: int| 
            0 <= i < sets.len() && #[trigger]
            sets[i].contains(x) ==> flatten_set_seq(sets).contains(x)),
    decreases sets.len(),
{
    if sets.len() == 0 {
    } else {
        lemma_flatten_set_seq_spec(sets.drop_last());
        assert forall|x: A| flatten_set_seq(sets).contains(x) implies exists|i: int| 
            0 <= i < sets.len() && #[trigger]
            sets[i].contains(x) by {
            if sets.last().contains(x) {
            } else {
                assert(flatten_set_seq(sets.drop_last()).contains(x));
            }
        }
        assert forall|x: A, i: int| 
            0 <= i < sets.len() && #[trigger]
            sets[i].contains(x) implies flatten_set_seq(sets).contains(x) by {
            if i == sets.len() - 1 {
                assert(sets.last().contains(x));
                assert(flatten_set_seq(sets) == flatten_set_seq(sets.drop_last()).union(
                    sets.last(),
                ));
            } else {
                assert(0 <= i < sets.drop_last().len() && sets.drop_last()[i].contains(x));
            }
        }
    }
}

pub proof fn lemma_seq_push_to_set<A>(s: Seq<A>, x: A)
    ensures
        s.push(x).to_set() == s.to_set().insert(x),
{
    assert_sets_equal!(s.push(x).to_set() == s.to_set().insert(x), elem => {
        if elem == x {
            assert(s.push(x)[s.len() as int] == x);
            assert(s.push(x).contains(x))
        } else {
            if s.to_set().insert(x).contains(elem) {
                assert(s.to_set().contains(elem));
                let i = choose |i: int| 0 <= i < s.len() && s[i] == elem;
                assert(s.push(x)[i] == elem);
            }
        }
    });
}

pub proof fn lemma_set_map_insert<A, B>(s: Set<A>, f: FnSpec(A) -> B, x: A)
    ensures
        s.insert(x).map(f) == s.map(f).insert(f(x)),
{
    assert_sets_equal!(s.insert(x).map(f) == s.map(f).insert(f(x)), y => {
        if y == f(x) {
            assert(s.insert(x).contains(x)); // OBSERVE
            // assert(s.map(f).insert(f(x)).contains(f(x)));
        } else {
            if s.insert(x).map(f).contains(y) {
                let x0 = choose |x0| s.contains(x0) && y == f(x0);
                assert(s.map(f).contains(y));
            } else {
                if s.map(f).insert(f(x)).contains(y) {
                    let x0 = choose |x0| s.contains(x0) && y == f(x0);
                    assert(s.map(f).contains(y));
                    assert(s.insert(x).contains(x0));
                }
            }
        }
    });
}

// TODO(verus): This consequence should somehow be broadcast from map_values/map
pub proof fn lemma_seq_map_equiv<A, B>(f: FnSpec(A) -> B, g: FnSpec(int, A) -> B)
    requires
        forall|i: int, a: A| #[trigger] g(i, a) == f(a),
    ensures
        forall|s: Seq<A>| s.map_values(f) == s.map(g),
{
    assert forall|s: Seq<A>| s.map_values(f) == s.map(g) by {
        assert_seqs_equal!(s.map_values(f), s.map(g));
    }
}

pub proof fn lemma_to_set_distributes_over_addition<A>(s: Seq<A>, t: Seq<A>)
    ensures
        (s + t).to_set() == s.to_set() + t.to_set(),
{
    let left = (s + t).to_set();
    let right = s.to_set() + t.to_set();
    assert forall|x| right.contains(x) implies left.contains(x) by {
        assert(s.to_set() + t.to_set() == s.to_set().union(t.to_set()));
        if s.to_set().contains(x) {
            let si = choose|si| 0 <= si < s.len() && s[si] == x;
            assert((s + t)[si] == x);
        } else {
            let ti = choose|ti| 0 <= ti < t.len() && t[ti] == x;
            assert((s + t)[s.len() + ti] == x);
        }
    }
    assert_sets_equal!(left, right);
}

pub proof fn lemma_to_set_union_auto<A>()
    ensures
        forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set(),
{
    assert forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set() by {
        lemma_to_set_distributes_over_addition(s, t);
    }
}

spec fn map_fold<A, B>(s: Set<A>, f: FnSpec(A) -> B) -> Set<B>
    recommends
        s.finite(),
{
    set_fold(s, Set::empty(), |s1: Set<B>, a: A| s1.insert(f(a)))
}

proof fn map_fold_ok<A, B>(s: Set<A>, f: FnSpec(A) -> B)
    requires
        s.finite(),
    ensures
        map_fold(s, f) =~= s.map(f),
    decreases s.len(),
{
    if s.len() == 0 {
        return ;
    } else {
        let a = s.choose();
        map_fold_ok(s.remove(a), f);
        return ;
    }
}

proof fn map_fold_finite<A, B>(s: Set<A>, f: FnSpec(A) -> B)
    requires
        s.finite(),
    ensures
        map_fold(s, f).finite(),
    decreases s.len(),
{
    if s.len() == 0 {
        return ;
    } else {
        let a = s.choose();
        map_fold_finite(s.remove(a), f);
        return ;
    }
}

pub proof fn map_finite<A, B>(s: Set<A>, f: FnSpec(A) -> B)
    requires
        s.finite(),
    ensures
        s.map(f).finite(),
{
    map_fold_ok(s, f);
    map_fold_finite(s, f);
}

pub proof fn map_set_finite_auto<A, B>()
    ensures
        forall|s: Set<A>, f: FnSpec(A) -> B| 
            s.finite() ==> #[trigger]
            (s.map(f).finite()),
{
    assert forall|s: Set<A>, f: FnSpec(A) -> B| s.finite() implies #[trigger]
    s.map(f).finite() by {
        map_finite(s, f);
    }
}

pub proof fn lemma_to_set_singleton_auto<A>()
    ensures
        forall|x: A| #[trigger] seq![x].to_set() == set![x],
{
    assert forall|x: A| #[trigger] seq![x].to_set() =~= set![x] by {
        assert(seq![x][0] == x);
    }
}

pub proof fn lemma_map_values_singleton_auto<A, B>()
    ensures
        forall|x: A, f: FnSpec(A) -> B| #[trigger] seq![x].map_values(f) =~= seq![f(x)],
{
}

pub proof fn lemma_map_set_singleton_auto<A, B>()
    ensures
        forall|x: A, f: FnSpec(A) -> B| #[trigger] set![x].map(f) == set![f(x)],
{
    assert forall|x: A, f: FnSpec(A) -> B| #[trigger] set![x].map(f) =~= set![f(x)] by {
        assert(set![x].contains(x));
    }
}

pub proof fn lemma_map_seq_singleton_auto<A, B>()
    ensures
        forall|x: A, f: FnSpec(A) -> B| #[trigger] seq![x].map_values(f) =~= seq![f(x)],
{
}

pub proof fn flatten_sets_singleton_auto<A>()
    ensures
        forall|x: Set<A>| #[trigger] flatten_sets(set![x]) =~= x,
{
}

// TODO(Tej): We strongly suspect there is a trigger loop in these auto
// lemmas somewhere, but it's not easy to see from the profiler yet.

} // verus!

}


}
 // TODO: maybe move into Verus?

use crate::io_t::EndPoint;
use crate::io_t::NetcReceiveResult;

verus! {

// The function `unflatten_args` takes arguments passed to us by the C# main
// executable and unflattens then into a vector of arguments. C# flattens
// the arguments by contatenating them all together, and passing us an array
// of their lengths.
#[verifier(external)]
#[verus::line_count::ignore]
pub unsafe fn unflatten_args(
    num_args: i32,
    arg_lengths: *const i32,
    _total_arg_length: i32,
    flattened_args: *const u8,
) -> Vec<Vec<u8>> {
    let mut offset: isize = 0;
    let mut args: Vec<Vec<u8>> = Vec::new();
    for i in 0..num_args as isize {
        let arg_length = *arg_lengths.offset(i as isize);
        let arg_array: &[u8] = std::slice::from_raw_parts(
            flattened_args.offset(offset),
            arg_length as usize,
        );
        let arg_vec: std::vec::Vec<u8> = arg_array.to_vec();
        let mut arg: Vec<u8> = Vec::new();
        arg = arg_vec;
        args.push(arg);
        offset += arg_length as isize;
    }
    args
}

#[verifier(external)]
#[verus::line_count::ignore]
pub unsafe fn sht_main_placeholder_to_test_netclient(
    nc: &mut io_t::NetClient,
    args: &Vec<Vec<u8>>,
) {
    for i in 0..args.len() {
        println!("Command-line argument #{}: {:#?}", i+1, args[i]);
    }
    let my_end_point: EndPoint = nc.get_my_end_point();
    println!("My end point: {:#?}", my_end_point.id);
    println!("Current time is {}", nc.get_time());
    let mut message: Vec<u8> = Vec::new();
    message = "Hello, world!".as_bytes().to_vec();
    let _ = nc.send(&my_end_point, &message);
    match nc.receive(0) {
        NetcReceiveResult::Received { sender, message } => {
            println!("Received message {:#?}", message);
        },
        NetcReceiveResult::TimedOut {  } => {
            println!("Timed out");
        },
        NetcReceiveResult::Error {  } => {
            println!("Error");
        },
    }
    std::thread::sleep(std::time::Duration::from_millis(1000));
    match nc.receive(0) {
        NetcReceiveResult::Received { sender, message } => {
            println!("Received message {:#?}", message);
        },
        NetcReceiveResult::TimedOut {  } => {
            println!("Timed out");
        },
        NetcReceiveResult::Error {  } => {
            println!("Error");
        },
    }
}

// This routine is exported to the C# main executable containing the I/O
// framework. This lets the I/O framework allocate Rust buffers that it can fill
// and return to us.
//
// For instance, suppose the I/O framework is about to receive a packet, and has
// learned that packet's length. It will call `allocate_buffer`, and we'll
// return to it two things: `buffer_ptr`, a pointer to a region of memory with
// length `length`, and `box_vec_ptr`, a pointer that it will return to us when
// we ask to receive a message.
#[verifier(external)]
#[no_mangle]
#[verus::line_count::ignore]
pub unsafe extern "C" fn allocate_buffer(
    length: u64,
    box_vec_ptr: *mut *mut std::vec::Vec<u8>,
    buffer_ptr: *mut *mut u8,
) {
    // Allocate a std::vec::Vec<u8> with the given length.
    let mut v: std::vec::Vec<u8> = std::vec::Vec::<u8>::with_capacity(length as usize);
    v.set_len(length as usize);
    // Box the vector.
    let mut b: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::new(v);
    // Return the raw pointer to the vector's buffer as `*buffer_ptr`.
    *buffer_ptr = (*b).as_mut_ptr();
    // Return the raw pointer to the Box as `*box_vec_ptr`.
    *box_vec_ptr = Box::<std::vec::Vec<u8>>::into_raw(b);
}

// This routine is exported to the C# main executable containing the I/O
// framework. This lets the I/O framework deallocate a Rust buffers that
// it allocated with `allocate_buffer` that it was planning to return to
// us but has now decided it doesn't want to return to us. For instance,
// if the I/O framework allocated it to store an incoming packet, but
// detected that the connection closed, it needs to free the buffer.
#[verifier(external)]
#[verus::line_count::ignore]
#[no_mangle]
pub unsafe extern "C" fn free_buffer(box_vec_ptr: *mut std::vec::Vec<u8>) {
    // Convert back from a raw pointer to a Box so that when the Box
    // goes out of scope at the end of this function, it will be
    // freed.
    let _box_vec: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(box_vec_ptr);
}

#[verifier(external)]
#[verus::line_count::ignore]
#[no_mangle]
pub unsafe extern "C" fn sht_main_wrapper(
    num_args: i32,
    arg_lengths: *const i32,
    total_arg_length: i32,
    flattened_args: *const u8,
    get_my_end_point_func: extern "C" fn (*mut *mut std::vec::Vec<u8>),
    get_time_func: extern "C" fn () -> u64,
    receive_func: extern "C" fn (
        i32,
        *mut bool,
        *mut bool,
        *mut *mut std::vec::Vec<u8>,
        *mut *mut std::vec::Vec<u8>,
    ),
    send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
) -> i32 {
    let args: Vec<Vec<u8>> = unflatten_args(
        num_args,
        arg_lengths,
        total_arg_length,
        flattened_args,
    );
    let mut my_end_point_vec_ptr = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();
    get_my_end_point_func(my_end_point_vec_ptr.as_mut_ptr());
    let my_end_point_ptr: *mut std::vec::Vec<u8> = my_end_point_vec_ptr.assume_init();
    let my_end_point_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
        my_end_point_ptr,
    );
    let my_end_point_vec: std::vec::Vec<u8> = *my_end_point_box;
    let mut my_end_point: Vec<u8> = Vec::new();
    my_end_point = my_end_point_vec;
    let mut nc = crate::io_t::NetClient::new(
        EndPoint { id: my_end_point },
        get_time_func,
        receive_func,
        send_func,
    );
    match main_t::sht_main(nc, args) {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

} // verus!
