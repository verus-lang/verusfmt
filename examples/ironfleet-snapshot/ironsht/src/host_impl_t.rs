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

// NB, here we have a trusted file including an untrusted file, which violates our goal
// of having the auditor need to read only _t files. This was an interim workaround due
// to some limitations of Verus traits at the time it was written, which may be resolved now.
use crate::host_impl_v::*;

verus! {

type Ios = Seq<NetEvent>;

// When this text was ported, Verus had limitations in its support for associated types or trait
// type parameters, which would have let us abstract the ConcreteConfiguration type exactly as
// IronFleet did.  As an alternative, this protocol init accepts the Args on the command line.
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
        &&& forall|i| 0 <= i < self.recvs.len() ==> self.recvs[i] is Receive
        &&& forall|i|
            0 <= i < self.clocks.len() ==> self.clocks[i] is ReadClock
                || self.clocks[i] is TimeoutReceive
        &&& forall|i| 0 <= i < self.sends.len() ==> self.sends[i] is Send
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
            netc.valid(),
    // IronFleet also gives us netc.IsOpen(), but it seems to be rotted, so we're ignoring it

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
        &&& netc.state() is Receiving  // new wrt ironfleet because we're encoding reduction rules in NetClient interface instead of by reading the history.

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
