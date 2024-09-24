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
        netc.state() is Receiving,
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
            ok ==> netc.state() is Receiving,
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
