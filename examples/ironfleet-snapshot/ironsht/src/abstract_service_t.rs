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

pub enum AppRequest {
    AppGetRequest { seqno: nat, key: AbstractKey },
    AppSetRequest { seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
}

pub enum AppReply {
    AppReply { g_seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
}

} // verus!
// verus
