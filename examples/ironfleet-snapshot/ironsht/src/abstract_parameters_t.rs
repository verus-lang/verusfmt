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
