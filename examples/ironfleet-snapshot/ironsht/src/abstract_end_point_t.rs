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
