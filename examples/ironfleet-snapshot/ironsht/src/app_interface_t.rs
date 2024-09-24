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
