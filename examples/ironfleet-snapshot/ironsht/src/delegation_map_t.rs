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
