#![verus::trusted]
//! Wrapper around Rust HashMap with Vec<u8> keys, with a Map view
//!
//! This is a copy-paste of hashmap_t.rs but for HashMap<Vec<u8>, V>.
//! At the time this was written, that's because Verus generics had some
//! limitations; those limitations may already resolved now.

use std::collections;
use vstd::map::*;
use vstd::prelude::*;

use crate::abstract_end_point_t::AbstractEndPoint;
use crate::io_t::EndPoint;

verus! {

#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct HashMap<V> {
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
        new_map_v == old_map_v.insert(
            key,
            value,
        )
        //         &&& new_map_v.contains_key(key)
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
