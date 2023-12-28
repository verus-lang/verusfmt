verus! {

pub exec const MASK_L1_PG_ADDR: u64 ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1)
}

} // verus!
