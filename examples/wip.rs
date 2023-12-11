verus! {

spec fn host_ignoring_unparseable(pre: AbstractHostState, post: AbstractHostState) -> bool {
    post == AbstractHostState { received_packet: None, ..pre }
}

} // verus!
