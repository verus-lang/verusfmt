verus! {

#[verifier(external_body)]
pub struct NetClientCPointers {
    get_time_func: extern "C" fn() -> u64,
    receive_func: extern "C" fn(i32, *mut bool, *mut bool, *mut *mut std::vec::Vec<u8>, *mut *mut std::vec::Vec<u8>),
    send_func: extern "C" fn(u64, *const u8, u64, *const u8) -> bool
}


} // verus!
