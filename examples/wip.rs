verus! {

impl AbstractEndPoint {
    fn abstractable() {
        0
    }
    
    // TODO: attempt to translate Dafny/Distributed/Impl/Common/UdpClient.i.dfy
    // but verus EndPoint does not have IPV4 fields
    fn valid_ipv4() {
        true
    }
}

} // verus!
