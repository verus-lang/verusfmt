verus! {

fn count_size_overflow()
    ensures !x.1 ==> x.0 == count * size
{
    true
}

} // verus!
