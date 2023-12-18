verus! {

fn test() {
    loop
        invariant
            x > 0,
    {
        x += 1;
    }

}

} // verus!

/*
pub type ReplicaId = usize; // $line_count$Trusted$
*/
