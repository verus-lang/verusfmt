verus! {

// TODO: Need to add support for if-let https://doc.rust-lang.org/reference/expressions/if-expr.html
fn test() {
    if let Result::Ok(val) = res {
        0
    } else {
        1
    }
}

} // verus!

/*
pub type ReplicaId = usize; // $line_count$Trusted$
*/
