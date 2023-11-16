verus! {

pub fn clone_vec_u8() {
    let i = 0;
    while i < v.len() 
        invariant
            i <= v.len(),
            i == out.len(),
            forall|j| #![auto] 0 <= j < i ==> out@[j] == v@[j],
        ensures
            i > 0,
        decreases 72,
    {
        i = i + 1;
    }
}

} // verus!
