verus! {

fn test() {
    for x in iter: 0..end
        invariant
            end == 10,
    {
        n += 3;
    }
    let x = 2;
    for x in iter: vec_iter_copy(v)
        invariant
            b <==> (forall|i: int| 0 <= i < iter.cur ==> v[i] > 0),
    {
        b = b && x > 0;
    }
    let y = 3;
    for x in iter: 0..({
        let z = end;
        non_spec();
        z
    })
        invariant
            n == iter.cur * 3,
            end == 10,
    {
        n += 3;
        end = end + 0;  // causes end to be non-constant
    }
}

} // verus!
