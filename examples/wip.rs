verus! {

fn test() {
    let mut i: i8 = 0;
    loop
        invariant
            i <= 9,
        invariant_except_break
            i <= 9,
        invariant
            0 <= i <= 10,
        invariant_ensures
            0 <= i <= 10,
        ensures
            1 <= i,
    {
        assert(i <= 9);
        i = i + 1;
        if i == 10 {
            break ;
        }
    }
    assert(1 <= i <= 10);
}

fn test() {
    let mut i: i8 = 0;
    while true
        invariant
            i <= 9,
        invariant_except_break
            i <= 9,
        invariant
            0 <= i <= 10,
        invariant_ensures
            0 <= i <= 10,
        ensures
            1 <= i,
    {
        assert(i <= 9);
        i = i + 1;
        if i == 10 {
            break ;
        }
    }
    assert(1 <= i <= 10);
}

} // verus!
