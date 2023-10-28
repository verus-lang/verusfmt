verus! {

fn test_function() {
    if y {
        1
    } else if x {
        2
    } else {
        3
    }
}

fn test_function() {
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else if x > 0 {
        2 + test_rec2(x - 1, 100)
    } else {
        3
    }
}

} // verus!
