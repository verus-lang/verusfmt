
verus! {

fn test() {
    let op = |x: i32| -> (y: i32) requires x < 100000 ensures y > x { x + 1 };
}

} // verus!
