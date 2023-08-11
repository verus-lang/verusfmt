verus! {

pub fn test_function() -> u32 {
    let x = if b { 5 } else { 10 };
    let u = MyStruct { x: 2, y: 3 };
    if b {
        a();
    } else {
        b();
    };
    5
}

} // verus!
