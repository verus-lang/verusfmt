// Example that's currently being used for experimentation
verus! {

pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let f = || true;
    let g = |x, y| x;
    let h = |x, y, z: int| {
        let w = y;
        let u = w;
        u
    };
    let i = |x| unsafe {
        let y = x;
        y
    };
}

} // verus!
