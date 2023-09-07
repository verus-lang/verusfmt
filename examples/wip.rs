verus! {

pub fn test_function<A, B, C>(a: u32, b: bool, c: LongTypeName) -> u32 {
    let _ = { a_call() };
    let _ = unsafe { a_call() };
    let _ = {
        a_call();
        b
    };
    unsafe {
        a_call();
    };
    let x = 5;
    a
}
pub fn test() -> bool {
    let z = {
        let k = 5;
        k
    };
}
pub fn test() -> bool {
    {
        let y = 7;
        b
    }
}
pub fn test() -> bool {
    unsafe {
        let x = 5;
        x
    }
}

pub fn test_function(x: bool, y: bool) -> u32
    requires
        x,
        y,
{
    5
}

} // verus!
