verus! {

pub fn test() {
    let Some((key, val)) = cur else { 
        panic!() /* covered by while condition */ 
    };
    
    let Some((key, val)) = cur else { panic!() };
}


} // verus!
