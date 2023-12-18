verus! {

global size_of usize == 4;

global size_of S == 8;

global size_of S<u64> == 8;

global size_of S<U> == 8;

global layout S is size == 8, align == 8;

global layout S<u64> is size == 16, align == 8;

global layout S<u32> is size == 8, align == 4;

} // verus!
