verus! {

enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}
fn len<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
    }
}

} // verus!
