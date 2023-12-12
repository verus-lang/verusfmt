verus! {

fn test() {
    match m {
        CMessage::LongConstructorNameGetRequest{..} => old_self.long_function_next_get_request_preconditions(),
    }

    fn len<T>(l: List<T>) -> nat {
        match l {
            List::Nil => 0,
            List::Cons(_, tl) => 1 + len(*tl),
        }
    }

    fn uses_is(t: ThisOrThat) {
         match t {
            ThisOrThat::This(..) => assert(t),
            ThisOrThat::That{..} => assert(t),
         }
    }
}

} // verus!
