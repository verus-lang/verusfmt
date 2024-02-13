verus! {

fn borrow_join<'a>(tracked &'a self) {
    2
}

fn borrow_join2<'a>(tracked &'a self, x: u32) {
    2
}

} // verus!
