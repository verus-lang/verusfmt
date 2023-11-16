verus! {

#[allow(unused_macros)]
macro_rules! no_usize_overflows {
  ($e:expr,) => {
    true
  };
  ($($e:expr),*) => {
    no_usize_overflows!(@@internal 0, $($e),*)
  };
  (@@internal $total:expr,) => {
    true
  };
  (@@internal $total:expr, $a:expr) => {
    usize::MAX - $total >= $a
  };
  (@@internal $total:expr, $a:expr, $($rest:expr),*) => {
    usize::MAX - $total >= $a
      &&
    no_usize_overflows!(@@internal ($total + $a), $($rest),*)
  };
}

} // verus!
