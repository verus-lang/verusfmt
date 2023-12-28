/*
 
#[inline]
pub fn heap_malloc()  // $line_count$Trusted$
    -> (t: (int, nat)) // $line_count$Trusted$
    requires // $line_count$Trusted$
        heap.wf(), // $line_count$Trusted$
        heap.is_in(), // $line_count$Trusted$
    ensures // $line_count$Trusted$
        local.wf(), // $line_count$Trusted$
        local.instance == old(local).instance, // $line_count$Trusted$
        ({ // $line_count$Trusted$
            let (ptr, points_to_raw, dealloc) = t; // $line_count$Trusted$
            dealloc@.wf() // $line_count$Trusted$
              && dealloc@.instance() == local.instance  // $line_count$Trusted$
              && dealloc@.size == size  // $line_count$Trusted$
        })  // $line_count$Trusted$
{
    a
}
*/

verus! {

fn heap_malloc()  // $line_count$Trusted$ 1
    -> (t: nat) // $line_count$Trusted$ 2
    requires
        true,
{
    a
}

} // verus!
