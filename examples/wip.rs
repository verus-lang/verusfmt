verus! {

fn test_ghost_unwrap(x: int)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        y < 100,
{
}

fn test_ghost_unwrap(
    x: u32,
    y: very_very_very_very_very_long_type,
)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        x < 100,
{
}

} // verus!
