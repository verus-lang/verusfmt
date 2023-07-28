// Example that's currently being used for experimentation
verus! {

enum Enum {
    ConsIdentifier,
    ConsTupleStruct1(u32, bool, u8),
    ConsStruct2 {
        a_very_very_very_very_very_very_long_name:
            a_very_very_very_very_very_very_very_very_very_very_very_very_long_type,
        b: bool,
    },
}

} // verus!
