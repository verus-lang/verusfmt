verus! {

fn macro_calls() {
    println!("{} {} {}", very_very_very_very_very_very_long_e1 + 42, very_very_very_very_very_very_long_e2, very_very_very_very_very_very_long_e3);
    unknown_macro1!("{} {} {}", very_very_very_very_very_very_long_e1, very_very_very_very_very_very_long_e2, very_very_very_very_very_very_long_e3);
    unknown_macro2!("
        intro h1;
        simpl;
        cong;
        done;
    ");
}

} // verus!
