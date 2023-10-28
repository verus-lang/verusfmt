verus! {

fn test_function() {
    let (mut stream, _addr) = listener.accept().unwrap();
    match len_valid_owl_Result(&(*arg.data).as_slice()) {
        Some(l) => {
            arg.parsing_outcome = owl_Result_ParsingOutcome::Success;
        },
        None => {
            arg.data = rc_new(vec_u8_from_elem(0, 1));
            arg.parsing_outcome = owl_Result_ParsingOutcome::Failure;
        },
    }
}

} // verus!
