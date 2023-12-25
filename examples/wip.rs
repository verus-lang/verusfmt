verus! {

fn test() {
    match popped {
        SegmentCreating(sid) if sid == page_id.segment_id => true,
        _ => false,
    }
}

} // verus!
