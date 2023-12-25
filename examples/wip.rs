verus! {

fn has_new_pointsto() {
    (forall |addr: int| mem_protect == MemProtect { read: true })
}

fn foo()
    ensures forall|x:int| x == x
{
}

} // verus!
