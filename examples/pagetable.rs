#![feature(nonnull_slice_from_raw_parts)]
extern crate alloc;

pub mod impl_u {
    pub mod l0 {
        #![allow(unused_imports)]
        use crate::definitions_t::{
            aligned, between, overlap, Arch, Flags, MemRegion, PageTableEntry,
        };
        use crate::extra as lib;
        use builtin::*;
        use builtin_macros::*;
        use vstd::map::*;
        use vstd::modes::*;
        use vstd::option::{Option::*, *};
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::set::*;
        use vstd::set_lib::*;

        verus! {

#[verifier(nonlinear)]
pub proof fn ambient_arith()
    ensures
        forall|a: nat, b: nat| a == 0 ==> #[trigger] (a * b) == 0,
        forall|a: nat, b: nat| b == 0 ==> #[trigger] (a * b) == 0,
        forall|a: nat, b: nat| a > 0 && b > 0 ==> #[trigger] (a * b) > 0,
        forall|a: int, b: int| #[trigger] (a * b) == (b * a),
        forall|a: nat| a != 0 ==> aligned(0, a),
{
    lib::aligned_zero();
}

pub proof fn ambient_lemmas1()
    ensures
        forall|s1: Map<nat, PageTableEntry>, s2: Map<nat, PageTableEntry>|
            s1.dom().finite() && s2.dom().finite() ==> #[trigger] s1.union_prefer_right(
                s2,
            ).dom().finite(),
        forall|a: int, b: int| #[trigger] (a * b) == b * a,
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat|
            (m1.dom().contains(n) && !m2.dom().contains(n)) ==> equal(
                m1.remove(n).union_prefer_right(m2),
                m1.union_prefer_right(m2).remove(n),
            ),
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat|
            (m2.dom().contains(n) && !m1.dom().contains(n)) ==> equal(
                m1.union_prefer_right(m2.remove(n)),
                m1.union_prefer_right(m2).remove(n),
            ),
        forall|
            m1: Map<nat, PageTableEntry>,
            m2: Map<nat, PageTableEntry>,
            n: nat,
            v: PageTableEntry,
        |
            (!m1.dom().contains(n) && !m2.dom().contains(n)) ==> equal(
                m1.insert(n, v).union_prefer_right(m2),
                m1.union_prefer_right(m2).insert(n, v),
            ),
        forall|
            m1: Map<nat, PageTableEntry>,
            m2: Map<nat, PageTableEntry>,
            n: nat,
            v: PageTableEntry,
        |
            (!m1.dom().contains(n) && !m2.dom().contains(n)) ==> equal(
                m1.union_prefer_right(m2.insert(n, v)),
                m1.union_prefer_right(m2).insert(n, v),
            ),
// forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().upper == d.upper_vaddr())),
// forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().lower == d.base_vaddr)),

{
    lemma_finite_map_union::<nat, PageTableEntry>();
    // assert_nonlinear_by({ ensures(forall|d: Directory| equal(d.num_entries() * d.entry_size(), d.entry_size() * d.num_entries())); });
    // assert_forall_by(|d: Directory, i: nat| {
    //     requires(#[auto_trigger] d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
    //     ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
    //     assert(d.directories_obey_invariant());
    // });
    lemma_map_union_prefer_right_remove_commute::<nat, PageTableEntry>();
    lemma_map_union_prefer_right_insert_commute::<nat, PageTableEntry>();
    assert(forall|a: int, b: int| #[trigger] (a * b) == b * a) by (nonlinear_arith){};
}

pub struct PageTableContents {
    pub map: Map<nat  /* VAddr */ , PageTableEntry>,
    pub arch: Arch,
    pub lower: nat,
    pub upper: nat,
}

impl PageTableContents {
    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.map.dom().finite()
        &&& self.arch.inv()
        &&& self.mappings_are_of_valid_size()
        &&& self.mappings_are_aligned()
        &&& self.mappings_dont_overlap()
        &&& self.mappings_in_bounds()
    }

    pub open spec(checked) fn mappings_are_of_valid_size(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).frame.size]
            #![trigger self.map.index(va).frame.base]
            self.map.dom().contains(va) ==> self.arch.contains_entry_size(
                self.map.index(va).frame.size,
            )
    }

    pub open spec(checked) fn mappings_are_aligned(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).frame.size]
            #![trigger self.map.index(va).frame.base]
            self.map.dom().contains(va) ==> aligned(va, self.map.index(va).frame.size) && aligned(
                self.map.index(va).frame.base,
                self.map.index(va).frame.size,
            )
    }

    pub open spec(checked) fn mappings_dont_overlap(self) -> bool {
        forall|b1: nat, b2: nat|
            #![trigger self.map[b1], self.map[b2]]
            #![trigger self.map.dom().contains(b1), self.map.dom().contains(b2)]
            self.map.dom().contains(b1) && self.map.dom().contains(b2) ==> ((b1 == b2) || !overlap(
                MemRegion { base: b1, size: self.map[b1].frame.size },
                MemRegion { base: b2, size: self.map[b2].frame.size },
            ))
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(
        self,
        base: nat,
        pte: PageTableEntry,
    ) -> bool {
        self.lower <= base && base + pte.frame.size <= self.upper
    }

    pub open spec(checked) fn mappings_in_bounds(self) -> bool {
        forall|b1: nat|
            #![trigger self.map[b1]]
            #![trigger self.map.dom().contains(b1)]
            #![trigger self.candidate_mapping_in_bounds(b1, self.map[b1])]
            self.map.dom().contains(b1) ==> self.candidate_mapping_in_bounds(b1, self.map[b1])
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PageTableEntry) -> bool {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size(pte.frame.size)
    }

    pub open spec(checked) fn valid_mapping(self, base: nat, pte: PageTableEntry) -> bool {
        forall|b: nat|
            #![auto]
            self.map.dom().contains(b) ==> !overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: b, size: self.map.index(b).frame.size },
            )
    }

    /// Maps the given `pte` at `base` in the address space
    pub open spec(checked) fn map_frame(self, base: nat, pte: PageTableEntry) -> Result<
        PageTableContents,
        PageTableContents,
    > {
        if self.accepted_mapping(base, pte) {
            if self.valid_mapping(base, pte) {
                Ok(PageTableContents { map: self.map.insert(base, pte), ..self })
            } else {
                Err(self)
            }
        } else {
            arbitrary()
        }
    }

    proof fn map_frame_preserves_inv(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(
                base,
                pte,
            ),
    // self.map_frame(base, frame).is_Ok(),

        ensures
            self.map_frame(base, pte).is_Ok() ==> self.map_frame(base, pte).get_Ok_0().inv(),
            self.map_frame(base, pte).is_Err() ==> self.map_frame(base, pte).get_Err_0() === self,
    {
        if self.map_frame(base, pte).is_Ok() {
            let nself = self.map_frame(base, pte).get_Ok_0();
            assert(nself.mappings_in_bounds());
        }
    }

    pub open spec(checked) fn accepted_resolve(self, vaddr: nat) -> bool {
        between(vaddr, self.lower, self.upper)
    }

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    pub open spec(checked) fn resolve(self, vaddr: nat) -> Result<(nat, PageTableEntry), ()>
        recommends
            self.accepted_resolve(vaddr),
    {
        if exists|base: nat, pte: PageTableEntry|
            self.map.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size) {
            let (base, pte) = choose|base: nat, pte: PageTableEntry|
                self.map.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            Ok((base, pte))
        } else {
            Err(())
        }
    }

    pub open spec(checked) fn remove(self, n: nat) -> PageTableContents {
        PageTableContents { map: self.map.remove(n), ..self }
    }

    pub open spec(checked) fn accepted_unmap(self, base: nat) -> bool {
        &&& between(base, self.lower, self.upper)
        &&& exists|size: nat|
            #![trigger self.arch.contains_entry_size(size)]
            #![trigger aligned(base, size)]
            self.arch.contains_entry_size(size) && aligned(base, size)
    }

    /// Removes the frame from the address space that contains `base`.
    pub open spec(checked) fn unmap(self, base: nat) -> Result<PageTableContents, PageTableContents>
        recommends
            self.accepted_unmap(base),
    {
        if self.map.dom().contains(base) {
            Ok(self.remove(base))
        } else {
            Err(self)
        }
    }

    proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
        ensures
            self.unmap(base).is_Ok() ==> self.unmap(base).get_Ok_0().inv(),
            self.unmap(base).is_Err() ==> self.unmap(base).get_Err_0() === self,
    ;

    pub proof fn lemma_unmap_decrements_len(self, base: nat)
        requires
            self.inv(),
            self.unmap(base).is_Ok(),
        ensures
            self.map.dom().len() > 0,
            equal(self.unmap(base).get_Ok_0().map.dom(), self.map.dom().remove(base)),
            self.unmap(base).get_Ok_0().map.dom().len() == self.map.dom().len() - 1,
    {
        assert(self.map.dom().contains(base));
        lemma_set_contains_IMP_len_greater_zero::<nat>(self.map.dom(), base);
    }

    pub open spec fn ranges_disjoint(self, other: Self) -> bool {
        if self.lower <= other.lower {
            self.upper <= other.lower
        } else {
            // other.lower < self.lower
            other.upper <= self.lower
        }
    }

    pub open spec fn mappings_disjoint(self, other: Self) -> bool {
        forall|s: nat, o: nat|
            self.map.dom().contains(s) && other.map.dom().contains(o) ==> !overlap(
                MemRegion { base: s, size: self.map.index(s).frame.size },
                MemRegion { base: o, size: other.map.index(o).frame.size },
            )
    }

    pub proof fn lemma_ranges_disjoint_implies_mappings_disjoint(self, other: Self)
        requires
            self.inv(),
            other.inv(),
            self.ranges_disjoint(other),
        ensures
            self.mappings_disjoint(other),
    ;

    proof fn lemma_mappings_have_positive_entry_size(self)
        requires
            self.inv(),
        ensures
            forall|va: nat| #[trigger]
                self.map.dom().contains(va) ==> self.map.index(va).frame.size > 0,
    ;
}

// TODO: move
pub proof fn lemma_set_contains_IMP_len_greater_zero<T>(s: Set<T>, a: T)
    requires
        s.finite(),
        s.contains(a),
    ensures
        s.len() > 0,
{
    if s.len() == 0 {
        // contradiction
        assert(s.remove(a).len() + 1 == 0);
    }
}

pub proof fn lemma_map_union_prefer_right_insert_commute<S, T>()
    ensures
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            !m1.dom().contains(n) && !m2.dom().contains(n) ==> equal(
                m1.insert(n, v).union_prefer_right(m2),
                m1.union_prefer_right(m2).insert(n, v),
            ),
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            !m1.dom().contains(n) && !m2.dom().contains(n) ==> equal(
                m1.union_prefer_right(m2.insert(n, v)),
                m1.union_prefer_right(m2).insert(n, v),
            ),
{
    assert_forall_by(
        |m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            {
                requires(!m1.dom().contains(n) && !m2.dom().contains(n));
                ensures(
                    equal(
                        m1.insert(n, v).union_prefer_right(m2),
                        m1.union_prefer_right(m2).insert(n, v),
                    ),
                );
                let union1 = m1.insert(n, v).union_prefer_right(m2);
                let union2 = m1.union_prefer_right(m2).insert(n, v);
                assert_maps_equal!(union1, union2);
                assert(equal(union1, union2));
            },
    );
    assert_forall_by(
        |m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            {
                requires(!m1.dom().contains(n) && !m2.dom().contains(n));
                ensures(
                    equal(
                        m1.union_prefer_right(m2.insert(n, v)),
                        m1.union_prefer_right(m2).insert(n, v),
                    ),
                );
                let union1 = m1.union_prefer_right(m2.insert(n, v));
                let union2 = m1.union_prefer_right(m2).insert(n, v);
                assert_maps_equal!(union1, union2);
                assert(equal(union1, union2));
            },
    );
}

pub proof fn lemma_map_union_prefer_right_remove_commute<S, T>()
    ensures
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S|
            m1.dom().contains(n) && !m2.dom().contains(n) ==> equal(
                m1.remove(n).union_prefer_right(m2),
                m1.union_prefer_right(m2).remove(n),
            ),
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S|
            m2.dom().contains(n) && !m1.dom().contains(n) ==> equal(
                m1.union_prefer_right(m2.remove(n)),
                m1.union_prefer_right(m2).remove(n),
            ),
{
    assert_forall_by(
        |m1: Map<S, T>, m2: Map<S, T>, n: S|
            {
                requires(m1.dom().contains(n) && !m2.dom().contains(n));
                ensures(
                    equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)),
                );
                let union1 = m1.remove(n).union_prefer_right(m2);
                let union2 = m1.union_prefer_right(m2).remove(n);
                assert_maps_equal!(union1, union2);
                assert(equal(union1, union2));
                // TODO: verus bug? (uncomment assertions below)
                // substituting union1 and/or union2's definition makes the assertion fail:
                // assert(equal(m1.remove(n).union_prefer_right(m2), union2));
                // assert(equal(union1, m1.union_prefer_right(m2).remove(n)));
            },
    );
    assert_forall_by(
        |m1: Map<S, T>, m2: Map<S, T>, n: S|
            {
                requires(m2.dom().contains(n) && !m1.dom().contains(n));
                ensures(
                    equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)),
                );
                let union1 = m1.union_prefer_right(m2.remove(n));
                let union2 = m1.union_prefer_right(m2).remove(n);
                assert_maps_equal!(union1, union2);
                assert(equal(union1, union2));
            },
    );
}

// TODO: should go somewhere else
pub proof fn lemma_finite_map_union<S, T>()
    ensures
        forall|s1: Map<S, T>, s2: Map<S, T>|
            s1.dom().finite() && s2.dom().finite() ==> #[trigger] s1.union_prefer_right(
                s2,
            ).dom().finite(),
{
    assert_forall_by(
        |s1: Map<S, T>, s2: Map<S, T>|
            {
                requires(s1.dom().finite() && s2.dom().finite());
                ensures((#[trigger] s1.union_prefer_right(s2)).dom().finite());
                assert(s1.dom().union(s2.dom()).finite());
                let union_dom = s1.union_prefer_right(s2).dom();
                let dom_union = s1.dom().union(s2.dom());
                assert(forall|s: S| union_dom.contains(s) ==> dom_union.contains(s));
                assert(forall|s: S| dom_union.contains(s) ==> union_dom.contains(s));
                assert_sets_equal!(union_dom, dom_union);
            },
    );
}

} // verus!
}

    pub mod l1 {
        #![allow(unused_imports)]
        use crate::definitions_t::new_seq;
        use crate::definitions_u::lemma_new_seq;
        use crate::extra as lib;
        use crate::impl_u::indexing;
        use builtin::*;
        use builtin_macros::*;
        use vstd::map::*;
        use vstd::modes::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::seq_lib::*;
        use vstd::set::*;
        use vstd::set_lib::*;

        use crate::definitions_t::{
            aligned, between, overlap, Arch, Flags, MemRegion, PageTableEntry,
        };
        use crate::definitions_u::permissive_flags;
        use crate::impl_u::l0::{self, ambient_arith, ambient_lemmas1};

        verus! {

pub proof fn ambient_lemmas2()
    ensures
        forall|d: Directory, i: nat|
            #![trigger d.inv(), d.entries.index(i as int)]
            d.inv() && i < d.num_entries() && d.entries.index(i as int).is_Directory()
                ==> d.entries.index(i as int).get_Directory_0().inv(),
        forall|d: Directory| d.inv() ==> (#[trigger] d.interp()).upper == d.upper_vaddr(),
        forall|d: Directory| d.inv() ==> (#[trigger] d.interp()).lower == d.base_vaddr,
{
    assert forall|d: Directory, i: nat|
        #![auto]
        d.inv() && i < d.num_entries() && d.entries.index(
            i as int,
        ).is_Directory() implies d.entries.index(i as int).get_Directory_0().inv() by {
        assert(d.directories_obey_invariant());
    };
    assert forall|d: Directory| #![auto] d.inv() implies d.interp().upper == d.upper_vaddr()
        && d.interp().lower == d.base_vaddr by {
        d.lemma_inv_implies_interp_inv();
    };
}

// Simply uncommenting this thing slows down verification of this file by 2.5x
// #[proof]
// fn ambient_lemmas3() {
//     ensures([
//             forall(|d: Directory, base: nat, pte: PageTableEntry|
//                    d.inv() && #[trigger] d.accepted_mapping(base, pte) ==>
//                    d.interp().accepted_mapping(base, pte)),
//     ]);
//     assert_forall_by(|d: Directory, base: nat, pte: PageTableEntry| {
//         requires(d.inv() && #[trigger] d.accepted_mapping(base, pte));
//         ensures(d.interp().accepted_mapping(base, pte));
//         d.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
//     });
// }
#[is_variant]
pub enum NodeEntry {
    Directory(Directory),
    Page(PageTableEntry),
    Empty(),
}

pub struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat,  // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
    pub flags: Flags,
}

// Layer 0: 425 Directory ->
// Layer 1: 47  Directory ->
// Layer 2: 5   Page (1K)
// Layer 1: 46  Directory -> (1M)
// Layer 2: 1024 Pages
// Layer 0: 1024 Directories (1T)
// Layer 1: 1024 Directories (1G)
// Layer 2: 1024 Pages
impl Directory {
    pub open spec(checked) fn well_formed(&self) -> bool {
        &&& self.arch.inv()
        &&& self.layer < self.arch.layers.len()
        &&& aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        &&& self.entries.len() == self.num_entries()
        &&& self.flags == permissive_flags
    }

    pub open spec(checked) fn entry_size(&self) -> nat
        recommends
            self.layer < self.arch.layers.len(),
    {
        self.arch.entry_size(self.layer)
    }

    pub open spec(checked) fn num_entries(&self) -> nat  // number of entries

        recommends
            self.layer < self.arch.layers.len(),
    {
        self.arch.num_entries(self.layer)
    }

    pub open spec(checked) fn empty(&self) -> bool
        recommends
            self.well_formed(),
    {
        forall|i: nat| i < self.num_entries() ==> self.entries.index(i as int).is_Empty()
    }

    pub open spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends
            self.well_formed(),
    {
        forall|i: nat|
            (i < self.entries.len() && self.entries[i as int].is_Page()) ==> (
            #[trigger] self.entries[i as int].get_Page_0().frame.size) == self.entry_size()
    }

    pub open spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends
            self.well_formed(),
    {
        forall|i: nat|
            i < self.entries.len() && self.entries.index(i as int).is_Directory() ==> {
                let directory = #[trigger] self.entries[i as int].get_Directory_0();
                &&& directory.layer == self.layer + 1
                &&& directory.base_vaddr == self.base_vaddr + i * self.entry_size()
            }
    }

    pub open spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases self.arch.layers.len() - self.layer, 0nat,
    {
        if self.well_formed() && self.directories_are_in_next_layer()
            && self.directories_match_arch() {
            forall|i: nat|
                (i < self.entries.len() && self.entries[i as int].is_Directory()) ==> (
                #[trigger] self.entries[i as int].get_Directory_0()).inv()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn directories_match_arch(&self) -> bool {
        forall|i: nat|
            (i < self.entries.len() && self.entries.index(i as int).is_Directory()) ==> (
            #[trigger] self.entries.index(i as int).get_Directory_0().arch) == self.arch
    }

    pub open spec fn directories_are_nonempty(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
    {
        forall|i: nat|
            i < self.entries.len() && self.entries.index(i as int).is_Directory() ==> !(
            #[trigger] self.entries.index(i as int).get_Directory_0().empty())
    }

    pub open spec(checked) fn frames_aligned(&self) -> bool
        recommends
            self.well_formed(),
    {
        forall|i: nat|
            i < self.entries.len() && self.entries.index(i as int).is_Page() ==> aligned(
                (#[trigger] self.entries.index(i as int).get_Page_0()).frame.base,
                self.entry_size(),
            )
    }

    pub open spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer,
    {
        &&& self.well_formed()
        &&& self.pages_match_entry_size()
        &&& self.directories_are_in_next_layer()
        &&& self.directories_match_arch()
        &&& self.directories_obey_invariant()
        &&& self.directories_are_nonempty()
        &&& self.frames_aligned()
    }

    pub open spec(checked) fn interp(self) -> l0::PageTableContents {
        self.interp_aux(0)
    }

    pub open spec(checked) fn upper_vaddr(self) -> nat
        recommends
            self.well_formed(),
    {
        self.arch.upper_vaddr(self.layer, self.base_vaddr)
    }

    pub open spec fn index_for_vaddr(self, vaddr: nat) -> nat {
        self.arch.index_for_vaddr(self.layer, self.base_vaddr, vaddr)
    }

    pub open spec(checked) fn entry_base(self, idx: nat) -> nat
        recommends
            self.inv(),
    {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec(checked) fn next_entry_base(self, idx: nat) -> nat
        recommends
            self.inv(),
    {
        self.arch.next_entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn entry_bounds(self, entry: nat) -> (nat, nat) {
        (self.entry_base(entry), self.entry_base(entry + 1))
    }

    pub open spec fn interp_of_entry(self, entry: nat) -> l0::PageTableContents
        decreases self.arch.layers.len() - self.layer, self.num_entries() - entry, 0nat,
    {
        if self.inv() && entry < self.entries.len() {
            let (lower, upper) = self.entry_bounds(entry);
            l0::PageTableContents {
                map: match self.entries.index(entry as int) {
                    NodeEntry::Page(p) => map![self.entry_base(entry) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty() => map![],
                },
                arch: self.arch,
                lower,
                upper,
            }
        } else {
            arbitrary()
        }
    }

    proof fn lemma_interp_of_entry(self)
        requires
            self.inv(),
        ensures
            forall|i: nat|
                #![auto]
                i < self.num_entries() ==> self.interp_of_entry(i).inv() && self.interp_of_entry(
                    i,
                ).lower == self.entry_base(i) && self.interp_of_entry(i).upper == self.entry_base(
                    i + 1,
                ) && (forall|base: nat|
                    self.interp_of_entry(i).map.dom().contains(base) ==> between(
                        base,
                        self.entry_base(i),
                        self.entry_base(i + 1),
                    )) && (forall|base: nat, pte: PageTableEntry|
                    self.interp_of_entry(i).map.contains_pair(base, pte) ==> between(
                        base,
                        self.entry_base(i),
                        self.entry_base(i + 1),
                    )),
    {
        assert forall|i: nat| #![auto] i < self.num_entries() implies self.interp_of_entry(i).inv()
            && self.interp_of_entry(i).lower == self.entry_base(i) && self.interp_of_entry(i).upper
            == self.entry_base(i + 1) by {
            self.lemma_inv_implies_interp_of_entry_inv(i);
        };
    }

    proof fn lemma_inv_implies_interp_of_entry_inv(self, i: nat)
        requires
            self.inv(),
            i < self.num_entries(),
        ensures
            self.interp_of_entry(i).inv(),
            self.interp_of_entry(i).lower == self.entry_base(i),
            self.interp_of_entry(i).upper == self.entry_base(i + 1),
    {
        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, i, self.entry_size());
        if let NodeEntry::Directory(d) = self.entries[i as int] {
            d.lemma_inv_implies_interp_inv();
        }
    }

    proof fn lemma_interp_of_entries_disjoint(self)
        requires
            self.inv(),
        ensures
            forall|i: nat, j: nat|
                i < self.num_entries() && j < self.num_entries() && i != j ==> self.interp_of_entry(
                    i,
                ).ranges_disjoint(self.interp_of_entry(j)),
    {
        assert forall|i: nat, j: nat|
            i < self.num_entries() && j < self.num_entries() && i != j implies self.interp_of_entry(
            i,
        ).ranges_disjoint(self.interp_of_entry(j)) by {
            if i < j {
                assert(self.base_vaddr + i * self.entry_size() <= self.base_vaddr + j
                    * self.entry_size()) by (nonlinear_arith)
                    requires
                        self.inv() && i < j && self.entry_size() > 0,
                {};
                assert(self.base_vaddr + (i + 1) * self.entry_size() <= self.base_vaddr + j
                    * self.entry_size()) by (nonlinear_arith)
                    requires
                        self.inv() && i < j && self.entry_size() > 0,
                {};
            } else {
                assert(self.base_vaddr + j * self.entry_size() < self.base_vaddr + i
                    * self.entry_size()) by (nonlinear_arith)
                    requires
                        self.inv() && j < i && self.entry_size() > 0,
                {};
                assert(self.base_vaddr + (j + 1) * self.entry_size() <= self.base_vaddr + i
                    * self.entry_size()) by (nonlinear_arith)
                    requires
                        self.inv() && j < i && self.entry_size() > 0,
                {};
            }
        }
    }

    pub open spec fn interp_aux(self, i: nat) -> l0::PageTableContents
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i, 1nat,
    {
        if self.inv() {
            if i >= self.entries.len() {
                l0::PageTableContents {
                    map: map![],
                    arch: self.arch,
                    lower: self.upper_vaddr(),
                    upper: self.upper_vaddr(),
                }
            } else {  // i < self.entries.len()
                let rem = self.interp_aux(i + 1);
                let entry_i = self.interp_of_entry(i);
                l0::PageTableContents {
                    map: rem.map.union_prefer_right(entry_i.map),
                    arch: self.arch,
                    lower: entry_i.lower,
                    upper: rem.upper,
                }
            }
        } else {
            arbitrary()
        }
    }

    pub proof fn lemma_inv_implies_interp_inv(self)
        requires
            self.inv(),
        ensures
            self.interp().inv(),
            self.interp().upper == self.upper_vaddr(),
            self.interp().lower == self.base_vaddr,
    {
        self.lemma_inv_implies_interp_aux_inv(0);
    }

    pub proof fn lemma_inv_implies_interp_aux_inv(self, i: nat)
        requires
            self.inv(),
        ensures
            self.interp_aux(i).inv(),
            i <= self.entries.len() ==> self.interp_aux(i).lower == self.entry_base(i),
            self.interp_aux(i).upper == self.upper_vaddr(),
            i == 0 ==> self.interp_aux(0).lower == self.base_vaddr,
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        ambient_lemmas1();
        let interp = self.interp_aux(i);
        if i >= self.entries.len() {
        } else {
            assert(i < self.entries.len());
            self.lemma_inv_implies_interp_aux_inv(i + 1);
            assert(self.directories_obey_invariant());
            let entry = self.entries.index(i as int);
            let entry_i = self.interp_of_entry(i);
            let rem = self.interp_aux(i + 1);
            match entry {
                NodeEntry::Page(p) => {},
                NodeEntry::Directory(d) => {
                    d.lemma_inv_implies_interp_aux_inv(0);
                },
                NodeEntry::Empty() => {},
            }
            assert(interp.mappings_are_of_valid_size());
            if let NodeEntry::Page(pte) = entry {
                indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
                indexing::lemma_entry_base_from_index_support(
                    self.base_vaddr,
                    i,
                    self.entry_size(),
                );
            }
            assert(interp.mappings_are_aligned());
            match entry {
                NodeEntry::Page(pte) => {
                    assert_nonlinear_by(
                        {
                            requires(
                                [
                                    self.inv(),
                                    equal(entry_i, self.interp_of_entry(i)),
                                    self.entry_size() == pte.frame.size,
                                    i < self.entries.len(),
                                ],
                            );
                            ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), pte));
                        },
                    );
                },
                NodeEntry::Directory(d) => {
                    assert_nonlinear_by(
                        {
                            requires(
                                [
                                    self.inv(),
                                    equal(entry_i, self.interp_of_entry(i)),
                                    d.interp_aux(0).inv(),
                                    d.interp_aux(0).lower == self.entry_base(i),
                                    d.base_vaddr == self.entry_base(i),
                                    d.entry_size() * d.num_entries() == self.entry_size(),
                                    d.interp_aux(0).upper == d.upper_vaddr(),
                                    equal(self.interp_of_entry(i).map, d.interp_aux(0).map),
                                    i < self.entries.len(),
                                ],
                            );
                            ensures(entry_i.mappings_in_bounds());
                            assert(self.well_formed());
                            assert(entry_i.lower <= d.interp_aux(0).lower);  // proof stability
                            assert(entry_i.upper >= d.interp_aux(0).upper);  // proof stability
                        },
                    );
                },
                NodeEntry::Empty() => {},
            }
            assert(entry_i.mappings_in_bounds());
            assert(entry_i.inv());
            assert(self.interp_aux(i + 1).lower == self.entry_base(i + 1));
            assert_nonlinear_by(
                {
                    requires(
                        [
                            self.inv(),
                            equal(rem, self.interp_aux(i + 1)),
                            equal(entry_i, self.interp_of_entry(i)),
                            self.interp_aux(i + 1).lower == self.entry_base(i + 1),
                        ],
                    );
                    ensures(rem.ranges_disjoint(entry_i));
                },
            );
            rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);
            assert(interp.mappings_dont_overlap());
            assert_nonlinear_by(
                {
                    requires(
                        [
                            equal(interp, self.interp_aux(i)),
                            equal(entry_i, self.interp_of_entry(i)),
                            equal(rem, self.interp_aux(i + 1)),
                            self.interp_aux(i + 1).lower == self.entry_base(i + 1),
                            entry_i.upper == self.entry_base(i + 1),
                            interp.upper == self.upper_vaddr(),
                        ],
                    );
                    ensures(
                        [
                            interp.lower <= entry_i.lower,
                            interp.upper >= entry_i.upper,
                            interp.lower <= self.interp_aux(i + 1).lower,
                            interp.upper >= self.interp_aux(i + 1).upper,
                        ],
                    );
                },
            );
            assert(interp.mappings_in_bounds());
            assert(interp.map.dom().finite());
            if i == 0 {
                assert_nonlinear_by(
                    {
                        requires(
                            [
                                equal(entry_i, self.interp_of_entry(i)),
                                entry_i.lower == self.base_vaddr + i * self.entry_size(),
                                i == 0,
                            ],
                        );
                        ensures(self.interp_aux(0).lower == self.base_vaddr);
                    },
                );
            }
        }
    }

    pub proof fn lemma_empty_implies_interp_aux_empty(self, i: nat)
        requires
            self.inv(),
            self.empty(),
        ensures
            equal(self.interp_aux(i).map, Map::empty()),
            equal(self.interp_aux(i).map.dom(), Set::empty()),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        if i >= self.entries.len() {
        } else {
            let rem = self.interp_aux(i + 1);
            let entry_i = self.interp_of_entry(i);
            self.lemma_empty_implies_interp_aux_empty(i + 1);
            assert_maps_equal!(rem.map.union_prefer_right(entry_i.map), Map::empty());
        }
    }

    proof fn lemma_empty_implies_interp_empty(self)
        requires
            self.inv(),
            self.empty(),
        ensures
            equal(self.interp().map, Map::empty()),
            equal(self.interp().map.dom(), Set::empty()),
    {
        self.lemma_empty_implies_interp_aux_empty(0);
    }

    proof fn lemma_ranges_disjoint_interp_aux_interp_of_entry(self)
        requires
            self.inv(),
        ensures
            forall|i: nat, j: nat|
                j < i && i < self.num_entries() ==> self.interp_aux(i).ranges_disjoint(
                    self.interp_of_entry(j),
                ),
    {
        assert_forall_by(
            |i: nat, j: nat|
                {
                    requires(j < i && i < self.num_entries());
                    ensures(self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j)));
                    let interp = self.interp_aux(i);
                    let entry_j = self.interp_of_entry(j);
                    self.lemma_inv_implies_interp_aux_inv(i);
                    assert_nonlinear_by(
                        {
                            requires(
                                self.entry_size() > 0 && j < i && interp.lower == self.entry_base(i)
                                    && entry_j.lower == self.entry_base(j) && entry_j.upper
                                    == self.entry_base(j + 1),
                            );
                            ensures(entry_j.upper <= interp.lower && interp.lower > entry_j.lower);
                        },
                    );
                },
        );
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(
        self,
        i: nat,
        j: nat,
    )
        requires
            self.inv(),
            i <= j,
            j < self.entries.len(),
        ensures
            forall|va: nat, pte: PageTableEntry|
                #![auto]
                self.interp_of_entry(j).map.contains_pair(va, pte) ==> self.interp_aux(
                    i,
                ).map.contains_pair(va, pte),
            forall|va: nat|
                #![auto]
                self.interp_of_entry(j).map.dom().contains(va) ==> self.interp_aux(
                    i,
                ).map.dom().contains(va),
            forall|va: nat|
                between(va, self.entry_base(j), self.entry_base(j + 1)) && !self.interp_of_entry(
                    j,
                ).map.dom().contains(va) ==> !self.interp_aux(i).map.dom().contains(va),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        self.lemma_inv_implies_interp_aux_inv(i + 1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);
        let rem = self.interp_aux(i + 1);
        let entry_i = self.interp_of_entry(i);
        if i != j {
            self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(
                i + 1,
                j,
            );
            if let NodeEntry::Directory(d) = self.entries.index(i as int) {
                assert(self.directories_obey_invariant());
                assert(d.inv());
                d.lemma_inv_implies_interp_inv();
                self.lemma_ranges_disjoint_interp_aux_interp_of_entry();
                rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);
            }
        }
        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index(self.base_vaddr, j, self.entry_size());
    }

    pub proof fn lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
        self,
        j: nat,
    )
        requires
            self.inv(),
            j < self.entries.len(),
        ensures
            forall|va: nat|
                #![auto]
                self.interp_of_entry(j).map.dom().contains(va) ==> self.interp().map.dom().contains(
                    va,
                ),
            forall|va: nat, pte: PageTableEntry|
                #![auto]
                self.interp_of_entry(j).map.contains_pair(va, pte)
                    ==> self.interp().map.contains_pair(va, pte),
            forall|va: nat|
                #![auto]
                between(va, self.entry_base(j), self.entry_base(j + 1)) && !self.interp_of_entry(
                    j,
                ).map.dom().contains(va) ==> !self.interp().map.dom().contains(va),
    {
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(0, j);
    }

    // TODO restore spec(checked) when recommends_by is fixed
    pub open spec fn resolve(self, vaddr: nat) -> Result<(nat, PageTableEntry), ()>
        recommends
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        decreases self.arch.layers.len() - self.layer,
    {
        decreases_when(self.inv() && self.interp().accepted_resolve(vaddr));
        decreases_by(Self::check_resolve);
        let entry = self.index_for_vaddr(vaddr);
        match self.entries.index(entry as int) {
            NodeEntry::Page(pte) => {
                let offset = vaddr - self.entry_base(entry);
                Ok((self.entry_base(entry), pte))
            },
            NodeEntry::Directory(d) => { d.resolve(vaddr) },
            NodeEntry::Empty() => { Err(()) },
        }
    }

    #[verifier(decreases_by)]
    proof fn check_resolve(self, vaddr: nat) {
        assert(self.inv() && self.interp().accepted_resolve(vaddr));
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        assert(between(vaddr, self.base_vaddr, self.upper_vaddr()));
        let entry = self.index_for_vaddr(vaddr);
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            vaddr,
            self.entry_size(),
            self.num_entries(),
        );
        // TODO: This makes the recommends failure on the line below go away but not the one in the
        // corresponding spec function. wtf
        assert(0 <= entry < self.entries.len());
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {},
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.inv());
            },
            NodeEntry::Empty() => {},
        }
    }

    proof fn lemma_interp_aux_contains_implies_interp_of_entry_contains(self, j: nat)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.interp_aux(j).map.contains_pair(base, pte) ==> exists|i: nat|
                    #![auto]
                    i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte),
            forall|base: nat|
                self.interp_aux(j).map.dom().contains(base) ==> exists|i: nat|
                    #![auto]
                    i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - j,
    {
        if j >= self.entries.len() {
        } else {
            let _ = self.interp_of_entry(j);
            self.lemma_interp_aux_contains_implies_interp_of_entry_contains(j + 1);
            assert forall|base: nat, pte: PageTableEntry|
                #![auto]
                self.interp_aux(j).map.contains_pair(base, pte) implies exists|i: nat|
                #![auto]
                i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte) by {
                if self.interp_aux(j + 1).map.contains_pair(base, pte) {
                } else {
                }
            };
            assert forall|base: nat|
                #![auto]
                self.interp_aux(j).map.dom().contains(base) implies exists|i: nat|
                #![auto]
                i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base) by {
                if self.interp_aux(j + 1).map.dom().contains(base) {
                } else {
                }
            };
        }
    }

    proof fn lemma_interp_contains_implies_interp_of_entry_contains(self)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.interp().map.contains_pair(base, pte) ==> exists|i: nat|
                    #![auto]
                    i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte),
            forall|base: nat|
                self.interp().map.dom().contains(base) ==> exists|i: nat|
                    #![auto]
                    i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base),
    {
        self.lemma_interp_aux_contains_implies_interp_of_entry_contains(0);
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(
        self,
        vaddr: nat,
        i: nat,
    )
        requires
            self.inv(),
            i < self.num_entries(),
            between(vaddr, self.interp_of_entry(i).lower, self.interp_of_entry(i).upper),
            !exists|base: nat|
                self.interp_of_entry(i).map.dom().contains(base) && between(
                    vaddr,
                    base,
                    base + (#[trigger] self.interp_of_entry(i).map.index(base)).frame.size,
                ),
        ensures
            !exists|base: nat|
                self.interp().map.dom().contains(base) && between(
                    vaddr,
                    base,
                    base + (#[trigger] self.interp().map.index(base)).frame.size,
                ),
    {
        assert(0 < self.arch.entry_size(self.layer));
        assert forall|idx: nat, idx2: nat, base: nat, layer: nat|
            layer < self.arch.layers.len() && idx < idx2 implies self.arch.entry_base(
            layer,
            base,
            idx,
        ) < self.arch.entry_base(layer, base, idx2) by {
            indexing::lemma_entry_base_from_index(base, idx, self.arch.entry_size(layer));
        };
        self.lemma_interp_of_entry();
        self.lemma_interp_contains_implies_interp_of_entry_contains();
        assert(self.directories_obey_invariant());
        if exists|base: nat|
            self.interp().map.dom().contains(base) && between(
                vaddr,
                base,
                base + (#[trigger] self.interp().map.index(base)).frame.size,
            ) {
            let base = choose|base: nat|
                self.interp().map.dom().contains(base) && between(
                    vaddr,
                    base,
                    base + (#[trigger] self.interp().map.index(base)).frame.size,
                );
            let p = self.interp().map.index(base);
            assert(self.interp().map.contains_pair(base, p));
            assert(self.interp().map.dom().contains(base));
            assert(self.interp().map.index(base) == p);
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_resolve_structure_assertions(self, vaddr: nat, idx: nat)
        requires
            self.inv(),
            self.interp().accepted_resolve(vaddr),
            idx == self.index_for_vaddr(vaddr),
        ensures
            self.entries.index(idx as int).is_Directory() ==> {
                let d = self.entries.index(idx as int).get_Directory_0();
                &&& d.interp().accepted_resolve(vaddr)
                &&& d.inv()
            },
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            vaddr,
            self.entry_size(),
            self.num_entries(),
        );
        match self.entries.index(idx as int) {
            NodeEntry::Page(p) => {},
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.interp().accepted_resolve(vaddr));
            },
            NodeEntry::Empty() => {},
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_resolve_refines(self, vaddr: nat)
        requires
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        ensures
            equal(self.interp().resolve(vaddr), self.resolve(vaddr)),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        let entry = self.index_for_vaddr(vaddr);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            vaddr,
            self.entry_size(),
            self.num_entries(),
        );
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {
                assert(self.resolve(vaddr).is_Ok());
                let p_vaddr = self.entry_base(entry);
                assert(self.interp().map.contains_pair(p_vaddr, p));
                assert(vaddr < p_vaddr + self.interp().map.index(p_vaddr).frame.size);
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.interp().accepted_resolve(vaddr));
                d.lemma_resolve_refines(vaddr);
                assert(equal(self.interp_of_entry(entry), d.interp()));
                assert(equal(d.interp().resolve(vaddr), d.resolve(vaddr)));
                if d.resolve(vaddr).is_Ok() {
                    assert(self.resolve(vaddr).is_Ok());
                    assert(exists|base: nat|
                        d.interp().map.dom().contains(base) && between(
                            vaddr,
                            base,
                            base + (#[trigger] d.interp().map.index(base)).frame.size,
                        ));
                    let base = choose|base: nat|
                        d.interp().map.dom().contains(base) && between(
                            vaddr,
                            base,
                            base + (#[trigger] d.interp().map.index(base)).frame.size,
                        );
                    assert(self.interp().map.contains_pair(
                        base,
                        self.interp_of_entry(entry).map.index(base),
                    ));
                    assert(d.resolve(vaddr).is_Ok());
                    assert(d.interp().resolve(vaddr).is_Ok());
                    assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
                } else {
                    assert(d.resolve(vaddr).is_Err());
                    assert(self.resolve(vaddr).is_Err());
                    assert(d.interp().resolve(vaddr).is_Err());
                    assert(!exists|base: nat|
                        d.interp().map.dom().contains(base) && between(
                            vaddr,
                            base,
                            base + (#[trigger] d.interp().map.index(base)).frame.size,
                        )) by {
                        assert(!exists|base: nat, pte: PageTableEntry|
                            d.interp().map.contains_pair(base, pte) && between(
                                vaddr,
                                base,
                                base + pte.frame.size,
                            ));
                        if exists|base: nat|
                            d.interp().map.dom().contains(base) && between(
                                vaddr,
                                base,
                                base + (#[trigger] d.interp().map.index(base)).frame.size,
                            ) {
                            let base = choose|base: nat|
                                d.interp().map.dom().contains(base) && between(
                                    vaddr,
                                    base,
                                    base + (#[trigger] d.interp().map.index(base)).frame.size,
                                );
                            let pte = d.interp().map.index(base);
                            assert(d.interp().map.contains_pair(base, pte));
                        }
                    };
                    self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(
                        vaddr,
                        entry,
                    );
                }
                assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
            },
            NodeEntry::Empty() => {
                assert(self.resolve(vaddr).is_Err());
                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(vaddr, entry);
                assert(self.interp().resolve(vaddr).is_Err());
            },
        }
    }

    pub open spec(checked) fn update(self, n: nat, e: NodeEntry) -> Self
        recommends
            n < self.entries.len(),
    {
        Directory { entries: self.entries.update(n as int, e), ..self }
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(
        self,
        base: nat,
        pte: PageTableEntry,
    ) -> bool
        recommends
            self.inv(),
    {
        self.base_vaddr <= base && base + pte.frame.size <= self.upper_vaddr()
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PageTableEntry) -> bool
        recommends
            self.inv(),
    {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size_at_index_atleast(pte.frame.size, self.layer)
    }

    pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_manual(
        self,
        base: nat,
        pte: PageTableEntry,
    )
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
        ensures
            self.interp().accepted_mapping(base, pte),
    {
        self.lemma_inv_implies_interp_inv();
    }

    pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_auto(self)
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.inv() && #[trigger] self.accepted_mapping(base, pte)
                    ==> self.interp().accepted_mapping(base, pte),
    {
        assert_forall_by(
            |base: nat, pte: PageTableEntry|
                {
                    requires(self.inv() && #[trigger] self.accepted_mapping(base, pte));
                    ensures(self.interp().accepted_mapping(base, pte));
                    self.lemma_accepted_mapping_implies_interp_accepted_mapping_manual(base, pte);
                },
        );
    }

    // Creates new empty directory to map to entry 'entry'
    pub open spec fn new_empty_dir(self, entry: nat) -> Self
        recommends
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
    {
        Directory {
            entries: new_seq(self.arch.num_entries((self.layer + 1) as nat), NodeEntry::Empty()),
            layer: self.layer + 1,
            base_vaddr: self.entry_base(entry),
            arch: self.arch,
            flags: permissive_flags,
        }
    }

    pub proof fn lemma_new_empty_dir(self, entry: nat)
        requires
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
        ensures
            self.new_empty_dir(entry).inv(),
            self.new_empty_dir(entry).entries.len() == self.arch.num_entries(
                (self.layer + 1) as nat,
            ),
            forall|j: nat|
                j < self.new_empty_dir(entry).num_entries() ==> equal(
                    self.new_empty_dir(entry).entries.index(j as int),
                    NodeEntry::Empty(),
                ),
    {
        let new_dir = self.new_empty_dir(entry);
        let num_entries = self.arch.num_entries((self.layer + 1) as nat);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        lemma_new_seq::<NodeEntry>(num_entries, NodeEntry::Empty());
        assert(new_dir.directories_obey_invariant());
        assert(new_dir.well_formed());
        assert(new_dir.inv());
    }

    pub open spec fn map_frame(self, base: nat, pte: PageTableEntry) -> Result<Directory, Directory>
        decreases self.arch.layers.len() - self.layer,
    {
        decreases_by(Self::check_map_frame);
        if self.inv() && self.accepted_mapping(base, pte) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry as int) {
                NodeEntry::Page(p) => { Err(self) },
                NodeEntry::Directory(d) => {
                    if self.entry_size() == pte.frame.size {
                        Err(self)
                    } else {
                        match d.map_frame(base, pte) {
                            Ok(d) => Ok(self.update(entry, NodeEntry::Directory(d))),
                            Err(d) => Err(self.update(entry, NodeEntry::Directory(d))),
                        }
                    }
                },
                NodeEntry::Empty() => {
                    if self.entry_size() == pte.frame.size {
                        Ok(self.update(entry, NodeEntry::Page(pte)))
                    } else {
                        // new_empty_dir's recommendation for `self.layer + 1 < self.arch.layers.len()`
                        // is satisfied because we know the frame size isn't this layer's entrysize
                        // (i.e. must be on some lower level).
                        let new_dir = self.new_empty_dir(entry);
                        // We never fail to insert an accepted mapping into an empty directory
                        Ok(
                            self.update(
                                entry,
                                NodeEntry::Directory(new_dir.map_frame(base, pte).get_Ok_0()),
                            ),
                        )
                    }
                },
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_map_frame(self, base: nat, pte: PageTableEntry) {
        ambient_lemmas1();
        ambient_lemmas2();  // TODO: unnecessary?
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        if self.inv() && self.accepted_mapping(base, pte) {
            indexing::lemma_index_from_base_and_addr(
                self.base_vaddr,
                base,
                self.entry_size(),
                self.num_entries(),
            );
        }
    }

    pub proof fn lemma_accepted_mapping_implies_directory_accepted_mapping(
        self,
        base: nat,
        pte: PageTableEntry,
        d: Directory,
    )
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            equal(d.arch, self.arch),
            d.base_vaddr == self.entry_base(self.index_for_vaddr(base)),
            d.upper_vaddr() == self.entry_base(self.index_for_vaddr(base) + 1),
            d.inv(),
            d.layer == self.layer + 1,
            self.entry_size() != pte.frame.size,
        ensures
            d.accepted_mapping(base, pte),
    {
        ambient_lemmas1();
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        assert(self.directories_obey_invariant());
        assert(d.inv());
        assert(aligned(base, pte.frame.size));
        assert(aligned(pte.frame.base, pte.frame.size));
        assert(d.arch.contains_entry_size_at_index_atleast(pte.frame.size, d.layer));
        assert(self.entry_base(entry) <= base);
        assert(aligned(base, pte.frame.size));
        self.arch.lemma_entry_sizes_aligned_auto();
        assert(aligned(self.entry_size(), pte.frame.size));
        lib::aligned_transitive_auto();
        assert(aligned(self.next_entry_base(entry), pte.frame.size));
        lib::leq_add_aligned_less(base, pte.frame.size, self.entry_base(entry + 1));
        assert(base + pte.frame.size <= self.entry_base(entry + 1));
        assert(base + pte.frame.size <= self.entry_base(entry) + self.entry_size());
        assert(base + pte.frame.size <= d.base_vaddr + self.entry_size());
        assert(base + pte.frame.size <= d.base_vaddr + d.num_entries() * d.entry_size());
        assert(base + pte.frame.size <= d.upper_vaddr());
        assert(d.candidate_mapping_in_bounds(base, pte));
        assert(aligned(base, pte.frame.size));
        assert(aligned(pte.frame.base, pte.frame.size));
    }

    proof fn lemma_map_frame_empty_is_ok(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            self.entries.index(self.index_for_vaddr(base) as int).is_Empty(),
        ensures
            self.map_frame(
                base,
                pte,
            ).is_Ok(),
    // self.new_empty_dir(self.index_for_vaddr(base)).map_frame(base, pte).is_Ok()

        decreases self.arch.layers.len() - self.layer,
    ;

    pub proof fn lemma_map_frame_preserves_inv(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            self.map_frame(base, pte).is_Ok(),
        ensures
            self.map_frame(base, pte).get_Ok_0().layer === self.layer,
            self.map_frame(base, pte).get_Ok_0().arch === self.arch,
            self.map_frame(base, pte).get_Ok_0().base_vaddr === self.base_vaddr,
            !self.map_frame(base, pte).get_Ok_0().empty(),
            self.map_frame(base, pte).get_Ok_0().inv(),
            !exists|b: nat|
                true && self.interp().map.dom().contains(b) && between(
                    base,
                    b,
                    b + (#[trigger] self.interp().map.index(b)).frame.size,
                ),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        let res = self.map_frame(base, pte).get_Ok_0();
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => (),
            NodeEntry::Directory(d) => {
                if self.entry_size() == pte.frame.size {
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    d.lemma_inv_implies_interp_inv();
                    assert(d.inv());
                    d.lemma_map_frame_preserves_inv(base, pte);
                    assert(res.well_formed());
                    assert(res.pages_match_entry_size());
                    assert(res.directories_match_arch());
                    // assert_forall_by(|i: nat| {
                    //     requires(i < res.entries.len() && res.entries.index(i as int).is_Directory());
                    //     ensures(true
                    //             && (#[trigger] res.entries.index(i as int)).get_Directory_0().layer == res.layer + 1
                    //             && res.entries.index(i as int).get_Directory_0().base_vaddr == res.base_vaddr + i * res.entry_size());
                    //     if i < res.entries.len() && res.entries.index(i as int).is_Directory() {
                    //         if i == entry {
                    //         }
                    //     }
                    // });
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.inv());
                    assert(equal(self.map_frame(base, pte).get_Ok_0().layer, self.layer));
                    assert(res.entries.index(entry as int).is_Directory());
                    assert(!res.empty());
                    self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(
                        base,
                        entry,
                    );
                }
            },
            NodeEntry::Empty() => {
                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry);
                if self.entry_size() == pte.frame.size {
                    assert(equal(res.layer, self.layer));
                    assert(res.entries.index(entry as int).is_Page());
                    assert(!res.empty());
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.inv());
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(
                        base,
                        pte,
                        new_dir,
                    );
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(
                        new_dir.base_vaddr,
                        base,
                        new_dir.entry_size(),
                        new_dir.num_entries(),
                    );
                    new_dir.lemma_map_frame_empty_is_ok(base, pte);
                    new_dir.lemma_map_frame_preserves_inv(base, pte);
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.frames_aligned());
                    assert(res.inv());
                    assert(equal(res.layer, self.layer));
                    assert(res.entries.index(entry as int).is_Directory());
                    assert(!res.empty());
                    assert(new_dir.map_frame(base, pte).is_Ok());
                }
            },
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp_aux(
        self,
        i: nat,
        j: nat,
        base: nat,
        n: NodeEntry,
        pte: PageTableEntry,
    )
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            !self.interp_aux(i).map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, pte),
                match n {
                    NodeEntry::Page(p) => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty() => map![],
                },
            ),
        ensures
            equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_aux_inv(i);
        self.lemma_inv_implies_interp_aux_inv(i + 1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);
        self.lemma_interp_of_entry();
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);
        let nself = self.update(j, n);
        if i >= self.entries.len() {
        } else {
            if i == j {
                assert(!self.interp_aux(i + 1).map.dom().contains(base));
                assert(equal(
                    self.interp_aux(i).map,
                    self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map),
                ));
                assert(equal(
                    self.interp_of_entry(i).map.insert(base, pte),
                    nself.interp_of_entry(i).map,
                ));
                self.lemma_entries_equal_implies_interp_aux_equal(nself, i + 1);
                assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));
                assert(!self.interp_aux(i + 1).map.union_prefer_right(
                    self.interp_of_entry(i).map,
                ).dom().contains(base));
                assert(equal(
                    self.interp_aux(i + 1).map.union_prefer_right(
                        self.interp_of_entry(i).map,
                    ).insert(base, pte),
                    self.update(j, n).interp_aux(i + 1).map.union_prefer_right(
                        nself.interp_of_entry(i).map,
                    ),
                ));
                assert(equal(
                    self.interp_aux(i).map.insert(base, pte),
                    self.update(j, n).interp_aux(i).map,
                ));
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());
                self.lemma_insert_interp_of_entry_implies_insert_interp_aux(i + 1, j, base, n, pte);
                self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(
                    i + 1,
                    j,
                );
                assert(!self.interp_of_entry(j).map.dom().contains(base));
                assert(!self.interp_aux(i).map.dom().contains(base));
                assert(equal(
                    self.interp_aux(i + 1).map.insert(base, pte),
                    self.update(j, n).interp_aux(i + 1).map,
                ));
                assert(equal(
                    self.interp_aux(i).map,
                    self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map),
                ));
                assert(nself.inv());
                assert(equal(
                    nself.interp_aux(i).map,
                    nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map),
                ));
                assert(equal(
                    self.interp_aux(i).map.insert(base, pte),
                    self.update(j, n).interp_aux(i).map,
                ));
            }
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp(
        self,
        j: nat,
        base: nat,
        n: NodeEntry,
        pte: PageTableEntry,
    )
        requires
            self.inv(),
            j < self.num_entries(),
            !self.interp().map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, pte),
                match n {
                    NodeEntry::Page(p) => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty() => map![],
                },
            ),
        ensures
            equal(self.interp().map.insert(base, pte), self.update(j, n).interp().map),
        decreases self.arch.layers.len() - self.layer,
    {
        self.lemma_insert_interp_of_entry_implies_insert_interp_aux(0, j, base, n, pte);
    }

    proof fn lemma_nonempty_implies_exists_interp_dom_contains(self)
        requires
            self.inv(),
            !self.empty(),
        ensures
            exists|b: nat| self.interp().map.dom().contains(b),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        assert(exists|i: nat| i < self.num_entries() && !self.entries.index(i as int).is_Empty());
        let i = choose|i: nat| i < self.num_entries() && !self.entries.index(i as int).is_Empty();
        assert(i < self.num_entries());
        assert(!self.entries.index(i as int).is_Empty());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(i);
        match self.entries.index(i as int) {
            NodeEntry::Page(p) => {
                assert(self.interp().map.dom().contains(self.entry_base(i)));
            },
            NodeEntry::Directory(d) => {
                d.lemma_nonempty_implies_exists_interp_dom_contains();
                let b = choose|b: nat| d.interp().map.dom().contains(b);
                assert(self.interp().map.dom().contains(b));
            },
            NodeEntry::Empty() => (),
        }
    }

    pub proof fn lemma_map_frame_structure_assertions(
        self,
        base: nat,
        pte: PageTableEntry,
        idx: nat,
    )
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            idx == self.index_for_vaddr(base),
        ensures
            match self.entries.index(idx as int) {
                NodeEntry::Page(p) => true,
                NodeEntry::Directory(d) => {
                    &&& d.inv()
                    &&& if self.entry_size() == pte.frame.size {
                        true
                    } else {
                        d.accepted_mapping(base, pte)
                    }
                },
                NodeEntry::Empty() => {
                    if self.entry_size() == pte.frame.size {
                        true
                    } else {
                        &&& ((self.layer + 1) as nat) < self.arch.layers.len()
                        &&& self.new_empty_dir(idx).inv()
                        &&& self.new_empty_dir(idx).accepted_mapping(base, pte)
                        &&& self.new_empty_dir(idx).map_frame(base, pte).is_Ok()
                    }
                },
            },
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        let res = self.map_frame(base, pte).get_Ok_0();
        if self.map_frame(base, pte).is_Ok() {
            self.lemma_map_frame_preserves_inv(base, pte);
        }
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {},
            NodeEntry::Directory(d) => {
                assert(d.inv());
                if self.entry_size() == pte.frame.size {
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    assert(d.accepted_mapping(base, pte));
                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == pte.frame.size {
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    assert(new_dir.inv());
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(
                        base,
                        pte,
                        new_dir,
                    );
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(
                        new_dir.base_vaddr,
                        base,
                        new_dir.entry_size(),
                        new_dir.num_entries(),
                    );
                    new_dir.lemma_map_frame_refines_map_frame(base, pte);
                    assert(new_dir.interp().map_frame(base, pte).is_Ok());
                }
            },
        }
    }

    pub proof fn lemma_map_frame_refines_map_frame(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
        ensures
            self.map_frame(base, pte).is_Err() ==> self.map_frame(base, pte).get_Err_0() === self,
            result_map(self.map_frame(base, pte), |d: Directory| d.interp())
                === self.interp().map_frame(base, pte),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        assert(aligned(self.base_vaddr, self.entry_size())) by {
            lib::mod_mult_zero_implies_mod_zero(
                self.base_vaddr,
                self.entry_size(),
                self.num_entries(),
            );
        };
        let res = self.map_frame(base, pte).get_Ok_0();
        if self.map_frame(base, pte).is_Ok() {
            self.lemma_map_frame_preserves_inv(base, pte);
        }
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {
                assert(self.map_frame(base, pte).is_Err());
                assert(self.interp_of_entry(entry).map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map_frame(base, pte).is_Err());
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.inv());
                if self.entry_size() == pte.frame.size {
                    assert(self.map_frame(base, pte).is_Err());
                    d.lemma_nonempty_implies_exists_interp_dom_contains();
                    let b = choose|b: nat| d.interp().map.dom().contains(b);
                    assert(self.interp().map.dom().contains(b));
                    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                        entry,
                    );
                    assert(!self.interp().valid_mapping(base, pte));
                    assert(self.interp().map_frame(base, pte).is_Err());
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    assert(d.accepted_mapping(base, pte));
                    d.lemma_map_frame_refines_map_frame(base, pte);
                    assert(equal(
                        result_map(d.map_frame(base, pte), |d: Directory| d.interp()),
                        d.interp().map_frame(base, pte),
                    ));
                    match d.map_frame(base, pte) {
                        Ok(nd) => {
                            assert(d.map_frame(base, pte).is_Ok());
                            assert(d.interp().map_frame(base, pte).is_Ok());
                            assert(d.interp().accepted_mapping(base, pte));
                            assert(d.interp().valid_mapping(base, pte));
                            assert(self.interp().accepted_mapping(base, pte));
                            assert(self.interp().valid_mapping(base, pte));
                            assert(self.map_frame(base, pte).is_Ok());
                            self.lemma_insert_interp_of_entry_implies_insert_interp(
                                entry,
                                base,
                                NodeEntry::Directory(nd),
                                pte,
                            );
                            assert(self.interp().map_frame(base, pte).is_Ok());
                            assert(equal(
                                self.interp().map.insert(base, pte),
                                self.update(entry, NodeEntry::Directory(nd)).interp().map,
                            ));
                            assert(equal(
                                self.interp().map.insert(base, pte),
                                self.interp().map_frame(base, pte).get_Ok_0().map,
                            ));
                            assert(equal(
                                self.map_frame(base, pte).get_Ok_0().interp(),
                                self.interp().map_frame(base, pte).get_Ok_0(),
                            ));
                        },
                        Err(e) => {
                            assert(d.map_frame(base, pte).is_Err());
                            assert(d.interp().map_frame(base, pte).is_Err());
                            assert(d.interp().accepted_mapping(base, pte));
                            assert(!d.interp().valid_mapping(base, pte));
                            let b = choose|b: nat|
                                #![auto]
                                d.interp().map.dom().contains(b) && overlap(
                                    MemRegion { base: base, size: pte.frame.size },
                                    MemRegion { base: b, size: d.interp().map.index(b).frame.size },
                                );
                            let bbase = d.interp().map.index(b).frame.base;
                            let bsize = d.interp().map.index(b).frame.size;
                            assert(d.interp().map.contains_pair(b, d.interp().map.index(b)));
                            assert(overlap(
                                MemRegion { base: base, size: pte.frame.size },
                                MemRegion { base: b, size: bsize },
                            ));
                            self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                            entry);
                            assert(self.interp().map.contains_pair(b, d.interp().map.index(b)));
                            assert(self.interp().accepted_mapping(base, pte));
                            assert(!self.interp().valid_mapping(base, pte));
                            assert(self.map_frame(base, pte).is_Err());
                            assert(self.interp().map_frame(base, pte).is_Err());
                            assert(self.entries.index(entry as int) === NodeEntry::Directory(d));
                            assert(self.entries.index(entry as int) === NodeEntry::Directory(e));
                            let res = self.update(entry, NodeEntry::Directory(e)).entries;
                            assert(res.index(entry as int) === self.entries.index(entry as int));
                            assert_seqs_equal!(res, self.entries);
                        },
                    }
                    // d.lemma_map_frame_preserves_inv(base, pte);

                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == pte.frame.size {
                    self.lemma_insert_interp_of_entry_implies_insert_interp(
                        entry,
                        base,
                        NodeEntry::Page(pte),
                        pte,
                    );
                    assert(equal(
                        result_map(self.map_frame(base, pte), |d: Directory| d.interp()),
                        self.interp().map_frame(base, pte),
                    ));
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    assert(new_dir.inv());
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(
                        base,
                        pte,
                        new_dir,
                    );
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(
                        new_dir.base_vaddr,
                        base,
                        new_dir.entry_size(),
                        new_dir.num_entries(),
                    );
                    new_dir.lemma_map_frame_empty_is_ok(base, pte);
                    new_dir.lemma_map_frame_preserves_inv(base, pte);
                    let new_dir_mapped = new_dir.map_frame(base, pte).get_Ok_0();
                    assert(new_dir.map_frame(base, pte).is_Ok());
                    assert(new_dir_mapped.inv());
                    new_dir.lemma_map_frame_refines_map_frame(base, pte);
                    assert(new_dir.interp().map_frame(base, pte).is_Ok());
                    assert(equal(
                        new_dir_mapped.interp(),
                        new_dir.interp().map_frame(base, pte).get_Ok_0(),
                    ));
                    new_dir.lemma_empty_implies_interp_empty();
                    assert_maps_equal!(new_dir.interp().map, map![]);
                    assert_maps_equal!(new_dir.interp().map_frame(base, pte).get_Ok_0().map, map![base => pte]);
                    assert_maps_equal!(self.interp_of_entry(entry).map, map![]);
                    assert(equal(self.interp_of_entry(entry).map, map![]));
                    assert(equal(map![].insert(base, pte), new_dir_mapped.interp().map));
                    assert(equal(
                        self.interp_of_entry(entry).map.insert(base, pte),
                        new_dir_mapped.interp().map,
                    ));
                    self.lemma_insert_interp_of_entry_implies_insert_interp(
                        entry,
                        base,
                        NodeEntry::Directory(new_dir_mapped),
                        pte,
                    );
                    assert(equal(
                        result_map(self.map_frame(base, pte), |d: Directory| d.interp()),
                        self.interp().map_frame(base, pte),
                    ));
                }
            },
        }
    }

    pub open spec(checked) fn accepted_unmap(self, base: nat) -> bool
        recommends
            self.well_formed(),
    {
        self.interp().accepted_unmap(base)
    }

    pub open spec fn unmap(self, base: nat) -> Result<Directory, Directory>
        recommends
            self.inv(),
            self.accepted_unmap(base),
        decreases self.arch.layers.len() - self.layer,
        via Self::check_unmap
    {
        if self.inv() && self.accepted_unmap(base) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry as int) {
                NodeEntry::Page(p) => {
                    if aligned(base, self.entry_size()) {
                        // This implies:
                        // base == self.base_vaddr + entry * self.entry_size()
                        // (i.e. no remainder on division)
                        // (proved in lemma_index_for_vaddr_bounds)
                        Ok(self.update(entry, NodeEntry::Empty()))
                    } else {
                        Err(self)
                    }
                },
                NodeEntry::Directory(d) => {
                    match d.unmap(base) {
                        Ok(new_d) => Ok(
                            self.update(
                                entry,
                                if new_d.empty() {
                                    NodeEntry::Empty()
                                } else {
                                    NodeEntry::Directory(new_d)
                                },
                            ),
                        ),
                        Err(new_d) => Err(self.update(entry, NodeEntry::Directory(new_d))),
                    }
                },
                NodeEntry::Empty() => Err(self),
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_unmap(self, base: nat) {
        if self.inv() && self.accepted_unmap(base) {
            ambient_lemmas2();
            indexing::lemma_index_from_base_and_addr(
                self.base_vaddr,
                base,
                self.entry_size(),
                self.num_entries(),
            );
        } else {
        }
    }

    pub proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
            self.unmap(base).is_Ok(),
        ensures
            self.unmap(base).get_Ok_0().inv(),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        let res = self.unmap(base).get_Ok_0();
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        assert(entry < self.num_entries());
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                    assert(res.directories_obey_invariant());
                } else {
                }
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.accepted_unmap(base));
                match d.unmap(base) {
                    Ok(new_d) => {
                        d.lemma_unmap_preserves_inv(base);
                        assert(res.directories_obey_invariant());
                    },
                    Err(_) => {},
                }
            },
            NodeEntry::Empty() => {},
        }
    }

    pub proof fn lemma_unmap_structure_assertions(self, base: nat, idx: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
            idx == self.index_for_vaddr(base),
        ensures
            match self.entries.index(idx as int) {
                NodeEntry::Page(p) => {
                    if aligned(base, self.entry_size()) {
                        base == self.base_vaddr + idx * self.entry_size()
                    } else {
                        true
                    }
                },
                NodeEntry::Directory(d) => {
                    &&& d.inv()
                    &&& d.accepted_unmap(base)
                },
                NodeEntry::Empty() => true,
            },
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        assert(aligned(self.base_vaddr, self.entry_size())) by {
            lib::mod_mult_zero_implies_mod_zero(
                self.base_vaddr,
                self.entry_size(),
                self.num_entries(),
            );
        };
        match self.entries.index(self.index_for_vaddr(base) as int) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                } else {
                }
            },
            NodeEntry::Directory(d) => {
                assert(d.inv());
                assert(d.accepted_unmap(base));
                d.lemma_unmap_refines_unmap(base);
            },
            NodeEntry::Empty() => {},
        }
    }

    pub proof fn lemma_unmap_refines_unmap(self, base: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
        ensures
            self.unmap(base).is_Err() ==> self.unmap(base).get_Err_0() === self,
            equal(
                result_map(self.unmap(base), |d: Directory| d.interp()),
                self.interp().unmap(base),
            ),
        decreases self.arch.layers.len() - self.layer,
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        if let Ok(nself) = self.unmap(base) {
            self.lemma_unmap_preserves_inv(base);
            assert(nself.inv());
            nself.lemma_inv_implies_interp_inv();
            assert(nself.interp().inv());
        }
        let nself_res = self.unmap(base);
        let nself = self.unmap(base).get_Ok_0();
        let i_nself_res = self.interp().unmap(base);
        let i_nself = self.interp().unmap(base).get_Ok_0();
        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(
            self.base_vaddr,
            base,
            self.entry_size(),
            self.num_entries(),
        );
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry as int) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                    assert_maps_equal!(self.interp_of_entry(entry).map.remove(base), map![]);
                    assert(self.update(entry, NodeEntry::Empty()).inv());
                    self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(
                        entry,
                        base,
                        NodeEntry::Empty(),
                    );
                } else {
                    indexing::lemma_entry_base_from_index(
                        self.base_vaddr,
                        entry,
                        self.entry_size(),
                    );
                    assert(!self.interp().map.dom().contains(base));
                    assert(i_nself_res.is_Err());
                }
            },
            NodeEntry::Directory(d) => {
                assert(d.inv());
                d.lemma_inv_implies_interp_inv();
                assert(d.accepted_unmap(base));
                d.lemma_unmap_refines_unmap(base);
                match d.unmap(base) {
                    Ok(new_d) => {
                        d.lemma_unmap_preserves_inv(base);
                        assert(new_d.inv());
                        assert(d.unmap(base).is_Ok());
                        assert(d.interp().unmap(base).is_Ok());
                        assert(equal(new_d.interp(), d.interp().unmap(base).get_Ok_0()));
                        if new_d.empty() {
                            new_d.lemma_empty_implies_interp_empty();
                            d.interp().lemma_unmap_decrements_len(base);
                            assert(new_d.interp().map.dom().len() == 0);
                            assert(d.interp().map.dom().len() == 1);
                            assert(d.interp().map.dom().contains(base));
                            assert_sets_equal!(d.interp().map.dom(), set![base]);
                            assert(nself_res.is_Ok());
                            assert(equal(self.interp_of_entry(entry).map, d.interp().map));
                            assert(equal(
                                d.interp().unmap(base).get_Ok_0().map,
                                d.interp().map.remove(base),
                            ));
                            assert_maps_equal!(self.interp_of_entry(entry).map.remove(base), map![]);
                            assert(self.update(entry, NodeEntry::Empty()).inv());
                            self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(
                                entry,
                                base,
                                NodeEntry::Empty(),
                            );
                            assert(equal(nself.interp(), i_nself));
                        } else {
                            assert(self.update(entry, NodeEntry::Directory(new_d)).inv());
                            self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(
                                entry,
                                base,
                                NodeEntry::Directory(new_d),
                            );
                        }
                    },
                    Err(e) => {
                        assert(self.entries.index(entry as int) === NodeEntry::Directory(d));
                        assert(self.entries.index(entry as int) === NodeEntry::Directory(e));
                        let res = self.update(entry, NodeEntry::Directory(e)).entries;
                        assert(res.index(entry as int) === self.entries.index(entry as int));
                        assert_seqs_equal!(res, self.entries);
                        assert(res === self.entries);
                    },
                }
            },
            NodeEntry::Empty() => {},
        }
    }

    proof fn lemma_entries_equal_implies_interp_aux_equal(self, other: Directory, i: nat)
        requires
            self.inv(),
            other.inv(),
            equal(self.arch, other.arch),
            equal(self.layer, other.layer),
            equal(self.base_vaddr, other.base_vaddr),
            equal(self.num_entries(), other.num_entries()),
            forall|j: int|
                i <= j && j < self.entries.len() ==> equal(
                    self.entries.index(j),
                    other.entries.index(j),
                ),
        ensures
            equal(self.interp_aux(i), other.interp_aux(i)),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        if i >= self.entries.len() {
        } else {
            let rem1 = self.interp_aux(i + 1);
            let rem2 = other.interp_aux(i + 1);
            let entry_i1 = self.interp_of_entry(i);
            let entry_i2 = other.interp_of_entry(i);
            self.lemma_entries_equal_implies_interp_aux_equal(other, i + 1);
            assert_maps_equal!(rem1.map.union_prefer_right(entry_i1.map), rem2.map.union_prefer_right(entry_i2.map));
        }
    }

    proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(
        self,
        j: nat,
        i: nat,
        vaddr: nat,
        n: NodeEntry,
    )
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            self.interp_of_entry(j).map.dom().contains(vaddr),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.remove(vaddr),
                match n {
                    NodeEntry::Page(p) => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty() => map![],
                },
            ),
        ensures
            equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i,
    {
        assert(j < self.entries.len());
        ambient_lemmas1();
        self.lemma_inv_implies_interp_aux_inv(i);
        self.lemma_inv_implies_interp_aux_inv(i + 1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);
        self.lemma_interp_of_entry();
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);
        let nself = self.update(j, n);
        if i >= self.entries.len() {
        } else {
            if i == j {
                assert(equal(
                    self.interp_aux(i).map,
                    self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map),
                ));
                assert(equal(
                    self.interp_of_entry(i).map.remove(vaddr),
                    nself.interp_of_entry(i).map,
                ));
                self.lemma_entries_equal_implies_interp_aux_equal(nself, i + 1);
                assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));
                assert(equal(
                    self.interp_aux(i + 1).map.union_prefer_right(
                        self.interp_of_entry(i).map,
                    ).remove(vaddr),
                    nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map),
                ));
                assert(equal(
                    self.interp_aux(i).map.remove(vaddr),
                    self.update(j, n).interp_aux(i).map,
                ));
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());
                self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(
                    j,
                    i + 1,
                    vaddr,
                    n,
                );
                self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(
                    i + 1,
                    j,
                );
                assert(self.interp_aux(j).map.dom().contains(vaddr));
                assert(self.interp_aux(i + 1).map.dom().contains(vaddr));
                assert(equal(
                    self.interp_aux(i + 1).map.remove(vaddr),
                    self.update(j, n).interp_aux(i + 1).map,
                ));
                assert(equal(
                    self.interp_aux(i).map,
                    self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map),
                ));
                assert(nself.inv());
                assert(equal(
                    nself.interp_aux(i).map,
                    nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map),
                ));
                assert(equal(
                    self.interp_aux(i).map.remove(vaddr),
                    self.update(j, n).interp_aux(i).map,
                ));
            }
        }
    }

    proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp(
        self,
        j: nat,
        vaddr: nat,
        n: NodeEntry,
    )
        requires
            self.inv(),
            j < self.num_entries(),
            self.interp_of_entry(j).map.dom().contains(vaddr),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.remove(vaddr),
                match n {
                    NodeEntry::Page(p) => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty() => map![],
                },
            ),
        ensures
            equal(self.interp().map.remove(vaddr), self.update(j, n).interp().map),
    {
        self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, 0, vaddr, n);
    }
}

// FIXME: Something like these functions should probably be added to vstd. One problem with that:
// May want exec versions of the functions but can't give them the same name.
pub open spec(checked) fn result_map_ok<A, B, C>(res: Result<A, B>, f: FnSpec(A) -> C) -> Result<
    C,
    B,
> {
    match res {
        Ok(a) => Ok(f(a)),
        Err(b) => Err(b),
    }
}

pub open spec(checked) fn result_map<A, B>(res: Result<A, A>, f: FnSpec(A) -> B) -> Result<B, B> {
    match res {
        Ok(a) => Ok(f(a)),
        Err(a) => Err(f(a)),
    }
}

} // verus!
}

    pub mod l2_impl {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use vstd::assert_by_contradiction;
        use vstd::map::*;
        use vstd::modes::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::seq_lib::*;
        use vstd::set::*;
        use vstd::set_lib::*;

        use crate::definitions_t::{
            aligned, axiom_max_phyaddr_width_facts, between, candidate_mapping_in_bounds, new_seq,
            overlap, x86_arch_exec, x86_arch_exec_spec, x86_arch_spec, Arch, ArchExec, Flags,
            MapResult, MemRegion, MemRegionExec, PageTableEntry, PageTableEntryExec, UnmapResult,
        };
        use crate::definitions_t::{
            bit, bitmask_inc, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_BASE, MAX_PHYADDR,
            MAX_PHYADDR_WIDTH, PAGE_SIZE, WORD_SIZE, X86_NUM_ENTRIES, X86_NUM_LAYERS,
        };
        use crate::definitions_u::{
            aligned_exec, lemma_maxphyaddr_facts, lemma_new_seq, permissive_flags,
        };
        use crate::extra as lib;
        use crate::impl_u::indexing;
        use crate::impl_u::l0::ambient_arith;
        use crate::impl_u::l1;
        use crate::spec_t::hardware::{GhostPageDirectoryEntry, PageDirectoryEntry};
        use crate::spec_t::hardware::{
            MASK_ADDR, MASK_DIR_ADDR, MASK_FLAG_A, MASK_FLAG_P, MASK_FLAG_PCD, MASK_FLAG_PWT,
            MASK_FLAG_RW, MASK_FLAG_US, MASK_FLAG_XD, MASK_L1_PG_ADDR, MASK_L1_PG_FLAG_PS,
            MASK_L2_PG_ADDR, MASK_L2_PG_FLAG_PS, MASK_L3_PG_ADDR, MASK_L3_PG_FLAG_PAT,
            MASK_PG_FLAG_D, MASK_PG_FLAG_G, MASK_PG_FLAG_PAT,
        };
        use crate::spec_t::mem;
        use crate::spec_t::mem::word_index_spec;

        verus! {

proof fn lemma_page_aligned_implies_mask_dir_addr_is_identity()
    ensures
        forall|addr: u64|
            addr <= MAX_PHYADDR ==> #[trigger] aligned(addr as nat, PAGE_SIZE as nat) ==> addr
                & MASK_DIR_ADDR == addr,
{
    assert forall|addr: u64|
        addr <= MAX_PHYADDR && #[trigger] aligned(addr as nat, PAGE_SIZE as nat) implies addr
        & MASK_DIR_ADDR == addr by {
        let max_width: u64 = MAX_PHYADDR_WIDTH;
        let mask_dir_addr: u64 = MASK_DIR_ADDR;
        assert(addr & mask_dir_addr == addr) by (bit_vector)
            requires
                addr <= sub(1u64 << max_width, 1u64),
                addr % 4096u64 == 0,
                mask_dir_addr == bitmask_inc!(12u64, max_width - 1),
        ;
    };
}

proof fn lemma_aligned_addr_mask_facts(addr: u64)
    ensures
        aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr & MASK_ADDR),
        aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr & MASK_ADDR),
        (addr & MASK_L3_PG_ADDR == addr & MASK_ADDR),
        addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
            == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
            == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
            == addr),
{
    axiom_max_phyaddr_width_facts();
    assert(aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr
        & MASK_ADDR)) by {
        if aligned(addr as nat, L1_ENTRY_SIZE as nat) {
            let max_width: u64 = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(30u64, max_width - 1) == addr
                & bitmask_inc!(12u64, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x40000000u64 == 0,
                    32 <= max_width,
            ;
        }
    };
    assert(aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr
        & MASK_ADDR)) by {
        if aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            let max_width: u64 = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(21u64, max_width - 1) == addr
                & bitmask_inc!(12u64, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x200000u64 == 0,
                    32 <= max_width,
            ;
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
        == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) {
            assert(aligned(L1_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by (nonlinear_arith);
            lib::aligned_transitive(addr as nat, L1_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
        == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            assert(aligned(L2_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by (nonlinear_arith);
            lib::aligned_transitive(addr as nat, L2_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR
        == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) {
            assert(aligned(L3_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by (nonlinear_arith);
            lib::aligned_transitive(addr as nat, L3_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
}

pub open spec fn addr_is_zero_padded(layer: nat, addr: u64, is_page: bool) -> bool {
    is_page ==> {
        if layer == 1 {
            addr & MASK_L1_PG_ADDR == addr
        } else if layer == 2 {
            addr & MASK_L2_PG_ADDR == addr
        } else if layer == 3 {
            addr & MASK_L3_PG_ADDR == addr
        } else {
            arbitrary()
        }
    }
}

// PageDirectoryEntry is defined in crate::spec_t::hardware to define the page table walk
// semantics. Here we reuse it for the implementation and add exec functions to it.
impl PageDirectoryEntry {
    // PAT flag is set to zero for huge pages and super pages
    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@.is_Page() && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@.is_Page() && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }

    pub proof fn lemma_addr_mask_when_hp_pat_is_zero(self)
        requires
            self.hp_pat_is_zero() && self.all_mb0_bits_are_zero() && self@.is_Page(),
        ensures
            self.layer == 1 ==> self.entry & MASK_L1_PG_ADDR == self.entry & MASK_ADDR,
            self.layer == 2 ==> self.entry & MASK_L2_PG_ADDR == self.entry & MASK_ADDR,
    {
        let e = self.entry;
        let mw = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        if self.layer() == 1 {
            assert(e & bitmask_inc!(12u64, mw - 1) == e & bitmask_inc!(30u64, mw - 1))
                by (bit_vector)
                requires
                    e & bit!(12u64) == 0,
                    e & bitmask_inc!(13u64,29u64) == 0,
                    32 <= mw <= 52,
            ;
        } else if self.layer() == 2 {
            assert(e & bitmask_inc!(12u64, mw - 1) == e & bitmask_inc!(21u64, mw - 1))
                by (bit_vector)
                requires
                    e & bit!(12u64) == 0,
                    e & bitmask_inc!(13u64,20u64) == 0,
                    32 <= mw <= 52,
            ;
        }
    }

    pub proof fn lemma_zero_entry_facts(self)
        requires
            self.entry == 0,
            self.layer@ <= 3,
        ensures
            self@.is_Empty(),
            self.all_mb0_bits_are_zero(),
    {
        assert(forall|a: u64| 0 & a == 0) by (bit_vector);
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        assert(1u64 << 0 == 1) by (bit_vector);
        assert(0u64 & 1 == 0) by (bit_vector);
    }

    pub proof fn lemma_new_entry_mb0_bits_are_zero(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
    )
        requires
            layer <= 3,
            if is_page {
                0 < layer
            } else {
                layer < 3
            },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({
                let e = address | MASK_FLAG_P | if is_page && layer != 3 {
                    MASK_L1_PG_FLAG_PS
                } else {
                    0
                } | if is_writable {
                    MASK_FLAG_RW
                } else {
                    0
                } | if is_supervisor {
                    0
                } else {
                    MASK_FLAG_US
                } | if is_writethrough {
                    MASK_FLAG_PWT
                } else {
                    0
                } | if disable_cache {
                    MASK_FLAG_PCD
                } else {
                    0
                } | if disable_execute {
                    MASK_FLAG_XD
                } else {
                    0
                };
                (PageDirectoryEntry {
                    entry: e,
                    layer: Ghost(layer as nat),
                }).all_mb0_bits_are_zero()
            }),
    {
        let or1 = MASK_FLAG_P;
        let or2 = if is_page && layer != 3 {
            MASK_L1_PG_FLAG_PS as u64
        } else {
            0
        };
        let or3 = if is_writable {
            MASK_FLAG_RW as u64
        } else {
            0
        };
        let or4 = if is_supervisor {
            0
        } else {
            MASK_FLAG_US as u64
        };
        let or5 = if is_writethrough {
            MASK_FLAG_PWT as u64
        } else {
            0
        };
        let or6 = if disable_cache {
            MASK_FLAG_PCD as u64
        } else {
            0
        };
        let or7 = if disable_execute {
            MASK_FLAG_XD as u64
        } else {
            0
        };
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: u64 = MAX_PHYADDR_WIDTH;
        assert(forall|a: u64| #![auto] a == a | 0) by (bit_vector);
        axiom_max_phyaddr_width_facts();
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 12 ==> a & bitmask_inc!(12u64,sub(mw,1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i != 7 && (a & bit!(7u64) == 0) ==> (a | bit!(i)) & bit!(7u64) == 0) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 13 && (a & bitmask_inc!(13u64,29u64) == 0) ==> ((a | bit!(i))
                & bitmask_inc!(13u64,29u64) == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i > 29 && (a & bitmask_inc!(13u64,29u64) == 0) ==> ((a | bit!(i))
                & bitmask_inc!(13u64,29u64) == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 13 && (a & bitmask_inc!(13u64,20u64) == 0) ==> ((a | bit!(i))
                & bitmask_inc!(13u64,20u64) == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i > 20 && (a & bitmask_inc!(13u64,20u64) == 0) ==> ((a | bit!(i))
                & bitmask_inc!(13u64,20u64) == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i < mw && (a & bitmask_inc!(mw,51u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51u64)
                == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i > 51 && (a & bitmask_inc!(mw,51u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51u64)
                == 0)) by (bit_vector)
            requires
                mw <= 52,
        ;
        assert(address & bitmask_inc!(mw, 51) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12u64, mw - 1) == address,
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i < mw && (a & bitmask_inc!(mw,62u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62u64)
                == 0)) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i > 62 && (a & bitmask_inc!(mw,62u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62u64)
                == 0)) by (bit_vector)
            requires
                mw <= 52,
        ;
        assert(address & bitmask_inc!(mw, 62) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12u64, mw - 1) == address,
                32 <= mw <= 52,
        ;
        PageDirectoryEntry::lemma_new_entry_addr_mask_is_address(
            layer,
            address,
            is_page,
            is_writable,
            is_supervisor,
            is_writethrough,
            disable_cache,
            disable_execute,
        );
        if layer == 0 {
            assert(!is_page);
            assert(e & bit!(7u64) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
        } else if layer == 1 {
            if is_page {
                assert(address & bitmask_inc!(30u64,sub(mw,1)) == address ==> address
                    & bitmask_inc!(13u64,29u64) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13u64,29u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            } else {
                assert(e & bit!(7u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            }
        } else if layer == 2 {
            if is_page {
                assert(address & bitmask_inc!(21u64,sub(mw,1)) == address ==> address
                    & bitmask_inc!(13u64,20u64) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13u64,20u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            } else {
                assert(e & bit!(7u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            }
        } else if layer == 3 {
            assert(is_page);
            // assert(e & bit!(7u64) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
        } else {
            assert(false);
        }
        let pde = PageDirectoryEntry { entry: e, layer: Ghost(layer as nat) };
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        assert(pde.all_mb0_bits_are_zero());
    }

    pub proof fn lemma_new_entry_addr_mask_is_address(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
    )
        requires
            layer <= 3,
            if is_page {
                0 < layer
            } else {
                layer < 3
            },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({
                let e = address | MASK_FLAG_P | if is_page && layer != 3 {
                    MASK_L1_PG_FLAG_PS
                } else {
                    0
                } | if is_writable {
                    MASK_FLAG_RW
                } else {
                    0
                } | if is_supervisor {
                    0
                } else {
                    MASK_FLAG_US
                } | if is_writethrough {
                    MASK_FLAG_PWT
                } else {
                    0
                } | if disable_cache {
                    MASK_FLAG_PCD
                } else {
                    0
                } | if disable_execute {
                    MASK_FLAG_XD
                } else {
                    0
                };
                &&& e & MASK_ADDR == address
                &&& e & MASK_FLAG_P == MASK_FLAG_P
                &&& (e & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3)
                &&& (e & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable
                &&& (e & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor
                &&& (e & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough
                &&& (e & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache
                &&& (e & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute
                &&& (is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0)
                &&& (is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0)
            }),
    {
        let or1 = MASK_FLAG_P;
        let or2 = if is_page && layer != 3 {
            MASK_L1_PG_FLAG_PS as u64
        } else {
            0
        };
        let or3 = if is_writable {
            MASK_FLAG_RW as u64
        } else {
            0
        };
        let or4 = if is_supervisor {
            0
        } else {
            MASK_FLAG_US as u64
        };
        let or5 = if is_writethrough {
            MASK_FLAG_PWT as u64
        } else {
            0
        };
        let or6 = if disable_cache {
            MASK_FLAG_PCD as u64
        } else {
            0
        };
        let or7 = if disable_execute {
            MASK_FLAG_XD as u64
        } else {
            0
        };
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: u64 = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        assert(forall|a: u64, x: u64| x < 64 && (a & bit!(x) == 0) ==> a & bit!(x) != bit!(x))
            by (bit_vector);
        assert(forall|a: u64| #![auto] a == a | 0) by (bit_vector);
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))
                & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))
                & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0)
            by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0)
            by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert(forall|a: u64, i: u64|
            #![auto]
            i < 64 ==> a & bit!(i) == 0 ==> (a | bit!(i)) & bit!(i) == bit!(i)) by (bit_vector);
        assert(forall|a: u64, i: u64, j: u64|
            #![auto]
            i != j ==> a & bit!(i) == (a | bit!(j)) & bit!(i)) by (bit_vector);
        assert({
            &&& is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0
            &&& is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0
        }) by {
            if is_page && layer == 1 {
                assert(address & bit!(12u64) == 0) by (bit_vector)
                    requires
                        address & bitmask_inc!(30u64, sub(mw, 1)) == address,
                ;
            }
            if is_page && layer == 2 {
                assert(address & bit!(12u64) == 0) by (bit_vector)
                    requires
                        address & bitmask_inc!(21u64, sub(mw, 1)) == address,
                ;
            }
        };
    }

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer as nat, pte.frame.base as u64, true),
            pte.frame.base as u64 & MASK_ADDR == pte.frame.base as u64,
        ensures
            r.all_mb0_bits_are_zero(),
            r.hp_pat_is_zero(),
            r@.is_Page(),
            r.layer@ == layer,
            r@.get_Page_addr() == pte.frame.base,
            r.entry & MASK_ADDR == pte.frame.base,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            (r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (layer != 3),
            (r.entry & MASK_FLAG_RW == MASK_FLAG_RW) == pte.flags.is_writable,
            r@.get_Page_flag_RW() == pte.flags.is_writable,
            (r.entry & MASK_FLAG_US == MASK_FLAG_US) == !pte.flags.is_supervisor,
            r@.get_Page_flag_US() == !pte.flags.is_supervisor,
            r.entry & MASK_FLAG_PWT != MASK_FLAG_PWT,
            r.entry & MASK_FLAG_PCD != MASK_FLAG_PCD,
            (r.entry & MASK_FLAG_XD == MASK_FLAG_XD) == pte.flags.disable_execute,
            r@.get_Page_flag_XD() == pte.flags.disable_execute,
    {
        Self::new_entry(
            layer,
            pte.frame.base as u64,
            true,
            pte.flags.is_writable,
            pte.flags.is_supervisor,
            false,
            false,
            pte.flags.disable_execute,
        )
    }

    pub fn new_dir_entry(layer: usize, address: u64) -> (r: Self)
        requires
            layer < 3,
            address & MASK_DIR_ADDR == address,
        ensures
            r.all_mb0_bits_are_zero(),
            r.hp_pat_is_zero(),
            r@.is_Directory(),
            r.layer@ == layer,
            r@.get_Directory_addr() == address,
            r@.get_Directory_flag_RW(),
            r@.get_Directory_flag_US(),
            !r@.get_Directory_flag_XD(),
    {
        Self::new_entry(
            layer,
            address,
            false,  // is_page
            true,  // is_writable
            false,  // is_supervisor
            false,  // is_writethrough
            false,  // disable_cache
            false,
        )  // disable_execute

    }

    pub fn new_entry(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
    ) -> (r: PageDirectoryEntry)
        requires
            layer <= 3,
            if is_page {
                0 < layer
            } else {
                layer < 3
            },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            r.all_mb0_bits_are_zero(),
            if is_page {
                r@.is_Page() && r@.get_Page_addr() == address
            } else {
                r@.is_Directory() && r@.get_Directory_addr() == address
            },
            r.hp_pat_is_zero(),
            r.layer@ == layer,
            r.entry & MASK_ADDR == address,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            (r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3),
            (r.entry & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable,
            (r.entry & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor,
            (r.entry & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough,
            (r.entry & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache,
            (r.entry & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute,
    {
        let e = PageDirectoryEntry {
            entry: {
                address | MASK_FLAG_P | if is_page && layer != 3 {
                    MASK_L1_PG_FLAG_PS
                } else {
                    0
                } | if is_writable {
                    MASK_FLAG_RW
                } else {
                    0
                } | if is_supervisor {
                    0
                } else {
                    MASK_FLAG_US
                } | if is_writethrough {
                    MASK_FLAG_PWT
                } else {
                    0
                } | if disable_cache {
                    MASK_FLAG_PCD
                } else {
                    0
                } | if disable_execute {
                    MASK_FLAG_XD
                } else {
                    0
                }
            },
            layer: Ghost(layer as nat),
        };
        proof {
            PageDirectoryEntry::lemma_new_entry_addr_mask_is_address(
                layer,
                address,
                is_page,
                is_writable,
                is_supervisor,
                is_writethrough,
                disable_cache,
                disable_execute,
            );
            PageDirectoryEntry::lemma_new_entry_mb0_bits_are_zero(
                layer,
                address,
                is_page,
                is_writable,
                is_supervisor,
                is_writethrough,
                disable_cache,
                disable_execute,
            );
            if is_page {
                e.lemma_addr_mask_when_hp_pat_is_zero();
            }
        }
        e
    }

    pub fn flags(&self) -> (res: Flags)
        requires
            self.layer() <= 3,
            self@.is_Page(),
        ensures
            res.is_writable <==> self.entry & MASK_FLAG_RW == MASK_FLAG_RW,
            res.is_supervisor <==> self.entry & MASK_FLAG_US != MASK_FLAG_US,
            res.disable_execute <==> self.entry & MASK_FLAG_XD == MASK_FLAG_XD,
    {
        Flags {
            is_writable: self.entry & MASK_FLAG_RW == MASK_FLAG_RW,
            is_supervisor: self.entry & MASK_FLAG_US != MASK_FLAG_US,
            disable_execute: self.entry & MASK_FLAG_XD == MASK_FLAG_XD,
        }
    }

    pub fn address(&self) -> (res: u64)
        requires
            self.layer() <= 3,
            self@.is_Page() ==> 0 < self.layer(),
            self.hp_pat_is_zero(),
            self.all_mb0_bits_are_zero(),
            !self@.is_Empty(),
        ensures
            res as usize == match self@ {
                GhostPageDirectoryEntry::Page { addr, .. } => addr,
                GhostPageDirectoryEntry::Directory { addr, .. } => addr,
                GhostPageDirectoryEntry::Empty => arbitrary(),
            },
    {
        proof {
            match self@ {
                GhostPageDirectoryEntry::Page {
                    addr,
                    ..
                } => self.lemma_addr_mask_when_hp_pat_is_zero(),
                GhostPageDirectoryEntry::Directory { addr, .. } => {},
                GhostPageDirectoryEntry::Empty => {},
            }
        }
        self.entry & MASK_ADDR
    }

    pub fn is_mapping(&self) -> (r: bool)
        requires
            self.all_mb0_bits_are_zero(),
            self.layer() <= 3,
        ensures
            r == !self@.is_Empty(),
    {
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r {
                self@.is_Page()
            } else {
                self@.is_Directory()
            },
    {
        if layer == 3 {
            true
        } else if layer == 0 {
            false
        } else {
            (self.entry & MASK_L1_PG_FLAG_PS) == MASK_L1_PG_FLAG_PS
        }
    }

    pub fn is_dir(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r {
                self@.is_Directory()
            } else {
                self@.is_Page()
            },
    {
        !self.is_page(layer)
    }
}

/// PTDir is used in the `ghost_pt` field of the PageTable. It's used to keep track of the memory
/// regions in which the corresponding translation structures are stored.
pub struct PTDir {
    /// Region of physical memory in which this PTDir is stored
    pub region: MemRegion,
    pub entries: Seq<Option<PTDir>>,
    /// reflexive-transitive closure of `region` over `entries`
    pub used_regions: Set<MemRegion>,
}

// Page table methods are in a separate module for namespacing, since we can't use a struct + impl
// (To use a struct we'd have to keep a &mut reference to the memory in the struct, which Verus
// doesn't support. Or we keep an owned copy but then can't have an external interface that mutably
// borrows a memory.)
pub mod PT {
    use super::*;

    pub open spec(checked) fn well_formed(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        ptr: usize,
    ) -> bool {
        &&& x86_arch_spec.inv()
    }

    pub open spec(checked) fn inv(mem: &mem::PageTableMemory, pt: PTDir) -> bool {
        &&& pt.region == mem.cr3_spec()@
        &&& inv_at(mem, pt, 0, mem.cr3_spec().base)
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn entry_at_spec(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        i: nat,
    ) -> PageDirectoryEntry {
        PageDirectoryEntry { entry: mem.spec_read(i, pt.region), layer: Ghost(layer) }
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn view_at(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        i: nat,
    ) -> GhostPageDirectoryEntry {
        PageDirectoryEntry { entry: mem.spec_read(i, pt.region), layer: Ghost(layer) }@
    }

    /// Get the entry at address ptr + i * WORD_SIZE
    fn entry_at(
        mem: &mem::PageTableMemory,
        Ghost(pt): Ghost<PTDir>,
        layer: usize,
        ptr: usize,
        i: usize,
    ) -> (res: PageDirectoryEntry)
        requires
            i < 512,
            inv_at(mem, pt, layer as nat, ptr),
        ensures
            res.layer@ == layer as nat,
            res@ === view_at(mem, pt, layer as nat, ptr, i as nat),
            res == entry_at_spec(mem, pt, layer as nat, ptr, i as nat),
            res.hp_pat_is_zero(),
            (res@.is_Page() ==> 0 < res.layer()),
    {
        assert(aligned((ptr + i * WORD_SIZE) as nat, 8)) by {
            assert(inv_at(mem, pt, layer as nat, ptr));
            assert(well_formed(mem, pt, ptr));
            assert(ptr % PAGE_SIZE == 0);
        };
        // triggering
        proof {
            let _ = entry_at_spec(mem, pt, layer as nat, ptr, i as nat);
        }
        PageDirectoryEntry { entry: mem.read(ptr, i, Ghost(pt.region)), layer: Ghost(layer as nat) }
    }

    pub open spec fn ghost_pt_matches_structure(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat|
            #![trigger pt.entries[i as int], view_at(mem, pt, layer, ptr, i)]
            i < X86_NUM_ENTRIES ==> {
                let entry = view_at(mem, pt, layer, ptr, i);
                entry.is_Directory() == pt.entries[i as int].is_Some()
            }
    }

    pub open spec fn directories_obey_invariant_at(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool
        decreases X86_NUM_LAYERS - layer, 0nat,
        when well_formed(mem, pt, ptr) && layer_in_range(layer)
    {
        forall|i: nat|
            i < X86_NUM_ENTRIES ==> {
                let entry = #[trigger] view_at(mem, pt, layer, ptr, i);
                entry.is_Directory() ==> {
                    &&& inv_at(
                        mem,
                        pt.entries[i as int].get_Some_0(),
                        layer + 1,
                        entry.get_Directory_addr(),
                    )
                }
            }
    }

    pub open spec fn empty_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool
        recommends
            well_formed(mem, pt, ptr),
    {
        forall|i: nat| i < X86_NUM_ENTRIES ==> view_at(mem, pt, layer, ptr, i).is_Empty()
    }

    pub open spec(checked) fn layer_in_range(layer: nat) -> bool {
        layer < X86_NUM_LAYERS
    }

    pub open spec(checked) fn inv_at(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool
        decreases X86_NUM_LAYERS - layer,
    {
        &&& ptr % PAGE_SIZE == 0
        &&& well_formed(mem, pt, ptr)
        &&& mem.inv()
        &&& mem.regions().contains(pt.region)
        &&& pt.region.base == ptr
        &&& pt.region.size == PAGE_SIZE
        &&& mem.region_view(pt.region).len() == pt.entries.len()
        &&& layer_in_range(layer)
        &&& pt.entries.len() == X86_NUM_ENTRIES
        &&& directories_obey_invariant_at(mem, pt, layer, ptr)
        &&& directories_have_flags(mem, pt, layer, ptr)
        &&& ghost_pt_matches_structure(mem, pt, layer, ptr)
        &&& ghost_pt_used_regions_rtrancl(mem, pt, layer, ptr)
        &&& ghost_pt_used_regions_pairwise_disjoint(mem, pt, layer, ptr)
        &&& ghost_pt_region_notin_used_regions(mem, pt, layer, ptr)
        &&& pt.used_regions.subset_of(mem.regions())
        &&& hp_pat_is_zero(mem, pt, layer, ptr)
        &&& entry_mb0_bits_are_zero(mem, pt, layer, ptr)
    }

    pub open spec fn directories_have_flags(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat|
            i < X86_NUM_ENTRIES ==> {
                let entry = #[trigger] view_at(mem, pt, layer, ptr, i);
                entry.is_Directory() ==> entry.get_Directory_flag_RW()
                    && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
            }
    }

    pub open spec fn entry_mb0_bits_are_zero(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat|
            i < X86_NUM_ENTRIES ==> (#[trigger] entry_at_spec(
                mem,
                pt,
                layer,
                ptr,
                i,
            )).all_mb0_bits_are_zero()
    }

    /// Entries for super pages and huge pages use bit 12 to denote the PAT flag. We always set that
    /// flag to zero, which allows us to always use the same mask to get the address.
    pub open spec fn hp_pat_is_zero(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat|
            #![auto]
            i < X86_NUM_ENTRIES ==> entry_at_spec(mem, pt, layer, ptr, i).hp_pat_is_zero()
    }

    pub open spec fn ghost_pt_used_regions_pairwise_disjoint(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat, j: nat, r: MemRegion|
            i != j && i < pt.entries.len() && pt.entries[i as int].is_Some()
                && #[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(r) && j
                < pt.entries.len() && pt.entries[j as int].is_Some() ==> !(
            #[trigger] pt.entries[j as int].get_Some_0().used_regions.contains(r))
    }

    // TODO: this may be implied by the other ones
    pub open spec fn ghost_pt_region_notin_used_regions(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        forall|i: nat|
            i < pt.entries.len() && pt.entries[i as int].is_Some() ==> !(
            #[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(pt.region))
    }

    pub open spec fn ghost_pt_used_regions_rtrancl(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    ) -> bool {
        // reflexive
        &&& pt.used_regions.contains(pt.region)
        // transitive

        &&& forall|i: nat, r: MemRegion|
            #![trigger pt.entries[i as int].get_Some_0().used_regions.contains(r), pt.used_regions.contains(r)]
            i < pt.entries.len() && pt.entries[i as int].is_Some()
                && pt.entries[i as int].get_Some_0().used_regions.contains(r)
                ==> pt.used_regions.contains(r)
    }

    pub open spec fn interp_at(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
    ) -> l1::Directory
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES, 2nat,
    {
        decreases_when(inv_at(mem, pt, layer, ptr));
        l1::Directory {
            entries: interp_at_aux(mem, pt, layer, ptr, base_vaddr, seq![]),
            layer: layer,
            base_vaddr,
            arch: x86_arch_spec,
            // We don't have to check the flags because we know (from the invariant) that all
            // directories have these flags set.
            flags: permissive_flags,
        }
    }

    pub open spec fn interp_at_entry(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
        idx: nat,
    ) -> l1::NodeEntry
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - idx, 0nat,
    {
        decreases_when(inv_at(mem, pt, layer, ptr));
        match view_at(mem, pt, layer, ptr, idx) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let entry_base = x86_arch_spec.entry_base(layer, base_vaddr, idx);
                l1::NodeEntry::Directory(
                    interp_at(
                        mem,
                        pt.entries[idx as int].get_Some_0(),
                        layer + 1,
                        dir_addr,
                        entry_base,
                    ),
                )
            },
            GhostPageDirectoryEntry::Page {
                addr,
                flag_RW,
                flag_US,
                flag_XD,
                ..
            } => l1::NodeEntry::Page(
                PageTableEntry {
                    frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(layer) },
                    flags: Flags {
                        is_writable: flag_RW,
                        is_supervisor: !flag_US,
                        disable_execute: flag_XD,
                    },
                },
            ),
            GhostPageDirectoryEntry::Empty => l1::NodeEntry::Empty(),
        }
    }

    pub open spec fn interp_at_aux(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
        init: Seq<l1::NodeEntry>,
    ) -> Seq<l1::NodeEntry>
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat,
        when inv_at(mem, pt, layer, ptr)
    {
        if init.len() >= X86_NUM_ENTRIES {
            init
        } else {
            let entry = interp_at_entry(mem, pt, layer, ptr, base_vaddr, init.len());
            interp_at_aux(mem, pt, layer, ptr, base_vaddr, init.push(entry))
        }
    }

    pub open spec fn interp(mem: &mem::PageTableMemory, pt: PTDir) -> l1::Directory {
        interp_at(mem, pt, 0, mem.cr3_spec().base, 0)
    }

    proof fn lemma_inv_at_different_memory(
        mem1: &mem::PageTableMemory,
        mem2: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    )
        requires
            inv_at(mem1, pt, layer, ptr),
            forall|r: MemRegion|
                pt.used_regions.contains(r) ==> #[trigger] mem1.region_view(r) === mem2.region_view(
                    r,
                ),
            // Some parts of mem2's invariant that we should already know
            mem2.inv(),
            mem2.regions().contains(pt.region),
            pt.used_regions.subset_of(mem2.regions()),
        ensures
            inv_at(mem2, pt, layer, ptr),
        decreases X86_NUM_LAYERS - layer,
    {
        assert forall|i: nat| i < X86_NUM_ENTRIES implies view_at(mem2, pt, layer, ptr, i)
            == view_at(mem1, pt, layer, ptr, i) by {};
        assert forall|i: nat| i < X86_NUM_ENTRIES implies entry_at_spec(mem2, pt, layer, ptr, i)
            == entry_at_spec(mem1, pt, layer, ptr, i) by {};
        // Prove directories_obey_invariant_at(mem2, pt, layer, ptr)
        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
            let entry = #[trigger] view_at(mem2, pt, layer, ptr, i);
            entry.is_Directory() ==> inv_at(
                mem2,
                pt.entries[i as int].get_Some_0(),
                layer + 1,
                entry.get_Directory_addr(),
            )
        } by {
            let entry = view_at(mem2, pt, layer, ptr, i);
            if entry.is_Directory() {
                assert(directories_obey_invariant_at(mem1, pt, layer, ptr));
                lemma_inv_at_different_memory(
                    mem1,
                    mem2,
                    pt.entries[i as int].get_Some_0(),
                    layer + 1,
                    entry.get_Directory_addr(),
                );
            }
        };
    }

    proof fn lemma_interp_at_entry_different_memory(
        mem1: &mem::PageTableMemory,
        pt1: PTDir,
        mem2: &mem::PageTableMemory,
        pt2: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
        idx: nat,
    )
        requires
            idx < X86_NUM_ENTRIES,
            pt2.region == pt1.region,
            pt2.entries[idx as int] == pt1.entries[idx as int],
            inv_at(mem1, pt1, layer, ptr),
            inv_at(mem2, pt2, layer, ptr),
            mem1.spec_read(idx, pt1.region) == mem2.spec_read(idx, pt2.region),
            pt2.entries[idx as int].is_Some() ==> (forall|r: MemRegion|
                pt2.entries[idx as int].get_Some_0().used_regions.contains(r)
                    ==> #[trigger] mem1.region_view(r) == mem2.region_view(r)),
        ensures
            interp_at_entry(mem1, pt1, layer, ptr, base, idx) == interp_at_entry(
                mem2,
                pt2,
                layer,
                ptr,
                base,
                idx,
            ),
        decreases X86_NUM_LAYERS - layer,
    {
        match view_at(mem1, pt1, layer, ptr, idx) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let e_base = x86_arch_spec.entry_base(layer, base, idx);
                let dir_pt = pt1.entries[idx as int].get_Some_0();
                assert(directories_obey_invariant_at(mem1, pt1, layer, ptr));
                assert(directories_obey_invariant_at(mem2, pt2, layer, ptr));
                lemma_interp_at_aux_facts(mem1, dir_pt, layer + 1, dir_addr, e_base, seq![]);
                lemma_interp_at_aux_facts(mem2, dir_pt, layer + 1, dir_addr, e_base, seq![]);
                assert forall|i: nat| i < X86_NUM_ENTRIES implies interp_at_entry(
                    mem1,
                    dir_pt,
                    layer + 1,
                    dir_addr,
                    e_base,
                    i,
                ) == interp_at_entry(mem2, dir_pt, layer + 1, dir_addr, e_base, i)
                    && #[trigger] interp_at(
                    mem1,
                    dir_pt,
                    layer + 1,
                    dir_addr,
                    e_base,
                ).entries[i as int] == interp_at(
                    mem2,
                    dir_pt,
                    layer + 1,
                    dir_addr,
                    e_base,
                ).entries[i as int] by {
                    lemma_interp_at_entry_different_memory(
                        mem1,
                        dir_pt,
                        mem2,
                        dir_pt,
                        layer + 1,
                        dir_addr,
                        e_base,
                        i,
                    );
                };
                assert(interp_at(mem1, dir_pt, layer + 1, dir_addr, e_base).entries =~= interp_at(
                    mem2,
                    dir_pt,
                    layer + 1,
                    dir_addr,
                    e_base,
                ).entries);
            },
            _ => (),
        }
    }

    pub proof fn lemma_interp_at_facts(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            interp_at(mem, pt, layer, ptr, base_vaddr).inv(),
        ensures
            interp_at(mem, pt, layer, ptr, base_vaddr).base_vaddr == base_vaddr,
            interp_at(mem, pt, layer, ptr, base_vaddr).upper_vaddr() == x86_arch_spec.upper_vaddr(
                layer,
                base_vaddr,
            ),
            interp_at(mem, pt, layer, ptr, base_vaddr).interp().lower == base_vaddr,
            interp_at(mem, pt, layer, ptr, base_vaddr).interp().upper == x86_arch_spec.upper_vaddr(
                layer,
                base_vaddr,
            ),
            ({
                let res = interp_at(mem, pt, layer, ptr, base_vaddr);
                forall|j: nat|
                    j < res.entries.len() ==> res.entries[j as int] === #[trigger] interp_at_entry(
                        mem,
                        pt,
                        layer,
                        ptr,
                        base_vaddr,
                        j,
                    )
            }),
    {
        lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, seq![]);
        let res = interp_at(mem, pt, layer, ptr, base_vaddr);
        assert(res.pages_match_entry_size());
        assert(res.directories_are_in_next_layer());
        assert(res.directories_match_arch());
        assert(res.directories_obey_invariant());
        assert(res.directories_are_nonempty());
        assert(res.frames_aligned());
        res.lemma_inv_implies_interp_inv();
    }

    pub proof fn lemma_interp_at_facts_entries(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
        i: nat,
    )
        requires
            i < 512,
            inv_at(mem, pt, layer, ptr),
            interp_at(mem, pt, layer, ptr, base_vaddr).inv(),
        ensures
            ({
                let res = interp_at(mem, pt, layer, ptr, base_vaddr);
                match view_at(mem, pt, layer, ptr, i) {
                    GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                        &&& res.entries[i as int].is_Directory()
                        &&& res.entries[i as int].get_Directory_0() == interp_at(
                            mem,
                            pt.entries[i as int].get_Some_0(),
                            (layer + 1) as nat,
                            dir_addr,
                            x86_arch_spec.entry_base(layer, base_vaddr, i),
                        )
                    },
                    GhostPageDirectoryEntry::Page { addr, .. } => res.entries[i as int].is_Page()
                        && res.entries[i as int].get_Page_0().frame.base == addr,
                    GhostPageDirectoryEntry::Empty => res.entries[i as int].is_Empty(),
                }
            }),
    {
        lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, seq![]);
    }

    proof fn lemma_interp_at_aux_facts(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base_vaddr: nat,
        init: Seq<l1::NodeEntry>,
    )
        requires
            inv_at(mem, pt, layer, ptr),
        ensures
            interp_at_aux(mem, pt, layer, ptr, base_vaddr, init).len() == if init.len()
                > X86_NUM_ENTRIES {
                init.len()
            } else {
                X86_NUM_ENTRIES as nat
            },
            forall|j: nat|
                j < init.len() ==> #[trigger] interp_at_aux(
                    mem,
                    pt,
                    layer,
                    ptr,
                    base_vaddr,
                    init,
                )[j as int] == init[j as int],
            ({
                let res = interp_at_aux(mem, pt, layer, ptr, base_vaddr, init);
                &&& (forall|j: nat|
                    #![trigger res[j as int]]
                    init.len() <= j && j < res.len() ==> match view_at(mem, pt, layer, ptr, j) {
                        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                            &&& res[j as int].is_Directory()
                            &&& res[j as int].get_Directory_0() == interp_at(
                                mem,
                                pt.entries[j as int].get_Some_0(),
                                (layer + 1) as nat,
                                dir_addr,
                                x86_arch_spec.entry_base(layer, base_vaddr, j),
                            )
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => res[j as int].is_Page()
                            && res[j as int].get_Page_0().frame.base == addr,
                        GhostPageDirectoryEntry::Empty => res[j as int].is_Empty(),
                    })
                &&& (forall|j: nat|
                    init.len() <= j && j < res.len() ==> res[j as int]
                        == #[trigger] interp_at_entry(mem, pt, layer, ptr, base_vaddr, j))
            }),
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat,
    {
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            assert(directories_obey_invariant_at(mem, pt, layer, ptr));
            let entry = interp_at_entry(mem, pt, layer, ptr, base_vaddr, init.len());
            lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, init.push(entry));
        }
    }

    fn resolve_aux(
        mem: &mem::PageTableMemory,
        Ghost(pt): Ghost<PTDir>,
        layer: usize,
        ptr: usize,
        base: usize,
        vaddr: usize,
    ) -> (res: Result<(usize, PageTableEntryExec), ()>)
        requires
            inv_at(mem, pt, layer as nat, ptr),
            interp_at(mem, pt, layer as nat, ptr, base as nat).inv(),
            interp_at(mem, pt, layer as nat, ptr, base as nat).interp().accepted_resolve(
                vaddr as nat,
            ),
            base <= vaddr < MAX_BASE,
        ensures
    // Refinement of l1

            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@))
                === interp_at(mem, pt, layer as nat, ptr, base as nat).resolve(vaddr as nat),
            // Refinement of l0
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@))
                === interp_at(mem, pt, layer as nat, ptr, base as nat).interp().resolve(
                vaddr as nat,
            ),
    // decreases X86_NUM_LAYERS - layer

    {
        proof {
            lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat);
        }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof {
            indexing::lemma_index_from_base_and_addr(
                base as nat,
                vaddr as nat,
                x86_arch_spec.entry_size(layer as nat),
                X86_NUM_ENTRIES as nat,
            );
        }
        let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
        let interp: Ghost<l1::Directory> = Ghost(
            interp_at(mem, pt, layer as nat, ptr, base as nat),
        );
        proof {
            interp@.lemma_resolve_structure_assertions(vaddr as nat, idx as nat);
            interp@.lemma_resolve_refines(vaddr as nat);
        }
        if entry.is_mapping() {
            let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
            proof {
                indexing::lemma_entry_base_from_index(
                    base as nat,
                    idx as nat,
                    x86_arch_spec.entry_size(layer as nat),
                );
                assert(entry_base <= vaddr);
            }
            if entry.is_dir(layer) {
                assert(entry@.is_Directory());
                let dir_addr = entry.address() as usize;
                assert(pt.entries[idx as int].is_Some());
                let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
                assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
                proof {
                    assert(interp@.inv());
                    assert(interp@.directories_obey_invariant());
                    assert(interp@.entries[idx as int].is_Directory());
                    assert(interp@.entries[idx as int].get_Directory_0().inv());
                    assert(l1::NodeEntry::Directory(
                        interp_at(mem, dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat),
                    ) === interp@.entries[idx as int]);
                    assert(inv_at(mem, dir_pt@, (layer + 1) as nat, dir_addr));
                }
                let res = resolve_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr);
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@))
                    === interp@.resolve(vaddr as nat));
                res
            } else {
                assert(entry@.is_Page());
                assert(interp@.entries[idx as int].is_Page());
                let pte = PageTableEntryExec {
                    frame: MemRegionExec {
                        base: entry.address() as usize,
                        size: x86_arch_exec().entry_size(layer),
                    },
                    flags: entry.flags(),
                };
                let res = Ok((entry_base, pte));
                proof {
                    if interp@.resolve(vaddr as nat).is_Ok() {
                        assert(interp@.entries[idx as int].get_Page_0() === interp@.resolve(
                            vaddr as nat,
                        ).get_Ok_0().1);
                        assert(interp@.entries[idx as int] === interp_at_entry(
                            mem,
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                            idx as nat,
                        ));
                    }
                }
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).0)
                    === l1::result_map_ok(
                    interp@.resolve(vaddr as nat),
                    |v: (nat, PageTableEntry)| v.0,
                ));
                assert(l1::result_map_ok(
                    res,
                    |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.frame,
                ) === l1::result_map_ok(
                    interp@.resolve(vaddr as nat),
                    |v: (nat, PageTableEntry)| v.1.frame,
                ));
                assert(l1::result_map_ok(
                    res,
                    |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.flags,
                ) === l1::result_map_ok(
                    interp@.resolve(vaddr as nat),
                    |v: (nat, PageTableEntry)| v.1.flags,
                ));
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@))
                    === interp@.resolve(vaddr as nat));
                res
            }
        } else {
            assert(entry@.is_Empty());
            assert(interp@.entries[idx as int].is_Empty());
            assert(l1::result_map_ok(Err(()), |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@))
                === interp@.resolve(vaddr as nat));
            Err(())
        }
    }

    pub fn resolve(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, vaddr: usize) -> (res:
        Result<(usize, PageTableEntryExec), ()>)
        requires
            inv(mem, pt),
            interp(mem, pt).inv(),
            interp(mem, pt).interp().accepted_resolve(vaddr as nat),
            vaddr < MAX_BASE,
        ensures
    // Refinement of l1

            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(
                mem,
                pt,
            ).resolve(vaddr as nat),
            // Refinement of l0
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(
                mem,
                pt,
            ).interp().resolve(vaddr as nat),
    {
        proof {
            ambient_arith();
        }
        let res = resolve_aux(mem, Ghost(pt), 0, mem.cr3().base, 0, vaddr);
        res
    }

    pub open spec fn accepted_mapping(vaddr: nat, pte: PageTableEntry) -> bool {
        // Can't map pages in PML4, i.e. layer 0
        &&& x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size, 1)
        &&& pte.frame.base <= MAX_PHYADDR
    }

    fn map_frame_aux(
        mem: &mut mem::PageTableMemory,
        Ghost(pt): Ghost<PTDir>,
        layer: usize,
        ptr: usize,
        base: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (res: Result<Ghost<(PTDir, Set<MemRegion>)>, ()>)
        requires
            inv_at(&*old(mem), pt, layer as nat, ptr),
            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
            old(mem).inv(),
            old(mem).alloc_available_pages() >= 3 - layer,
            accepted_mapping(vaddr as nat, pte@),
            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).accepted_mapping(
                vaddr as nat,
                pte@,
            ),
            base <= vaddr < MAX_BASE,
        ensures
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    // We return the regions that we added
                    &&& mem.regions() === old(mem).regions().union(new_regions)
                    &&& pt_res.used_regions === pt.used_regions.union(
                        new_regions,
                    )
                    // and only those we added

                    &&& new_regions.disjoint(old(mem).regions())
                    &&& (forall|r: MemRegion|
                        new_regions.contains(r) ==> !(#[trigger] pt.used_regions.contains(
                            r,
                        )))
                    // Invariant preserved

                    &&& inv_at(
                        mem,
                        pt_res,
                        layer as nat,
                        ptr,
                    )
                    // We only touch already allocated regions if they're in pt.used_regions

                    &&& (forall|r: MemRegion|
                        !(#[trigger] pt.used_regions.contains(r)) && !(new_regions.contains(r))
                            ==> mem.region_view(r) === old(mem).region_view(r))
                    &&& pt_res.region === pt.region
                },
                Err(e) => {
                    // If error, unchanged
                    &&& mem === old(mem)
                },
            },
            // Refinement of l1
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    Ok(interp_at(mem, pt_res, layer as nat, ptr, base as nat)) === interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).map_frame(vaddr as nat, pte@)
                },
                Err(e) => Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                    &*old(mem),
                    pt,
                    layer as nat,
                    ptr,
                    base as nat,
                ).map_frame(vaddr as nat, pte@),
            },
            mem.cr3_spec() == old(
                mem,
            ).cr3_spec(),
    // decreases X86_NUM_LAYERS - layer

    {
        proof {
            lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat);
        }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof {
            assert({
                &&& between(
                    vaddr as nat,
                    x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat),
                    x86_arch_spec.next_entry_base(layer as nat, base as nat, idx as nat),
                )
                &&& aligned(vaddr as nat, x86_arch_spec.entry_size(layer as nat)) ==> vaddr
                    == x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat)
                &&& idx < X86_NUM_ENTRIES
            }) by {
                let es = x86_arch_spec.entry_size(layer as nat);
                assert(aligned(base as nat, es)) by {
                    lib::mod_mult_zero_implies_mod_zero(base as nat, es, X86_NUM_ENTRIES as nat);
                };
                indexing::lemma_index_from_base_and_addr(
                    base as nat,
                    vaddr as nat,
                    es,
                    X86_NUM_ENTRIES as nat,
                );
            };
            lemma_interp_at_facts_entries(
                &*old(mem),
                pt,
                layer as nat,
                ptr,
                base as nat,
                idx as nat,
            );
        }
        let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
        let interp: Ghost<l1::Directory> = Ghost(
            interp_at(mem, pt, layer as nat, ptr, base as nat),
        );
        proof {
            interp@.lemma_map_frame_structure_assertions(vaddr as nat, pte@, idx as nat);
            interp@.lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
        }
        let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(
                base as nat,
                idx as nat,
                x86_arch_spec.entry_size(layer as nat),
            );
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                if x86_arch_exec().entry_size(layer) == pte.frame.size {
                    assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).map_frame(vaddr as nat, pte@));
                    Err(())
                } else {
                    let dir_addr = entry.address() as usize;
                    assert(pt.entries[idx as int].is_Some());
                    let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
                    assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
                    match map_frame_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr, pte) {
                        Ok(rec_res) => {
                            let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                            let new_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);
                            assert(dir_pt_res@.used_regions === dir_pt@.used_regions.union(
                                new_regions@,
                            ));
                            assert(inv_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr));
                            assert(Ok(
                                interp_at(
                                    mem,
                                    dir_pt_res@,
                                    (layer + 1) as nat,
                                    dir_addr,
                                    entry_base as nat,
                                ),
                            ) === interp_at(
                                &*old(mem),
                                dir_pt@,
                                (layer + 1) as nat,
                                dir_addr,
                                entry_base as nat,
                            ).map_frame(vaddr as nat, pte@));
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt.region,
                                    entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt.used_regions.union(new_regions@),
                                },
                            );
                            assert(idx < pt.entries.len());
                            assert(pt_res@.region === pt.region);
                            assert(!new_regions@.contains(pt_res@.region));
                            assert(!dir_pt_res@.used_regions.contains(pt_res@.region));
                            // None of the entries at this level change
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies view_at(
                                mem,
                                pt_res@,
                                layer as nat,
                                ptr,
                                i,
                            ) == view_at(&*old(mem), pt, layer as nat, ptr, i) by {};
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies entry_at_spec(
                                mem,
                                pt_res@,
                                layer as nat,
                                ptr,
                                i,
                            ) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i) by {};
                            assert(inv_at(mem, pt_res@, layer as nat, ptr) && Ok(
                                interp_at(mem, pt_res@, layer as nat, ptr, base as nat),
                            ) === interp_at(
                                &*old(mem),
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                            ).map_frame(vaddr as nat, pte@)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                    entry.is_Directory() == (
                                    #[trigger] pt_res@.entries[i as int]).is_Some()
                                } by {
                                    assert(mem.region_view(pt_res@.region) === mem.region_view(
                                        pt_res@.region,
                                    ));
                                    let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                    if i == idx {
                                    } else {
                                        assert(pt.entries[i as int] === pt_res@.entries[i as int]);
                                        assert(entry === view_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            i,
                                        ));
                                        assert(entry.is_Directory()
                                            == pt_res@.entries[i as int].is_Some());
                                    }
                                };
                                assert(ghost_pt_matches_structure(mem, pt_res@, layer as nat, ptr));
                                assert(ghost_pt_used_regions_rtrancl(
                                    mem,
                                    pt_res@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert(ghost_pt_region_notin_used_regions(
                                    mem,
                                    pt_res@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert forall|i: nat, j: nat, r: MemRegion|
                                    i != j && i < pt_res@.entries.len()
                                        && pt_res@.entries[i as int].is_Some()
                                        && #[trigger] pt_res@.entries[i as int].get_Some_0().used_regions.contains(
                                    r) && j < pt_res@.entries.len()
                                        && pt_res@.entries[j as int].is_Some() implies !(
                                #[trigger] pt_res@.entries[j as int].get_Some_0().used_regions.contains(
                                r)) by {
                                    assert(ghost_pt_used_regions_pairwise_disjoint(
                                        mem,
                                        pt,
                                        layer as nat,
                                        ptr,
                                    ));
                                    if j == idx {
                                        assert(pt_res@.entries[j as int].get_Some_0()
                                            === dir_pt_res@);
                                        assert(pt_res@.entries[i as int] === pt.entries[i as int]);
                                        if new_regions@.contains(r) {
                                            assert(!dir_pt@.used_regions.contains(r));
                                            assert(!old(mem).regions().contains(r));
                                            assert(!dir_pt_res@.used_regions.contains(r));
                                        } else {
                                            if dir_pt@.used_regions.contains(r) {
                                                assert(pt.used_regions.contains(r));
                                                assert(old(mem).regions().contains(r));
                                                assert(!dir_pt_res@.used_regions.contains(r));
                                            }
                                        }
                                    } else {
                                        if i == idx {
                                            assert(pt_res@.entries[i as int].get_Some_0()
                                                === dir_pt_res@);
                                            assert(pt_res@.entries[j as int]
                                                === pt.entries[j as int]);
                                            if new_regions@.contains(r) {
                                                assert(dir_pt_res@.used_regions.contains(r));
                                                assert(!dir_pt@.used_regions.contains(r));
                                                assert(!old(mem).regions().contains(r));
                                                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(
                                                r));
                                            } else {
                                                assert(dir_pt@.used_regions.contains(r));
                                                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(
                                                r));
                                            }
                                        } else {
                                            assert(pt_res@.entries[i as int]
                                                === pt.entries[i as int]);
                                            assert(pt_res@.entries[j as int]
                                                === pt.entries[j as int]);
                                        }
                                    }
                                };
                                assert(ghost_pt_used_regions_pairwise_disjoint(
                                    mem,
                                    pt_res@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] view_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    );
                                    entry.is_Directory() ==> {
                                        &&& inv_at(
                                            mem,
                                            pt_res@.entries[i as int].get_Some_0(),
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        )
                                    }
                                } by {
                                    let entry = #[trigger] view_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    );
                                    if i == idx {
                                        assert(pt_res@.entries[i as int].get_Some_0()
                                            === dir_pt_res@);
                                        assert(entry.get_Directory_addr() === dir_addr);
                                        assert(inv_at(
                                            mem,
                                            pt_res@.entries[i as int].get_Some_0(),
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        ));
                                    } else {
                                        assert(directories_obey_invariant_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                        ));
                                        assert(pt.entries[i as int] === pt_res@.entries[i as int]);
                                        assert(entry === view_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            i,
                                        ));
                                        assert(entry === view_at(
                                            &*old(mem),
                                            pt_res@,
                                            layer as nat,
                                            ptr,
                                            i,
                                        ));
                                        if entry.is_Directory() {
                                            let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                            assert(ghost_pt_used_regions_pairwise_disjoint(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                            ));
                                            assert forall|r: MemRegion| #[trigger]
                                                pt_entry.used_regions.contains(
                                                    r,
                                                ) implies !new_regions@.contains(r) by {
                                                assert(pt_entry.used_regions.contains(r));
                                                assert(old(mem).regions().contains(r));
                                            };
                                            assert(forall|r: MemRegion| #[trigger]
                                                pt_entry.used_regions.contains(r)
                                                    ==> !dir_pt@.used_regions.contains(r));
                                            assert(forall|r: MemRegion|
                                                pt_entry.used_regions.contains(r)
                                                    ==> #[trigger] mem.region_view(r)
                                                    === mem.region_view(r));
                                            assert(inv_at(
                                                &*old(mem),
                                                pt.entries[i as int].get_Some_0(),
                                                (layer + 1) as nat,
                                                entry.get_Directory_addr(),
                                            ));
                                            assert(forall|r: MemRegion|
                                                pt_res@.entries[i as int].get_Some_0().used_regions.contains(
                                                r) ==> #[trigger] mem.region_view(r) === old(
                                                    mem,
                                                ).region_view(r));
                                            assert(pt_res@.entries[i as int].is_Some());
                                            assert(pt_res@.entries[i as int].get_Some_0().used_regions
                                                === pt.entries[i as int].get_Some_0().used_regions);
                                            lemma_inv_at_different_memory(
                                                &*old(mem),
                                                mem,
                                                pt.entries[i as int].get_Some_0(),
                                                (layer + 1) as nat,
                                                entry.get_Directory_addr(),
                                            );
                                            assert(inv_at(
                                                mem,
                                                pt_res@.entries[i as int].get_Some_0(),
                                                (layer + 1) as nat,
                                                entry.get_Directory_addr(),
                                            ));
                                        }
                                    }
                                };
                                assert(directories_obey_invariant_at(
                                    mem,
                                    pt_res@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert(inv_at(mem, pt_res@, layer as nat, ptr));
                                assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat))
                                    === interp_at(
                                    &*old(mem),
                                    pt,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                ).map_frame(vaddr as nat, pte@)) by {
                                    lemma_interp_at_aux_facts(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        seq![],
                                    );
                                    assert(pt_res@.region === pt.region);
                                    // recursive postcondition:
                                    assert(Ok(
                                        interp_at(
                                            mem,
                                            dir_pt_res@,
                                            (layer + 1) as nat,
                                            dir_addr,
                                            entry_base as nat,
                                        ),
                                    ) === interp_at(
                                        &*old(mem),
                                        dir_pt@,
                                        (layer + 1) as nat,
                                        dir_addr,
                                        entry_base as nat,
                                    ).map_frame(vaddr as nat, pte@));
                                    assert(inv_at(mem, pt_res@, layer as nat, ptr));
                                    assert(inv_at(&*old(mem), pt, layer as nat, ptr));
                                    assert(pt_res@.entries[idx as int].is_Some());
                                    assert(pt_res@.entries[idx as int].get_Some_0()
                                        === dir_pt_res@);
                                    assert(forall|i: nat|
                                        i < X86_NUM_ENTRIES && i != idx ==> pt.entries[i as int]
                                            === pt_res@.entries[i as int]);
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES && i != idx implies interp_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries[i as int] === #[trigger] interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).map_frame(
                                        vaddr as nat,
                                        pte@,
                                    ).get_Ok_0().entries[i as int] by {
                                        assert(interp_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                        ).map_frame(vaddr as nat, pte@).is_Ok());
                                        assert(interp_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                        ).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int]
                                            === interp_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                        ).entries[i as int]);
                                        assert(interp_at(
                                            mem,
                                            pt_res@,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                        ).entries[i as int] === interp_at_entry(
                                            mem,
                                            pt_res@,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                            i,
                                        ));
                                        assert(interp_at(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                        ).entries[i as int] === interp_at_entry(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                            i,
                                        ));
                                        if pt_res@.entries[i as int].is_Some() {
                                            let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                            assert(ghost_pt_used_regions_pairwise_disjoint(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                            ));
                                            assert forall|r: MemRegion| #[trigger]
                                                pt_entry.used_regions.contains(
                                                    r,
                                                ) implies !new_regions@.contains(r) by {
                                                assert(pt_entry.used_regions.contains(r));
                                                assert(old(mem).regions().contains(r));
                                            };
                                            assert(forall|r: MemRegion| #[trigger]
                                                pt_entry.used_regions.contains(r)
                                                    ==> !dir_pt_res@.used_regions.contains(r));
                                            assert(forall|r: MemRegion|
                                                pt_entry.used_regions.contains(r)
                                                    ==> #[trigger] old(mem).region_view(r)
                                                    === mem.region_view(r));
                                        }
                                        lemma_interp_at_entry_different_memory(
                                            &*old(mem),
                                            pt,
                                            mem,
                                            pt_res@,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                            i,
                                        );
                                        assert(interp_at_entry(
                                            mem,
                                            pt_res@,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                            i,
                                        ) === interp_at_entry(
                                            &*old(mem),
                                            pt,
                                            layer as nat,
                                            ptr,
                                            base as nat,
                                            i,
                                        ));
                                    };
                                    assert(interp_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries[idx as int] === interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                                    assert_seqs_equal!(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries, interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                    assert(interp_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries === interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                    assert(Ok(
                                        interp_at(mem, pt_res@, layer as nat, ptr, base as nat),
                                    ) === interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).map_frame(vaddr as nat, pte@));
                                };
                            };
                            // posts
                            assert forall|r: MemRegion|
                                !pt.used_regions.contains(r) && !new_regions@.contains(
                                    r,
                                ) implies #[trigger] mem.region_view(r) === old(mem).region_view(
                                r,
                            ) by {
                                assert(!dir_pt@.used_regions.contains(r));
                            };
                            assert(mem.regions() === old(mem).regions().union(new_regions@));
                            assert(pt_res@.used_regions === pt.used_regions.union(new_regions@));
                            assert(pt_res@.region === pt.region);
                            Ok(Ghost((pt_res@, new_regions@)))
                        },
                        Err(e) => {
                            assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat))
                                === interp_at(
                                &*old(mem),
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                            ).map_frame(vaddr as nat, pte@));
                            Err(e)
                        },
                    }
                }
            } else {
                assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                    &*old(mem),
                    pt,
                    layer as nat,
                    ptr,
                    base as nat,
                ).map_frame(vaddr as nat, pte@));
                Err(())
            }
        } else {
            if x86_arch_exec().entry_size(layer) == pte.frame.size {
                proof {
                    assert_by_contradiction!(layer > 0, {
                            let iprime = choose|i: nat| 0 < i && i < X86_NUM_LAYERS && #[trigger] x86_arch_spec.entry_size(i) == pte.frame.size;
                            assert(x86_arch_spec.entry_size(0) == pte.frame.size);
                            assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1));
                            assert forall|i: nat|
                                0 < i < X86_NUM_LAYERS
                                implies
                                x86_arch_spec.entry_size(0) >= #[trigger] x86_arch_spec.entry_size(i)
                            by {
                                x86_arch_spec.lemma_entry_sizes_increase(0, i);
                            };
                            assert(false);
                        });
                    let frame_base = pte.frame.base as u64;
                    assert(addr_is_zero_padded(layer as nat, frame_base, true)) by {
                        assert(x86_arch_spec.contains_entry_size_at_index_atleast(
                            pte.frame.size as nat,
                            1,
                        ));
                        assert(x86_arch_spec.entry_size(layer as nat) == pte.frame.size);
                        assert(aligned(pte.frame.base as nat, pte.frame.size as nat));
                        lemma_aligned_addr_mask_facts(frame_base);
                        if layer == 1 {
                            assert(x86_arch_spec.entry_size(1) == L1_ENTRY_SIZE);
                            assert(frame_base & MASK_L1_PG_ADDR == frame_base & MASK_ADDR);
                        } else if layer == 2 {
                            assert(x86_arch_spec.entry_size(2) == L2_ENTRY_SIZE);
                            assert(frame_base & MASK_L2_PG_ADDR == frame_base & MASK_ADDR);
                        } else if layer == 3 {
                            assert(x86_arch_spec.entry_size(3) == L3_ENTRY_SIZE);
                            assert(frame_base & MASK_L3_PG_ADDR == frame_base & MASK_ADDR);
                        } else {
                            assert(false);
                        }
                    };
                    assert(frame_base & MASK_ADDR == frame_base) by {
                        lemma_aligned_addr_mask_facts(frame_base);
                    };
                }
                let new_page_entry = PageDirectoryEntry::new_page_entry(layer, pte);
                let pwmem: Ghost<mem::PageTableMemory> = Ghost(*mem);
                mem.write(ptr, idx, Ghost(pt.region), new_page_entry.entry);
                assert(mem.region_view(pt.region) === pwmem@.region_view(pt.region).update(
                    idx as int,
                    new_page_entry.entry,
                ));
                assert forall|i: nat| i < X86_NUM_ENTRIES implies #[trigger] view_at(
                    mem,
                    pt,
                    layer as nat,
                    ptr,
                    i,
                ) == if i == idx {
                    new_page_entry@
                } else {
                    view_at(&*old(mem), pt, layer as nat, ptr, i)
                } by {};
                assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies entry_at_spec(
                    mem,
                    pt,
                    layer as nat,
                    ptr,
                    i,
                ) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i) by {};
                assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr)) by {
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        let entry = #[trigger] view_at(mem, pt, layer as nat, ptr, i);
                        entry.is_Directory() ==> {
                            &&& inv_at(
                                mem,
                                pt.entries[i as int].get_Some_0(),
                                (layer + 1) as nat,
                                entry.get_Directory_addr(),
                            )
                        }
                    } by {
                        let entry = view_at(mem, pt, layer as nat, ptr, i);
                        if i != idx {
                            assert(directories_obey_invariant_at(
                                &*old(mem),
                                pt,
                                layer as nat,
                                ptr,
                            ));
                            if entry.is_Directory() {
                                lemma_inv_at_different_memory(
                                    &*old(mem),
                                    mem,
                                    pt.entries[i as int].get_Some_0(),
                                    (layer + 1) as nat,
                                    entry.get_Directory_addr(),
                                );
                            }
                        }
                    };
                };
                assert(inv_at(mem, pt, layer as nat, ptr));
                assert(Ok(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                    &*old(mem),
                    pt,
                    layer as nat,
                    ptr,
                    base as nat,
                ).map_frame(vaddr as nat, pte@)) by {
                    lemma_interp_at_aux_facts(mem, pt, layer as nat, ptr, base as nat, seq![]);
                    assert(inv_at(mem, pt, layer as nat, ptr));
                    assert(inv_at(&*old(mem), pt, layer as nat, ptr));
                    assert(pt.entries[idx as int].is_None());
                    assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies interp_at(
                        mem,
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).entries[i as int] === #[trigger] interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by {
                        assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(
                            vaddr as nat,
                            pte@,
                        ).is_Ok());
                        assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(
                            vaddr as nat,
                            pte@,
                        ).get_Ok_0().entries[i as int] === interp_at(
                            &*old(mem),
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                        ).entries[i as int]);
                        assert(interp_at(
                            &*old(mem),
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                        ).entries[i as int] === interp_at_entry(
                            &*old(mem),
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                            i,
                        ));
                        assert(old(mem).spec_read(i, pt.region) === mem.spec_read(i, pt.region));
                        lemma_interp_at_entry_different_memory(
                            &*old(mem),
                            pt,
                            mem,
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                            i,
                        );
                        assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, i)
                            === interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, i));
                    };
                    let new_interp = interp_at(mem, pt, layer as nat, ptr, base as nat);
                    assert(new_interp.entries[idx as int] === interp_at_entry(
                        mem,
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                        idx as nat,
                    ));
                    assert(view_at(mem, pt, layer as nat, ptr, idx as nat) === new_page_entry@);
                    assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat)
                        === l1::NodeEntry::Page(pte@));
                    assert(new_interp.entries[idx as int] == interp@.map_frame(
                        vaddr as nat,
                        pte@,
                    ).get_Ok_0().entries[idx as int]);
                    assert(new_interp.entries =~= interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                    assert(Ok(new_interp) === interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).map_frame(vaddr as nat, pte@));
                };
                // posts
                assert(forall|r: MemRegion|
                    !pt.used_regions.contains(r) ==> #[trigger] mem.region_view(r) === old(
                        mem,
                    ).region_view(r));
                proof {
                    lemma_set_union_empty_equals_set::<MemRegion>(mem.regions());
                    lemma_set_union_empty_equals_set::<MemRegion>(pt.used_regions);
                }
                assert(forall|r: MemRegion|
                    set![].contains(r) ==> !(#[trigger] old(mem).regions().contains(r)));
                assert(forall|r: MemRegion|
                    set![].contains(r) ==> !(#[trigger] pt.used_regions.contains(r)));
                assert(pt.region === pt.region);
                Ok(Ghost((pt, set![])))
            } else {
                let new_dir_region = mem.alloc_page();
                let new_dir_ptr = new_dir_region.base;
                let new_dir_ptr_u64 = new_dir_ptr as u64;
                let new_dir_pt: Ghost<PTDir> = Ghost(
                    PTDir {
                        region: new_dir_region@,
                        entries: new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None),
                        used_regions: set![new_dir_region@],
                    },
                );
                assert(new_dir_ptr_u64 & MASK_DIR_ADDR == new_dir_ptr_u64) by {
                    lemma_page_aligned_implies_mask_dir_addr_is_identity();
                };
                let new_dir_entry = PageDirectoryEntry::new_dir_entry(layer, new_dir_ptr_u64);
                mem.write(ptr, idx, Ghost(pt.region), new_dir_entry.entry);
                // After writing the new empty directory entry we prove that the resulting state
                // satisfies the invariant and that the interpretation remains unchanged.
                let pt_with_empty: Ghost<PTDir> = Ghost(
                    PTDir {
                        region: pt.region,
                        entries: pt.entries.update(idx as int, Some(new_dir_pt@)),
                        used_regions: pt.used_regions.insert(new_dir_pt@.region),
                    },
                );
                // For easier reference we take a snapshot of mem here. In the subsequent proofs
                // (after the recursive call) we have old(mem), mem_with_empty and mem to refer
                // to each relevant state.
                let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);
                proof {
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies #[trigger] view_at(
                        mem_with_empty@,
                        pt_with_empty@,
                        layer as nat,
                        ptr,
                        i,
                    ) == if i == idx {
                        new_dir_entry@
                    } else {
                        view_at(&*old(mem), pt, layer as nat, ptr, i)
                    } by {};
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies #[trigger] entry_at_spec(
                        mem_with_empty@,
                        pt_with_empty@,
                        layer as nat,
                        ptr,
                        i,
                    ) == if i == idx {
                        new_dir_entry
                    } else {
                        entry_at_spec(&*old(mem), pt, layer as nat, ptr, i)
                    } by {};
                    assert(pt_with_empty@.region === pt.region);
                    lemma_new_seq::<u64>(512nat, 0u64);
                    lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
                    assert(new_dir_pt@.entries.len() == 512);
                    assert(new_dir_region@.contains(new_dir_ptr as nat));
                    assert(mem_with_empty@.region_view(new_dir_region@) === new_seq(512nat, 0u64));
                    lemma_zeroed_page_implies_empty_at(
                        mem_with_empty@,
                        new_dir_pt@,
                        (layer + 1) as nat,
                        new_dir_ptr,
                    );
                    assert(empty_at(mem_with_empty@, new_dir_pt@, (layer + 1) as nat, new_dir_ptr));
                    assert(inv_at(mem_with_empty@, new_dir_pt@, (layer + 1) as nat, new_dir_ptr));
                    assert(forall|r: MemRegion|
                        r !== new_dir_pt@.region && r !== pt_with_empty@.region
                            ==> mem_with_empty@.region_view(r) === old(mem).region_view(r));
                    assert(mem_with_empty@.region_view(pt_with_empty@.region) === old(
                        mem,
                    ).region_view(pt_with_empty@.region).update(idx as int, new_dir_entry.entry));
                    assert(inv_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr)) by {
                        assert(ghost_pt_matches_structure(
                            mem_with_empty@,
                            pt_with_empty@,
                            layer as nat,
                            ptr,
                        ));
                        assert(directories_obey_invariant_at(
                            mem_with_empty@,
                            pt_with_empty@,
                            layer as nat,
                            ptr,
                        )) by {
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] view_at(
                                    mem_with_empty@,
                                    pt_with_empty@,
                                    layer as nat,
                                    ptr,
                                    i,
                                );
                                entry.is_Directory() ==> inv_at(
                                    mem_with_empty@,
                                    pt_with_empty@.entries[i as int].get_Some_0(),
                                    (layer + 1) as nat,
                                    entry.get_Directory_addr(),
                                )
                            } by {
                                let entry = view_at(
                                    mem_with_empty@,
                                    pt_with_empty@,
                                    layer as nat,
                                    ptr,
                                    i,
                                );
                                if i == idx {
                                } else {
                                    if entry.is_Directory() {
                                        let pt_entry = pt.entries[i as int].get_Some_0();
                                        assert(inv_at(
                                            &*old(mem),
                                            pt_entry,
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        ));
                                        assert(pt.entries[i as int]
                                            == pt_with_empty@.entries[i as int]);
                                        assert(old(mem).regions().contains(pt_entry.region));
                                        lemma_inv_at_different_memory(
                                            &*old(mem),
                                            mem_with_empty@,
                                            pt_entry,
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        );
                                        assert(inv_at(
                                            mem_with_empty@,
                                            pt_with_empty@.entries[i as int].get_Some_0(),
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        ));
                                    }
                                }
                            };
                        };
                    };
                    lemma_empty_at_interp_at_equal_l1_empty_dir(
                        mem_with_empty@,
                        pt_with_empty@,
                        layer as nat,
                        ptr,
                        base as nat,
                        idx as nat,
                    );
                    interp@.lemma_new_empty_dir(idx as nat);
                    lemma_interp_at_aux_facts(
                        mem_with_empty@,
                        pt_with_empty@,
                        layer as nat,
                        ptr,
                        base as nat,
                        seq![],
                    );
                }
                let new_dir_interp = Ghost(
                    interp_at(
                        mem_with_empty@,
                        new_dir_pt@,
                        (layer + 1) as nat,
                        new_dir_ptr,
                        entry_base as nat,
                    ),
                );
                proof {
                    assert(forall|i: nat|
                        i < new_dir_interp@.entries.len() ==> new_dir_interp@.entries[i as int]
                            === l1::NodeEntry::Empty());
                    assert(new_dir_interp@.entries =~= interp@.new_empty_dir(idx as nat).entries);
                    assert(new_dir_interp@ == interp@.new_empty_dir(idx as nat));
                }
                match map_frame_aux(
                    mem,
                    new_dir_pt,
                    layer + 1,
                    new_dir_ptr,
                    entry_base,
                    vaddr,
                    pte,
                ) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                        let dir_new_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);
                        let pt_final: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt_with_empty@.region,
                                entries: pt_with_empty@.entries.update(
                                    idx as int,
                                    Some(dir_pt_res@),
                                ),
                                used_regions: pt_with_empty@.used_regions.union(dir_new_regions@),
                            },
                        );
                        let new_regions: Ghost<Set<MemRegion>> = Ghost(
                            dir_new_regions@.insert(new_dir_region@),
                        );
                        proof {
                            assert(idx < pt_with_empty@.entries.len());
                            assert(!dir_new_regions@.contains(pt_final@.region));
                            assert(!new_dir_pt@.used_regions.contains(pt_final@.region));
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies #[trigger] view_at(
                                mem,
                                pt_final@,
                                layer as nat,
                                ptr,
                                i,
                            ) == if i == idx {
                                new_dir_entry@
                            } else {
                                view_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr, i)
                            } by {};
                            assert forall|i: nat|
                                i < X86_NUM_ENTRIES implies #[trigger] entry_at_spec(
                                mem,
                                pt_final@,
                                layer as nat,
                                ptr,
                                i,
                            ) == if i == idx {
                                new_dir_entry
                            } else {
                                entry_at_spec(mem_with_empty@, pt_with_empty@, layer as nat, ptr, i)
                            } by {};
                            assert(inv_at(mem, pt_final@, layer as nat, ptr)) by {
                                assert(ghost_pt_matches_structure(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                )) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] view_at(
                                            mem,
                                            pt_final@,
                                            layer as nat,
                                            ptr,
                                            i,
                                        );
                                        entry.is_Directory()
                                            == pt_final@.entries[i as int].is_Some()
                                    } by {
                                        assert(directories_obey_invariant_at(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        assert(ghost_pt_matches_structure(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        if i == idx {
                                        } else {
                                        }
                                    };
                                };
                                assert(directories_obey_invariant_at(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                )) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] view_at(
                                            mem,
                                            pt_final@,
                                            layer as nat,
                                            ptr,
                                            i,
                                        );
                                        entry.is_Directory() ==> inv_at(
                                            mem,
                                            pt_final@.entries[i as int].get_Some_0(),
                                            (layer + 1) as nat,
                                            entry.get_Directory_addr(),
                                        )
                                    } by {
                                        let entry = view_at(mem, pt_final@, layer as nat, ptr, i);
                                        assert(directories_obey_invariant_at(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        assert(ghost_pt_matches_structure(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        assert(ghost_pt_used_regions_rtrancl(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        if i == idx {
                                        } else {
                                            assert(entry == view_at(
                                                mem_with_empty@,
                                                pt_with_empty@,
                                                layer as nat,
                                                ptr,
                                                i,
                                            ));
                                            assert(pt_final@.entries[i as int]
                                                === pt_with_empty@.entries[i as int]);
                                            if entry.is_Directory() {
                                                assert(pt_with_empty@.entries[i as int].is_Some());
                                                let pt_entry =
                                                    pt_with_empty@.entries[i as int].get_Some_0();
                                                assert(pt_with_empty@.entries[i as int]
                                                    === pt_final@.entries[i as int]);
                                                assert(pt_with_empty@.entries[i as int].get_Some_0()
                                                    === pt_final@.entries[i as int].get_Some_0());
                                                assert(forall|r: MemRegion| #[trigger]
                                                    pt_entry.used_regions.contains(r)
                                                        ==> !dir_new_regions@.contains(r)
                                                        && !new_dir_pt@.used_regions.contains(r));
                                                assert(forall|r: MemRegion|
                                                    pt_entry.used_regions.contains(r)
                                                        ==> #[trigger] mem_with_empty@.region_view(
                                                        r,
                                                    ) === mem.region_view(r));
                                                lemma_inv_at_different_memory(
                                                    mem_with_empty@,
                                                    mem,
                                                    pt_entry,
                                                    (layer + 1) as nat,
                                                    entry.get_Directory_addr(),
                                                );
                                                assert(inv_at(
                                                    mem,
                                                    pt_final@.entries[i as int].get_Some_0(),
                                                    (layer + 1) as nat,
                                                    entry.get_Directory_addr(),
                                                ));
                                            }
                                        }
                                    };
                                };
                                assert(directories_have_flags(mem, pt_final@, layer as nat, ptr));
                                assert(pt_final@.entries.len() == pt_with_empty@.entries.len());
                                assert(forall|i: nat|
                                    i != idx && i < pt_final@.entries.len()
                                        ==> pt_final@.entries[i as int]
                                        === pt_with_empty@.entries[i as int]);
                                assert(ghost_pt_used_regions_rtrancl(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                )) by {
                                    assert forall|i: nat, r: MemRegion|
                                        i < pt_final@.entries.len()
                                            && pt_final@.entries[i as int].is_Some()
                                            && #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(
                                        r) implies pt_final@.used_regions.contains(r) by {
                                        if i == idx {
                                            if dir_new_regions@.contains(r) {
                                                assert(pt_final@.used_regions.contains(r));
                                            } else {
                                                assert(pt_with_empty@.entries[i as int].get_Some_0().used_regions.contains(
                                                r));
                                                assert(pt_with_empty@.used_regions.contains(r));
                                                assert(pt_final@.used_regions.contains(r));
                                            }
                                        } else {
                                        }
                                    };
                                };
                                assert(ghost_pt_used_regions_pairwise_disjoint(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                )) by {
                                    assert forall|i: nat, j: nat, r: MemRegion|
                                        i != j && i < pt_final@.entries.len()
                                            && pt_final@.entries[i as int].is_Some()
                                            && #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(
                                        r) && j < pt_final@.entries.len()
                                            && pt_final@.entries[j as int].is_Some() implies !(
                                    #[trigger] pt_final@.entries[j as int].get_Some_0().used_regions.contains(
                                    r)) by {
                                        assert(ghost_pt_used_regions_pairwise_disjoint(
                                            mem_with_empty@,
                                            pt_with_empty@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        if j == idx {
                                            assert(pt_final@.entries[j as int].get_Some_0()
                                                === dir_pt_res@);
                                            assert(pt_final@.entries[i as int]
                                                === pt.entries[i as int]);
                                            if dir_new_regions@.contains(r) {
                                                assert(!new_dir_pt@.used_regions.contains(r));
                                                assert(!mem_with_empty@.regions().contains(r));
                                                assert(!dir_pt_res@.used_regions.contains(r));
                                            } else {
                                                if new_dir_pt@.used_regions.contains(r) {
                                                    assert(pt.used_regions.contains(r));
                                                    assert(mem_with_empty@.regions().contains(r));
                                                    assert(!dir_pt_res@.used_regions.contains(r));
                                                }
                                            }
                                        } else {
                                            if i == idx {
                                                assert(pt_final@.entries[i as int].get_Some_0()
                                                    === dir_pt_res@);
                                                assert(pt_final@.entries[j as int]
                                                    === pt.entries[j as int]);
                                                if dir_new_regions@.contains(r) {
                                                    assert(dir_pt_res@.used_regions.contains(r));
                                                    assert(!new_dir_pt@.used_regions.contains(r));
                                                    assert(!mem_with_empty@.regions().contains(r));
                                                    assert(!pt.entries[j as int].get_Some_0().used_regions.contains(
                                                    r));
                                                } else {
                                                    assert(new_dir_pt@.used_regions.contains(r));
                                                    assert(!pt.entries[j as int].get_Some_0().used_regions.contains(
                                                    r));
                                                }
                                            } else {
                                                assert(pt_final@.entries[i as int]
                                                    === pt.entries[i as int]);
                                                assert(pt_final@.entries[j as int]
                                                    === pt.entries[j as int]);
                                            }
                                        }
                                    };
                                };
                                assert(ghost_pt_matches_structure(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert(ghost_pt_region_notin_used_regions(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                ));
                                assert(entry_mb0_bits_are_zero(mem, pt_final@, layer as nat, ptr));
                                assert(hp_pat_is_zero(mem, pt_final@, layer as nat, ptr));
                            };
                            assert(Ok(interp_at(mem, pt_final@, layer as nat, ptr, base as nat))
                                === interp_at(
                                &*old(mem),
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                            ).map_frame(vaddr as nat, pte@)) by {
                                lemma_interp_at_aux_facts(
                                    mem_with_empty@,
                                    pt_with_empty@,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                    seq![],
                                );
                                assert(inv_at(mem, pt_final@, layer as nat, ptr));
                                assert(inv_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                lemma_interp_at_aux_facts(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                    seq![],
                                );
                                // The original/old interp is `interp@`
                                let final_interp = interp_at(
                                    mem,
                                    pt_final@,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                );
                                let prev_interp = interp_at(
                                    mem_with_empty@,
                                    pt_with_empty@,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                );
                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES && i
                                        != idx implies prev_interp.entries[i as int]
                                    === #[trigger] interp@.entries[i as int] by {
                                    lemma_interp_at_entry_different_memory(
                                        &*old(mem),
                                        pt,
                                        mem_with_empty@,
                                        pt_with_empty@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        i,
                                    );
                                };
                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES && i
                                        != idx implies final_interp.entries[i as int]
                                    === #[trigger] prev_interp.entries[i as int] by {
                                    if pt_final@.entries[i as int].is_Some() {
                                        let pt_entry = pt_final@.entries[i as int].get_Some_0();
                                        assert(ghost_pt_used_regions_pairwise_disjoint(
                                            mem,
                                            pt_final@,
                                            layer as nat,
                                            ptr,
                                        ));
                                        assert forall|r: MemRegion| #[trigger]
                                            pt_entry.used_regions.contains(
                                                r,
                                            ) implies !new_regions@.contains(r) by {
                                            assert(pt_entry.used_regions.contains(r));
                                            assert(mem_with_empty@.regions().contains(r));
                                            assert(old(mem).regions().contains(r));
                                            assert(!new_regions@.contains(r));
                                        };
                                        assert(forall|r: MemRegion| #[trigger]
                                            pt_entry.used_regions.contains(r)
                                                ==> !dir_pt_res@.used_regions.contains(r));
                                        assert(forall|r: MemRegion|
                                            pt_entry.used_regions.contains(r) ==> #[trigger] old(
                                                mem,
                                            ).region_view(r) === mem.region_view(r));
                                    }
                                    lemma_interp_at_entry_different_memory(
                                        mem_with_empty@,
                                        pt_with_empty@,
                                        mem,
                                        pt_final@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        i,
                                    );
                                };
                                assert(final_interp.entries[idx as int] === interp@.map_frame(
                                    vaddr as nat,
                                    pte@,
                                ).get_Ok_0().entries[idx as int]);
                                assert(final_interp.entries =~= interp@.map_frame(
                                    vaddr as nat,
                                    pte@,
                                ).get_Ok_0().entries);
                                assert(Ok(interp_at(mem, pt_final@, layer as nat, ptr, base as nat))
                                    === interp@.map_frame(vaddr as nat, pte@));
                            };
                        }
                        // posts
                        proof {
                            assert(pt_final@.region === pt.region);
                            assert(pt_final@.used_regions =~= pt.used_regions.union(new_regions@));
                            assert(mem.regions() =~= old(mem).regions().union(new_regions@));
                            assert forall|r: MemRegion|
                                !(#[trigger] pt.used_regions.contains(r)) && !new_regions@.contains(
                                    r,
                                ) implies mem.region_view(r) === old(mem).region_view(r) by {
                                assert(r !== new_dir_region@);
                                assert(!pt_with_empty@.used_regions.contains(r));
                                assert(!new_dir_pt@.used_regions.contains(r));
                                assert(!dir_new_regions@.contains(r));
                                assert(mem.region_view(r) === mem_with_empty@.region_view(r));
                            };
                            assert forall|r: MemRegion| new_regions@.contains(r) implies !(
                            #[trigger] old(mem).regions().contains(r)) by {
                                if r === new_dir_region@ {
                                    assert(!old(mem).regions().contains(r));
                                } else {
                                    assert(dir_new_regions@.contains(r));
                                    assert(!mem_with_empty@.regions().contains(r));
                                    assert(!old(mem).regions().contains(r));
                                }
                            };
                            assert(forall|r: MemRegion|
                                new_regions@.contains(r) ==> !(#[trigger] pt.used_regions.contains(
                                    r,
                                )));
                        }
                        Ok(Ghost((pt_final@, new_regions@)))
                    },
                    Err(e) => {
                        proof {
                            indexing::lemma_index_from_base_and_addr(
                                entry_base as nat,
                                vaddr as nat,
                                x86_arch_spec.entry_size((layer + 1) as nat),
                                X86_NUM_ENTRIES as nat,
                            );
                            assert(false);  // We always successfully insert into an empty directory
                        }
                        Err(e)
                    },
                }
            }
        }
    }

    pub proof fn lemma_zeroed_page_implies_empty_at(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
    )
        requires
            ptr % PAGE_SIZE == 0,
            well_formed(mem, pt, ptr),
            mem.inv(),
            mem.regions().contains(pt.region),
            pt.region.base == ptr,
            pt.region.size == PAGE_SIZE,
            mem.region_view(pt.region).len() == pt.entries.len(),
            pt.region.base == ptr,
            ptr == pt.region.base,
            pt.used_regions === set![pt.region],
            layer_in_range(layer),
            pt.entries.len() == X86_NUM_ENTRIES,
            forall|i: nat| i < X86_NUM_ENTRIES ==> mem.region_view(pt.region)[i as int] == 0u64,
            forall|i: nat| i < X86_NUM_ENTRIES ==> pt.entries[i as int].is_None(),
        ensures
            empty_at(mem, pt, layer, ptr),
            inv_at(mem, pt, layer, ptr),
    {
        assert forall|i: nat| #![auto] i < X86_NUM_ENTRIES implies entry_at_spec(
            mem,
            pt,
            layer,
            ptr,
            i,
        )@.is_Empty() && entry_at_spec(mem, pt, layer, ptr, i).all_mb0_bits_are_zero() by {
            entry_at_spec(mem, pt, layer, ptr, i).lemma_zero_entry_facts();
        };
        assert(forall|i: nat|
            #![auto]
            entry_at_spec(mem, pt, layer, ptr, i)@ == view_at(mem, pt, layer, ptr, i));
    }

    proof fn lemma_empty_at_interp_at_aux_equal_l1_empty_dir(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
        init: Seq<l1::NodeEntry>,
        idx: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            forall|i: nat| i < init.len() ==> init[i as int] === l1::NodeEntry::Empty(),
            init.len() <= X86_NUM_ENTRIES,
            idx < X86_NUM_ENTRIES,
            view_at(mem, pt, layer, ptr, idx).is_Directory(),
            empty_at(
                mem,
                pt.entries[idx as int].get_Some_0(),
                (layer + 1) as nat,
                view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
            ),
        ensures
            ({
                let res = interp_at_aux(
                    mem,
                    pt.entries[idx as int].get_Some_0(),
                    layer + 1,
                    view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
                    x86_arch_spec.entry_base(layer, base, idx),
                    init,
                );
                &&& res.len() === X86_NUM_ENTRIES as nat
                &&& forall|i: nat| i < res.len() ==> res[i as int] === l1::NodeEntry::Empty()
            }),
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat,
    {
        let e_ptr = view_at(mem, pt, layer, ptr, idx).get_Directory_addr();
        let e_base = x86_arch_spec.entry_base(layer, base, idx);
        let e_pt = pt.entries[idx as int].get_Some_0();
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            lemma_empty_at_interp_at_aux_equal_l1_empty_dir(
                mem,
                pt,
                layer,
                ptr,
                base,
                init.push(interp_at_entry(mem, e_pt, layer + 1, e_ptr, e_base, init.len())),
                idx,
            );
        }
    }

    proof fn lemma_empty_at_interp_at_equal_l1_empty_dir(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
        idx: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            idx < X86_NUM_ENTRIES,
            view_at(mem, pt, layer, ptr, idx).is_Directory(),
            empty_at(
                mem,
                pt.entries[idx as int].get_Some_0(),
                (layer + 1) as nat,
                view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
            ),
        ensures
            ({
                let res = interp_at(
                    mem,
                    pt.entries[idx as int].get_Some_0(),
                    layer + 1,
                    view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
                    x86_arch_spec.entry_base(layer, base, idx),
                );
                &&& res.entries.len() === X86_NUM_ENTRIES as nat
                &&& forall|i: nat|
                    i < res.entries.len() ==> res.entries[i as int] === l1::NodeEntry::Empty()
            }),
    {
        lemma_empty_at_interp_at_aux_equal_l1_empty_dir(mem, pt, layer, ptr, base, seq![], idx);
    }

    proof fn lemma_not_empty_at_implies_interp_at_aux_not_empty(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
        init: Seq<l1::NodeEntry>,
        nonempty_idx: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            nonempty_idx < X86_NUM_ENTRIES,
            !view_at(mem, pt, layer, ptr, nonempty_idx).is_Empty(),
            nonempty_idx < init.len() ==> !init[nonempty_idx as int].is_Empty(),
        ensures
            !interp_at_aux(mem, pt, layer, ptr, base, init)[nonempty_idx as int].is_Empty(),
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat,
    {
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            let new_init = init.push(interp_at_entry(mem, pt, layer, ptr, base, init.len()));
            lemma_not_empty_at_implies_interp_at_aux_not_empty(
                mem,
                pt,
                layer,
                ptr,
                base,
                new_init,
                nonempty_idx,
            );
        }
    }

    proof fn lemma_empty_at_implies_interp_at_empty(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            empty_at(mem, pt, layer, ptr),
        ensures
            interp_at(mem, pt, layer, ptr, base).empty(),
    {
        lemma_interp_at_aux_facts(mem, pt, layer, ptr, base, seq![]);
    }

    proof fn lemma_not_empty_at_implies_interp_at_not_empty(
        mem: &mem::PageTableMemory,
        pt: PTDir,
        layer: nat,
        ptr: usize,
        base: nat,
    )
        requires
            inv_at(mem, pt, layer, ptr),
            !empty_at(mem, pt, layer, ptr),
        ensures
            !interp_at(mem, pt, layer, ptr, base).empty(),
    {
        let i = choose|i: nat| i < X86_NUM_ENTRIES && !view_at(mem, pt, layer, ptr, i).is_Empty();
        lemma_not_empty_at_implies_interp_at_aux_not_empty(mem, pt, layer, ptr, base, seq![], i);
    }

    pub fn map_frame(
        mem: &mut mem::PageTableMemory,
        pt: &mut Ghost<PTDir>,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (res: MapResult)
        requires
            inv(&*old(mem), old(pt)@),
            interp(&*old(mem), old(pt)@).inv(),
            old(mem).inv(),
            old(mem).alloc_available_pages() >= 3,
            accepted_mapping(vaddr as nat, pte@),
            interp(&*old(mem), old(pt)@).accepted_mapping(vaddr as nat, pte@),
            vaddr < MAX_BASE,
        ensures
            inv(mem, pt@),
            interp(mem, pt@).inv(),
            // Refinement of l0
            match res {
                MapResult::Ok => {
                    Ok(interp(mem, pt@).interp()) === interp(
                        &*old(mem),
                        old(pt)@,
                    ).interp().map_frame(vaddr as nat, pte@)
                },
                MapResult::ErrOverlap => Err(interp(mem, pt@).interp()) === interp(
                    &*old(mem),
                    old(pt)@,
                ).interp().map_frame(vaddr as nat, pte@),
            },
    {
        proof {
            interp(mem, pt@).lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
        }
        match map_frame_aux(mem, *pt, 0, mem.cr3().base, 0, vaddr, pte) {
            Ok(res) => {
                proof {
                    interp(&*old(mem), pt@).lemma_map_frame_preserves_inv(vaddr as nat, pte@);
                }
                *pt = Ghost(res@.0);
                MapResult::Ok
            },
            Err(e) => MapResult::ErrOverlap,
        }
    }

    fn is_directory_empty(
        mem: &mem::PageTableMemory,
        Ghost(pt): Ghost<PTDir>,
        layer: usize,
        ptr: usize,
    ) -> (res: bool)
        requires
            inv_at(mem, pt, layer as nat, ptr),
        ensures
            res === empty_at(mem, pt, layer as nat, ptr),
    {
        assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
        let mut idx = 0;
        let num_entries = x86_arch_exec().num_entries(layer);
        while idx < num_entries
            invariant
                num_entries == X86_NUM_ENTRIES,
                inv_at(mem, pt, layer as nat, ptr),
                forall|i: nat| i < idx ==> view_at(mem, pt, layer as nat, ptr, i).is_Empty(),
        {
            let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
            if entry.is_mapping() {
                assert(!view_at(mem, pt, layer as nat, ptr, idx as nat).is_Empty());
                assert(!empty_at(mem, pt, layer as nat, ptr));
                return false;
            }
            idx = idx + 1;
        }
        true
    }

    fn unmap_aux(
        mem: &mut mem::PageTableMemory,
        Ghost(pt): Ghost<PTDir>,
        layer: usize,
        ptr: usize,
        base: usize,
        vaddr: usize,
    ) -> (res: Result<Ghost<(PTDir, Set<MemRegion>)>, ()>)
        requires
            inv_at(&*old(mem), pt, layer as nat, ptr),
            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
            old(mem).inv(),
            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).accepted_unmap(vaddr as nat),
            base <= vaddr < MAX_BASE,
        ensures
            match res {
                Ok(resv) => {
                    let (pt_res, removed_regions) = resv@;
                    // We return the regions that we removed
                    &&& old(mem).regions() == mem.regions().union(removed_regions)
                    &&& pt.used_regions == pt_res.used_regions.union(
                        removed_regions,
                    )
                    // and only those we removed

                    &&& (forall|r: MemRegion|
                        removed_regions.contains(r) ==> !(#[trigger] mem.regions().contains(r)))
                    &&& (forall|r: MemRegion|
                        removed_regions.contains(r) ==> !(#[trigger] pt_res.used_regions.contains(
                            r,
                        )))
                    // Invariant preserved

                    &&& inv_at(
                        mem,
                        pt_res,
                        layer as nat,
                        ptr,
                    )
                    // We only touch regions in pt.used_regions

                    &&& (forall|r: MemRegion|
                        !(#[trigger] pt_res.used_regions.contains(r)) && !(
                        #[trigger] removed_regions.contains(r)) ==> mem.region_view(r) === old(
                            mem,
                        ).region_view(r))
                    &&& pt_res.region === pt.region
                },
                Err(e) => {
                    // If error, unchanged
                    &&& mem === old(mem)
                },
            },
            // Refinement of l1
            match res {
                Ok(resv) => {
                    let (pt_res, removed_regions) = resv@;
                    Ok(interp_at(mem, pt_res, layer as nat, ptr, base as nat)) === interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).unmap(vaddr as nat)
                },
                Err(e) => Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                    &*old(mem),
                    pt,
                    layer as nat,
                    ptr,
                    base as nat,
                ).unmap(vaddr as nat),
            },
            mem.cr3_spec() == old(
                mem,
            ).cr3_spec(),
    // decreases X86_NUM_LAYERS - layer

    {
        proof {
            lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat);
        }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof {
            indexing::lemma_index_from_base_and_addr(
                base as nat,
                vaddr as nat,
                x86_arch_spec.entry_size(layer as nat),
                X86_NUM_ENTRIES as nat,
            );
        }
        let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
        let interp: Ghost<l1::Directory> = Ghost(
            interp_at(mem, pt, layer as nat, ptr, base as nat),
        );
        proof {
            interp@.lemma_unmap_structure_assertions(vaddr as nat, idx as nat);
            interp@.lemma_unmap_refines_unmap(vaddr as nat);
        }
        let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(
                base as nat,
                idx as nat,
                x86_arch_spec.entry_size(layer as nat),
            );
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                let dir_addr = entry.address() as usize;
                assert(pt.entries[idx as int].is_Some());
                let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
                assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
                assert(forall|r: MemRegion|
                    #![auto]
                    pt.entries[idx as int].get_Some_0().used_regions.contains(r)
                        ==> pt.used_regions.contains(r));
                match unmap_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                        let removed_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);
                        assert(inv_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr));
                        assert(Ok(
                            interp_at(
                                mem,
                                dir_pt_res@,
                                (layer + 1) as nat,
                                dir_addr,
                                entry_base as nat,
                            ),
                        ) === interp_at(
                            &*old(mem),
                            dir_pt@,
                            (layer + 1) as nat,
                            dir_addr,
                            entry_base as nat,
                        ).unmap(vaddr as nat));
                        assert(idx < pt.entries.len());
                        assert(!pt.entries[idx as int].get_Some_0().used_regions.contains(
                            pt.region,
                        ));
                        assert(!removed_regions@.contains(pt.region));
                        assert(!dir_pt_res@.used_regions.contains(pt.region));
                        assert(old(mem).regions() === mem.regions().union(removed_regions@));
                        if is_directory_empty(mem, dir_pt_res, layer + 1, dir_addr) {
                            let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);
                            let pt_with_empty: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt.region,
                                    entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt.used_regions,
                                },
                            );
                            mem.write(ptr, idx, Ghost(pt.region), 0u64);
                            mem.dealloc_page(MemRegionExec { base: dir_addr, size: PAGE_SIZE });
                            let removed_regions: Ghost<Set<MemRegion>> = Ghost(
                                removed_regions@.insert(dir_pt_res@.region),
                            );
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt.region,
                                    entries: pt.entries.update(idx as int, None),
                                    used_regions: pt.used_regions.difference(removed_regions@),
                                },
                            );
                            let res: Ghost<(PTDir, Set<MemRegion>)> = Ghost(
                                (pt_res@, removed_regions@),
                            );
                            proof {
                                assert(pt_res@.region === pt.region);
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int]
                                        == pt.entries[i as int]);
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> view_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    ) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    ) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                                assert(forall|i: nat, r: MemRegion|
                                    i < X86_NUM_ENTRIES && i != idx
                                        && pt_res@.entries[i as int].is_Some()
                                        && pt_res@.entries[i as int].get_Some_0().used_regions.contains(
                                    r)
                                        ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(
                                    r));
                                entry_at_spec(
                                    mem,
                                    pt_res@,
                                    layer as nat,
                                    ptr,
                                    idx as nat,
                                ).lemma_zero_entry_facts();
                                assert(inv_at(mem, pt_res@, layer as nat, ptr)) by {
                                    assert(directories_obey_invariant_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                    )) by {
                                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                            let entry = #[trigger] view_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                i,
                                            );
                                            entry.is_Directory() ==> {
                                                &&& inv_at(
                                                    mem,
                                                    pt_res@.entries[i as int].get_Some_0(),
                                                    layer as nat + 1,
                                                    entry.get_Directory_addr(),
                                                )
                                            }
                                        } by {
                                            let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                            if i == idx {
                                            } else {
                                                if entry.is_Directory() {
                                                    lemma_inv_at_different_memory(
                                                        &*old(mem),
                                                        mem,
                                                        pt_res@.entries[i as int].get_Some_0(),
                                                        (layer + 1) as nat,
                                                        entry.get_Directory_addr(),
                                                    );
                                                }
                                            }
                                        };
                                    };
                                };
                                // postconditions
                                assert((forall|r: MemRegion|
                                    removed_regions@.contains(r) ==> !(
                                    #[trigger] mem.regions().contains(r))));
                                assert(old(mem).regions() =~= mem.regions().union(
                                    removed_regions@,
                                ));
                                assert(pt.used_regions =~= pt_res@.used_regions.union(
                                    removed_regions@,
                                ));
                                assert((forall|r: MemRegion|
                                    removed_regions@.contains(r) ==> !(
                                    #[trigger] pt_res@.used_regions.contains(r))));
                                assert(forall|r: MemRegion|
                                    !(#[trigger] pt_res@.used_regions.contains(r)) && !(
                                    #[trigger] removed_regions@.contains(r)) ==> mem.region_view(r)
                                        === old(mem).region_view(r));
                                assert(mem.cr3_spec() == old(mem).cr3_spec());
                                // Refinement
                                assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat))
                                    === interp_at(
                                    &*old(mem),
                                    pt,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                ).unmap(vaddr as nat)) by {
                                    lemma_interp_at_aux_facts(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        seq![],
                                    );
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES implies #[trigger] interp_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries[i as int] == interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).unmap(vaddr as nat).get_Ok_0().entries[i as int] by {
                                        if i == idx {
                                            lemma_empty_at_implies_interp_at_empty(
                                                mem_with_empty@,
                                                dir_pt_res@,
                                                (layer + 1) as nat,
                                                dir_addr,
                                                entry_base as nat,
                                            );
                                            assert(interp_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[idx as int] == interp_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                        } else {
                                            lemma_interp_at_entry_different_memory(
                                                &*old(mem),
                                                pt,
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                                i,
                                            );
                                            assert(interp_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[i as int] == interp_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                        }
                                    }
                                    assert_seqs_equal!(
                                            interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries,
                                            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                                };
                            }
                            Ok(res)
                        } else {
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt.region,
                                    entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt.used_regions.difference(removed_regions@),
                                },
                            );
                            let res: Ghost<(PTDir, Set<MemRegion>)> = Ghost(
                                (pt_res@, removed_regions@),
                            );
                            proof {
                                assert(pt_res@.region === pt.region);
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int]
                                        == pt.entries[i as int]);
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> view_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    ) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                                assert(forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        i,
                                    ) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                                assert(forall|i: nat, r: MemRegion|
                                    i < X86_NUM_ENTRIES && i != idx
                                        && pt_res@.entries[i as int].is_Some()
                                        && pt_res@.entries[i as int].get_Some_0().used_regions.contains(
                                    r)
                                        ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(
                                    r));
                                assert(inv_at(mem, pt_res@, layer as nat, ptr)) by {
                                    assert(directories_obey_invariant_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                    )) by {
                                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                            let entry = #[trigger] view_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                i,
                                            );
                                            entry.is_Directory() ==> {
                                                &&& inv_at(
                                                    mem,
                                                    pt_res@.entries[i as int].get_Some_0(),
                                                    layer as nat + 1,
                                                    entry.get_Directory_addr(),
                                                )
                                            }
                                        } by {
                                            let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                            if i == idx {
                                            } else {
                                                if entry.is_Directory() {
                                                    lemma_inv_at_different_memory(
                                                        &*old(mem),
                                                        mem,
                                                        pt_res@.entries[i as int].get_Some_0(),
                                                        (layer + 1) as nat,
                                                        entry.get_Directory_addr(),
                                                    );
                                                }
                                            }
                                        };
                                    };
                                };
                                // postconditions
                                assert(old(mem).regions() =~= mem.regions().union(
                                    removed_regions@,
                                ));
                                assert(pt.used_regions =~= pt_res@.used_regions.union(
                                    removed_regions@,
                                ));
                                assert(forall|r: MemRegion|
                                    !(#[trigger] pt_res@.used_regions.contains(r)) && !(
                                    #[trigger] removed_regions@.contains(r)) ==> mem.region_view(r)
                                        === old(mem).region_view(r));
                                assert(pt_res@.region === pt.region);
                                assert(mem.cr3_spec() == old(mem).cr3_spec());
                                // Refinement
                                assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat))
                                    === interp_at(
                                    &*old(mem),
                                    pt,
                                    layer as nat,
                                    ptr,
                                    base as nat,
                                ).unmap(vaddr as nat)) by {
                                    lemma_interp_at_aux_facts(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        seq![],
                                    );
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES implies #[trigger] interp_at(
                                        mem,
                                        pt_res@,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries[i as int] == interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).unmap(vaddr as nat).get_Ok_0().entries[i as int] by {
                                        if i == idx {
                                            assert(interp_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[idx as int] == l1::NodeEntry::Directory(
                                                interp_at(
                                                    mem,
                                                    dir_pt_res@,
                                                    (layer + 1) as nat,
                                                    dir_addr,
                                                    entry_base as nat,
                                                ),
                                            ));
                                            assert(interp_at(
                                                &*old(mem),
                                                dir_pt@,
                                                (layer + 1) as nat,
                                                dir_addr,
                                                entry_base as nat,
                                            ).unmap(vaddr as nat).is_Ok());
                                            assert(interp_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[idx as int] == interp_at_entry(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                                idx as nat,
                                            ));
                                            lemma_not_empty_at_implies_interp_at_not_empty(
                                                mem,
                                                dir_pt_res@,
                                                (layer + 1) as nat,
                                                dir_addr,
                                                entry_base as nat,
                                            );
                                            assert(interp_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[idx as int] == interp_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                        } else {
                                            lemma_interp_at_entry_different_memory(
                                                &*old(mem),
                                                pt,
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                                i,
                                            );
                                            assert(interp_at(
                                                mem,
                                                pt_res@,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).entries[i as int] == interp_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                                base as nat,
                                            ).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                        }
                                    }
                                    assert_seqs_equal!(
                                            interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries,
                                            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                                };
                            }
                            Ok(res)
                        }
                    },
                    Err(e) => {
                        assert(mem === old(mem));
                        assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat))
                            === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(
                            vaddr as nat,
                        ));
                        Err(e)
                    },
                }
            } else {
                if aligned_exec(vaddr, x86_arch_exec().entry_size(layer)) {
                    mem.write(ptr, idx, Ghost(pt.region), 0u64);
                    let removed_regions: Ghost<Set<MemRegion>> = Ghost(Set::empty());
                    let res: Ghost<(PTDir, Set<MemRegion>)> = Ghost((pt, removed_regions@));
                    proof {
                        assert(mem.region_view(pt.region) === old(mem).region_view(
                            pt.region,
                        ).update(idx as int, 0));
                        assert(mem.spec_read(idx as nat, pt.region) == 0);
                        let new_entry = entry_at_spec(mem, pt, layer as nat, ptr, idx as nat);
                        new_entry.lemma_zero_entry_facts();
                        assert(forall|i: nat|
                            i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(
                                mem,
                                pt,
                                layer as nat,
                                ptr,
                                i,
                            ) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                        assert(forall|i: nat|
                            i < X86_NUM_ENTRIES && i != idx ==> view_at(
                                mem,
                                pt,
                                layer as nat,
                                ptr,
                                i,
                            ) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                        assert(inv_at(mem, pt, layer as nat, ptr)) by {
                            assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] view_at(mem, pt, layer as nat, ptr, i);
                                    entry.is_Directory() ==> {
                                        &&& inv_at(
                                            mem,
                                            pt.entries[i as int].get_Some_0(),
                                            layer as nat + 1,
                                            entry.get_Directory_addr(),
                                        )
                                    }
                                } by {
                                    let entry = view_at(mem, pt, layer as nat, ptr, i);
                                    if i == idx {
                                    } else {
                                        if entry.is_Directory() {
                                            assert(directories_obey_invariant_at(
                                                &*old(mem),
                                                pt,
                                                layer as nat,
                                                ptr,
                                            ));
                                            lemma_inv_at_different_memory(
                                                &*old(mem),
                                                mem,
                                                pt.entries[i as int].get_Some_0(),
                                                (layer + 1) as nat,
                                                entry.get_Directory_addr(),
                                            );
                                            assert(inv_at(
                                                mem,
                                                pt.entries[i as int].get_Some_0(),
                                                layer as nat + 1,
                                                entry.get_Directory_addr(),
                                            ));
                                        }
                                    }
                                };
                            };
                        };
                        // postconditions
                        assert_sets_equal!(old(mem).regions(), mem.regions().union(removed_regions@));
                        assert_sets_equal!(pt.used_regions, pt.used_regions.union(removed_regions@));
                        // Refinement
                        assert(Ok(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                            &*old(mem),
                            pt,
                            layer as nat,
                            ptr,
                            base as nat,
                        ).unmap(vaddr as nat)) by {
                            lemma_interp_at_aux_facts(
                                mem,
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                                seq![],
                            );
                            assert(interp_at(mem, pt, layer as nat, ptr, base as nat).entries.len()
                                == X86_NUM_ENTRIES);
                            assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(
                                vaddr as nat,
                            ).get_Ok_0().entries.len() == X86_NUM_ENTRIES);
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies #[trigger] interp_at(
                                mem,
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                            ).entries[i as int] == interp_at(
                                &*old(mem),
                                pt,
                                layer as nat,
                                ptr,
                                base as nat,
                            ).unmap(vaddr as nat).get_Ok_0().entries[i as int] by {
                                if i == idx {
                                } else {
                                    lemma_interp_at_entry_different_memory(
                                        &*old(mem),
                                        pt,
                                        mem,
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                        i,
                                    );
                                    assert(interp_at(
                                        mem,
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).entries[i as int] == interp_at(
                                        &*old(mem),
                                        pt,
                                        layer as nat,
                                        ptr,
                                        base as nat,
                                    ).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                }
                            }
                            assert_seqs_equal!(
                                    interp_at(mem, pt, layer as nat, ptr, base as nat).entries,
                                    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                        };
                    }
                    Ok(res)
                } else {
                    assert(mem === old(mem));
                    assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                        &*old(mem),
                        pt,
                        layer as nat,
                        ptr,
                        base as nat,
                    ).unmap(vaddr as nat));
                    Err(())
                }
            }
        } else {
            assert(mem === old(mem));
            assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(
                &*old(mem),
                pt,
                layer as nat,
                ptr,
                base as nat,
            ).unmap(vaddr as nat));
            Err(())
        }
    }

    pub fn unmap(mem: &mut mem::PageTableMemory, pt: &mut Ghost<PTDir>, vaddr: usize) -> (res:
        UnmapResult)
        requires
            inv(&*old(mem), old(pt)@),
            interp(&*old(mem), old(pt)@).inv(),
            old(mem).inv(),
            interp(&*old(mem), old(pt)@).accepted_unmap(vaddr as nat),
            vaddr < MAX_BASE,
        ensures
            inv(mem, pt@),
            interp(mem, pt@).inv(),
            // Refinement of l0
            match res {
                UnmapResult::Ok => {
                    Ok(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().unmap(
                        vaddr as nat,
                    )
                },
                UnmapResult::ErrNoSuchMapping => Err(interp(mem, pt@).interp()) === interp(
                    &*old(mem),
                    old(pt)@,
                ).interp().unmap(vaddr as nat),
            },
    {
        proof {
            interp(mem, pt@).lemma_unmap_refines_unmap(vaddr as nat);
        }
        match unmap_aux(mem, *pt, 0, mem.cr3().base, 0, vaddr) {
            Ok(res) => {
                proof {
                    interp(&*old(mem), pt@).lemma_unmap_preserves_inv(vaddr as nat);
                }
                *pt = Ghost(res@.0);
                UnmapResult::Ok
            },
            Err(e) => UnmapResult::ErrNoSuchMapping,
        }
    }

}

pub proof fn lemma_set_union_empty_equals_set<T>(s: Set<T>)
    ensures
        s.union(set![]) === s,
{
    assert_sets_equal!(s.union(set![]), s);
}

} // verus!
}

    pub mod l2_refinement {
        #![allow(unused_imports)]
        use crate::spec_t::mem;
        use builtin::*;
        use builtin_macros::*;
        use map::*;
        use modes::*;
        use seq::*;
        use seq_lib::*;
        use set::*;
        use set_lib::*;
        use vstd::prelude::*;
        use vstd::*;

        use crate::definitions_t::{
            aligned, axiom_x86_arch_exec_spec, bit, bitmask_inc, candidate_mapping_in_bounds,
            candidate_mapping_overlaps_existing_vmem, new_seq, x86_arch_exec, x86_arch_exec_spec,
            x86_arch_spec, Flags, MemRegionExec, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
            L3_ENTRY_SIZE, MAX_BASE,
        };
        use crate::definitions_t::{
            MapResult, MemRegion, PageTableEntry, PageTableEntryExec, ResolveResultExec,
            UnmapResult,
        };
        use crate::definitions_u::{lemma_new_seq, x86_arch_inv};
        use crate::impl_u::l0;
        use crate::impl_u::l1;
        use crate::impl_u::l2_impl::PTDir;
        use crate::impl_u::l2_impl::PT;
        use crate::impl_u::spec_pt;
        use crate::spec_t::hardware::{
            interp_pt_mem, l0_bits, l1_bits, l2_bits, l3_bits, nat_to_u64, read_entry,
            valid_pt_walk, GhostPageDirectoryEntry,
        };
        use crate::spec_t::impl_spec;

        verus! {

pub proof fn lemma_page_table_walk_interp()
    ensures
        forall|mem: mem::PageTableMemory, pt: PTDir|
            #![auto]
            PT::inv(&mem, pt) && PT::interp(&mem, pt).inv() ==> PT::interp(&mem, pt).interp().map
                === interp_pt_mem(mem),
{
    assert forall|mem: mem::PageTableMemory, pt: PTDir|
        #![auto]
        PT::inv(&mem, pt) && PT::interp(&mem, pt).inv() implies PT::interp(&mem, pt).interp().map
        === interp_pt_mem(mem) by {
        lemma_page_table_walk_interp_aux(mem, pt);
    }
}

pub proof fn lemma_page_table_walk_interp_aux(mem: mem::PageTableMemory, pt: PTDir)
    requires
        PT::inv(&mem, pt) && PT::interp(&mem, pt).inv(),
    ensures
        PT::interp(&mem, pt).interp().map === interp_pt_mem(mem),
{
    let m1 = interp_pt_mem(mem);
    let m2 = PT::interp(&mem, pt).interp().map;
    PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
    assert(PT::interp(&mem, pt).interp().inv());
    assert forall|addr: nat, pte: PageTableEntry|
        m1.contains_pair(addr, pte) implies #[trigger] m2.contains_pair(addr, pte) by {
        let addr: u64 = addr as u64;
        assert(addr < MAX_BASE);
        let pte = choose|pte: PageTableEntry| valid_pt_walk(mem, addr, pte);
        assert(valid_pt_walk(mem, addr as u64, pte));
        PT::lemma_interp_at_facts(&mem, pt, 0, mem.cr3_spec().base, 0);
        let l0_idx_u64: u64 = l0_bits!(addr);
        let l0_idx: nat = l0_idx_u64 as nat;
        let l1_idx_u64: u64 = l1_bits!(addr);
        let l1_idx: nat = l1_idx_u64 as nat;
        let l2_idx_u64: u64 = l2_bits!(addr);
        let l2_idx: nat = l2_idx_u64 as nat;
        let l3_idx_u64: u64 = l3_bits!(addr);
        let l3_idx: nat = l3_idx_u64 as nat;
        assert(forall|a: u64| (a & bitmask_inc!(0u64,8u64) == a) ==> a < 512) by (bit_vector);
        assert(l0_idx < 512 && l1_idx < 512 && l2_idx < 512 && l3_idx < 512) by {
            assert(((addr & bitmask_inc!(12u64,20u64)) >> 12u64) & bitmask_inc!(0u64,8u64) == ((addr
                & bitmask_inc!(12u64,20u64)) >> 12u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(21u64,29u64)) >> 21u64) & bitmask_inc!(0u64,8u64) == ((addr
                & bitmask_inc!(21u64,29u64)) >> 21u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(30u64,38u64)) >> 30u64) & bitmask_inc!(0u64,8u64) == ((addr
                & bitmask_inc!(30u64,38u64)) >> 30u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(39u64,47u64)) >> 39u64) & bitmask_inc!(0u64,8u64) == ((addr
                & bitmask_inc!(39u64,47u64)) >> 39u64)) by (bit_vector);
        };
        assert(bitmask_inc!(39u64,47u64) == 0xFF80_0000_0000) by (compute);
        assert(bitmask_inc!(30u64,38u64) == 0x007F_C000_0000) by (compute);
        assert(bitmask_inc!(21u64,29u64) == 0x0000_3FE0_0000) by (compute);
        assert(bitmask_inc!(12u64,20u64) == 0x0000_001F_F000) by (compute);
        let interp_l0_dir = PT::interp(&mem, pt);
        let interp_l0_entry = PT::interp_at_entry(&mem, pt, 0, mem.cr3_spec().base, 0, l0_idx);
        interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
            l0_idx,
        );
        match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
            GhostPageDirectoryEntry::Directory {
                addr: l0_dir_addr,
                flag_RW: l0_RW,
                flag_US: l0_US,
                flag_XD: l0_XD,
                ..
            } => {
                assert(interp_l0_entry.is_Directory());
                let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                let l0_dir_ghost_pt = pt.entries[l0_idx as int].get_Some_0();
                assert(PT::directories_obey_invariant_at(&mem, pt, 0, mem.cr3_spec().base));
                assert(PT::inv_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                assert(interp_l0_dir.directories_obey_invariant());
                assert(interp_l0_dir.entries[l0_idx as int].get_Directory_0().inv());
                PT::lemma_interp_at_facts(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr);
                let interp_l1_dir = PT::interp_at(
                    &mem,
                    l0_dir_ghost_pt,
                    1,
                    l0_dir_addr,
                    l1_base_vaddr,
                );
                let interp_l1_entry = PT::interp_at_entry(
                    &mem,
                    l0_dir_ghost_pt,
                    1,
                    l0_dir_addr,
                    l1_base_vaddr,
                    l1_idx,
                );
                interp_l1_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                l1_idx);
                match read_entry(mem, l0_dir_addr as nat, 1, l1_idx) {
                    GhostPageDirectoryEntry::Page {
                        addr: page_addr,
                        flag_RW: l1_RW,
                        flag_US: l1_US,
                        flag_XD: l1_XD,
                        ..
                    } => {
                        assert(aligned(addr as nat, L1_ENTRY_SIZE as nat));
                        assert(pte == PageTableEntry {
                            frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                            flags: Flags {
                                is_writable: l0_RW && l1_RW,
                                is_supervisor: !l0_US || !l1_US,
                                disable_execute: l0_XD || l1_XD,
                            },
                        });
                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64)))
                            by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                addr % mul(512, mul(512, 4096)) == 0,
                        ;
                        assert(add(
                            mul(l0_idx_u64, mul(512u64, mul(512, mul(512, 4096)))),
                            mul(l1_idx_u64, mul(512u64, mul(512, 4096))),
                        ) == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64) by (bit_vector)
                            requires
                                l0_idx_u64 < 512 && l1_idx_u64 < 512,
                        ;
                        // Previous assert proves: l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64
                        assert(interp_l1_dir.interp_of_entry(l1_idx).map.contains_pair(
                            addr as nat,
                            pte,
                        ));
                        assert(interp_l1_dir.interp().map.contains_pair(addr as nat, pte));
                        assert(interp_l0_dir.interp().map.contains_pair(addr as nat, pte));
                        assert(m2.contains_pair(addr as nat, pte));
                    },
                    GhostPageDirectoryEntry::Directory {
                        addr: l1_dir_addr,
                        flag_RW: l1_RW,
                        flag_US: l1_US,
                        flag_XD: l1_XD,
                        ..
                    } => {
                        assert(interp_l1_entry.is_Directory());
                        let l2_base_vaddr = x86_arch_spec.entry_base(1, l1_base_vaddr, l1_idx);
                        let l1_dir_ghost_pt = l0_dir_ghost_pt.entries[l1_idx as int].get_Some_0();
                        assert(PT::directories_obey_invariant_at(
                            &mem,
                            l0_dir_ghost_pt,
                            1,
                            l0_dir_addr,
                        ));
                        assert(PT::inv_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                        PT::lemma_interp_at_facts(
                            &mem,
                            l1_dir_ghost_pt,
                            2,
                            l1_dir_addr,
                            l2_base_vaddr,
                        );
                        let interp_l2_dir = PT::interp_at(
                            &mem,
                            l1_dir_ghost_pt,
                            2,
                            l1_dir_addr,
                            l2_base_vaddr,
                        );
                        let interp_l2_entry = PT::interp_at_entry(
                            &mem,
                            l1_dir_ghost_pt,
                            2,
                            l1_dir_addr,
                            l2_base_vaddr,
                            l2_idx,
                        );
                        interp_l2_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                        l2_idx);
                        match read_entry(mem, l1_dir_addr as nat, 2, l2_idx) {
                            GhostPageDirectoryEntry::Page {
                                addr: page_addr,
                                flag_RW: l2_RW,
                                flag_US: l2_US,
                                flag_XD: l2_XD,
                                ..
                            } => {
                                assert(aligned(addr as nat, L2_ENTRY_SIZE as nat));
                                assert(pte == PageTableEntry {
                                    frame: MemRegion {
                                        base: page_addr as nat,
                                        size: L2_ENTRY_SIZE as nat,
                                    },
                                    flags: Flags {
                                        is_writable: l0_RW && l1_RW && l2_RW,
                                        is_supervisor: !l0_US || !l1_US || !l2_US,
                                        disable_execute: l0_XD || l1_XD || l2_XD,
                                    },
                                });
                                assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (
                                l2_idx_u64 << 21u64))) by (bit_vector)
                                    requires
                                        l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                        addr % mul(512, 4096) == 0,
                                ;
                                assert(add(
                                    add(
                                        mul(l0_idx_u64, mul(512u64, mul(512, mul(512, 4096)))),
                                        mul(l1_idx_u64, mul(512u64, mul(512, 4096))),
                                    ),
                                    mul(l2_idx_u64, mul(512, 4096)),
                                ) == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64 | l2_idx_u64
                                    << 21u64) by (bit_vector)
                                    requires
                                        l0_idx_u64 < 512 && l1_idx_u64 < 512 && l2_idx_u64 < 512,
                                ;
                                // Previous assert proves:
                                // l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE + l2_idx * L2_ENTRY_SIZE
                                // == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64 | (l2_idx as u64) << 21u64
                                assert(interp_l2_dir.interp_of_entry(l2_idx).map.contains_pair(
                                    addr as nat,
                                    pte,
                                ));
                                assert(interp_l2_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(interp_l1_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(interp_l0_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(m2.contains_pair(addr as nat, pte));
                            },
                            GhostPageDirectoryEntry::Directory {
                                addr: l2_dir_addr,
                                flag_RW: l2_RW,
                                flag_US: l2_US,
                                flag_XD: l2_XD,
                                ..
                            } => {
                                assert(interp_l2_entry.is_Directory());
                                let l3_base_vaddr = x86_arch_spec.entry_base(
                                    2,
                                    l2_base_vaddr,
                                    l2_idx,
                                );
                                let l2_dir_ghost_pt =
                                    l1_dir_ghost_pt.entries[l2_idx as int].get_Some_0();
                                assert(PT::directories_obey_invariant_at(
                                    &mem,
                                    l1_dir_ghost_pt,
                                    2,
                                    l1_dir_addr,
                                ));
                                assert(PT::inv_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr));
                                PT::lemma_interp_at_facts(
                                    &mem,
                                    l2_dir_ghost_pt,
                                    3,
                                    l2_dir_addr,
                                    l3_base_vaddr,
                                );
                                let interp_l3_dir = PT::interp_at(
                                    &mem,
                                    l2_dir_ghost_pt,
                                    3,
                                    l2_dir_addr,
                                    l3_base_vaddr,
                                );
                                let interp_l3_entry = PT::interp_at_entry(
                                    &mem,
                                    l2_dir_ghost_pt,
                                    3,
                                    l2_dir_addr,
                                    l3_base_vaddr,
                                    l3_idx,
                                );
                                interp_l3_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                                l3_idx);
                                match read_entry(mem, l2_dir_addr as nat, 3, l3_idx) {
                                    GhostPageDirectoryEntry::Page {
                                        addr: page_addr,
                                        flag_RW: l3_RW,
                                        flag_US: l3_US,
                                        flag_XD: l3_XD,
                                        ..
                                    } => {
                                        assert(aligned(addr as nat, L3_ENTRY_SIZE as nat));
                                        assert(pte == PageTableEntry {
                                            frame: MemRegion {
                                                base: page_addr as nat,
                                                size: L3_ENTRY_SIZE as nat,
                                            },
                                            flags: Flags {
                                                is_writable: l0_RW && l1_RW && l2_RW && l3_RW,
                                                is_supervisor: !l0_US || !l1_US || !l2_US || !l3_US,
                                                disable_execute: l0_XD || l1_XD || l2_XD || l3_XD,
                                            },
                                        });
                                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64
                                            << 30u64) | (l2_idx_u64 << 21u64) | (l3_idx_u64
                                            << 12u64))) by (bit_vector)
                                            requires
                                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                addr < mul(
                                                    512u64,
                                                    mul(512, mul(512, mul(512, 4096))),
                                                ),
                                                addr % 4096 == 0,
                                        ;
                                        assert(add(
                                            add(
                                                add(
                                                    mul(
                                                        l0_idx_u64,
                                                        mul(512u64, mul(512, mul(512, 4096))),
                                                    ),
                                                    mul(l1_idx_u64, mul(512u64, mul(512, 4096))),
                                                ),
                                                mul(l2_idx_u64, mul(512, 4096)),
                                            ),
                                            mul(l3_idx_u64, 4096),
                                        ) == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64 | l2_idx_u64
                                            << 21u64 | l3_idx_u64 << 12u64) by (bit_vector)
                                            requires
                                                l0_idx_u64 < 512 && l1_idx_u64 < 512 && l2_idx_u64
                                                    < 512 && l3_idx_u64 < 512,
                                        ;
                                        // Previous assert proves:
                                        // l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE + l2_idx * L2_ENTRY_SIZE + l3_idx * L3_ENTRY_SIZE
                                        // == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64 | (l2_idx as u64) << 21u64 | (l3_idx as u64) << 12u64
                                        assert(interp_l3_dir.interp_of_entry(
                                            l3_idx,
                                        ).map.contains_pair(addr as nat, pte));
                                        assert(interp_l3_dir.interp().map.contains_pair(
                                            addr as nat,
                                            pte,
                                        ));
                                        assert(interp_l2_dir.interp().map.contains_pair(
                                            addr as nat,
                                            pte,
                                        ));
                                        assert(interp_l1_dir.interp().map.contains_pair(
                                            addr as nat,
                                            pte,
                                        ));
                                        interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                                        l0_idx);
                                        assert(interp_l0_dir.interp().map.contains_pair(
                                            addr as nat,
                                            pte,
                                        ));
                                        assert(m1.contains_pair(addr as nat, pte));
                                    },
                                    GhostPageDirectoryEntry::Directory { .. } => assert(false),
                                    GhostPageDirectoryEntry::Empty => assert(false),
                                }
                            },
                            GhostPageDirectoryEntry::Empty => assert(false),
                        }
                    },
                    GhostPageDirectoryEntry::Empty => assert(false),
                }
            },
            _ => assert(false),
        };
    };
    assert forall|addr: nat| !m1.contains_key(addr) ==> !m2.contains_key(addr) by {
        PT::lemma_interp_at_facts(&mem, pt, 0, mem.cr3_spec().base, 0);
        PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
        if addr < MAX_BASE && (exists|pte: PageTableEntry|
            valid_pt_walk(mem, nat_to_u64(addr), pte)) {
        } else {
            if addr >= MAX_BASE {
            } else {
                assert(addr < MAX_BASE);
                let addr: u64 = addr as u64;
                assert(!exists|pte: PageTableEntry| valid_pt_walk(mem, addr, pte)) by {
                    assert(!exists|pte: PageTableEntry|
                        valid_pt_walk(mem, nat_to_u64(addr as nat), pte));
                };
                let l0_idx_u64: u64 = l0_bits!(addr);
                let l0_idx: nat = l0_idx_u64 as nat;
                let l1_idx_u64: u64 = l1_bits!(addr);
                let l1_idx: nat = l1_idx_u64 as nat;
                let l2_idx_u64: u64 = l2_bits!(addr);
                let l2_idx: nat = l2_idx_u64 as nat;
                let l3_idx_u64: u64 = l3_bits!(addr);
                let l3_idx: nat = l3_idx_u64 as nat;
                assert(forall|a: u64| (a & bitmask_inc!(0u64,8u64) == a) ==> a < 512)
                    by (bit_vector);
                assert(l0_idx < 512 && l1_idx < 512 && l2_idx < 512 && l3_idx < 512) by {
                    assert(((addr & bitmask_inc!(12u64,20u64)) >> 12u64) & bitmask_inc!(0u64,8u64)
                        == ((addr & bitmask_inc!(12u64,20u64)) >> 12u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(21u64,29u64)) >> 21u64) & bitmask_inc!(0u64,8u64)
                        == ((addr & bitmask_inc!(21u64,29u64)) >> 21u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(30u64,38u64)) >> 30u64) & bitmask_inc!(0u64,8u64)
                        == ((addr & bitmask_inc!(30u64,38u64)) >> 30u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(39u64,47u64)) >> 39u64) & bitmask_inc!(0u64,8u64)
                        == ((addr & bitmask_inc!(39u64,47u64)) >> 39u64)) by (bit_vector);
                };
                assert(bitmask_inc!(39u64,47u64) == 0xFF80_0000_0000) by (compute);
                assert(bitmask_inc!(30u64,38u64) == 0x007F_C000_0000) by (compute);
                assert(bitmask_inc!(21u64,29u64) == 0x0000_3FE0_0000) by (compute);
                assert(bitmask_inc!(12u64,20u64) == 0x0000_001F_F000) by (compute);
                let interp_l0_dir = PT::interp(&mem, pt);
                let interp_l0_entry = PT::interp_at_entry(
                    &mem,
                    pt,
                    0,
                    mem.cr3_spec().base,
                    0,
                    l0_idx,
                );
                interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                l0_idx);
                match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
                    GhostPageDirectoryEntry::Directory {
                        addr: l0_dir_addr,
                        flag_RW: l0_RW,
                        flag_US: l0_US,
                        flag_XD: l0_XD,
                        ..
                    } => {
                        assert(interp_l0_entry.is_Directory());
                        let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                        let l0_dir_ghost_pt = pt.entries[l0_idx as int].get_Some_0();
                        assert(PT::directories_obey_invariant_at(&mem, pt, 0, mem.cr3_spec().base));
                        assert(PT::inv_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                        assert(interp_l0_dir.directories_obey_invariant());
                        assert(interp_l0_dir.entries[l0_idx as int].get_Directory_0().inv());
                        PT::lemma_interp_at_facts(
                            &mem,
                            l0_dir_ghost_pt,
                            1,
                            l0_dir_addr,
                            l1_base_vaddr,
                        );
                        let interp_l1_dir = PT::interp_at(
                            &mem,
                            l0_dir_ghost_pt,
                            1,
                            l0_dir_addr,
                            l1_base_vaddr,
                        );
                        let interp_l1_entry = PT::interp_at_entry(
                            &mem,
                            l0_dir_ghost_pt,
                            1,
                            l0_dir_addr,
                            l1_base_vaddr,
                            l1_idx,
                        );
                        interp_l1_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                        l1_idx);
                        let low_bits: u64 = addr % (L1_ENTRY_SIZE as u64);
                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + low_bits
                        assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | low_bits == add(
                            add(
                                mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                mul(l1_idx_u64, mul(512, mul(512, 4096))),
                            ),
                            low_bits,
                        )) by (bit_vector)
                            requires
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                low_bits == addr % mul(512, mul(512, 4096)),
                        ;
                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | low_bits))
                            by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                low_bits == addr % mul(512, mul(512, 4096)),
                        ;
                        match read_entry(mem, l0_dir_addr as nat, 1, l1_idx) {
                            GhostPageDirectoryEntry::Page {
                                addr: page_addr,
                                flag_RW: l1_RW,
                                flag_US: l1_US,
                                flag_XD: l1_XD,
                                ..
                            } => {
                                assert_by_contradiction!(!aligned(addr as nat, L1_ENTRY_SIZE as nat), {
                                            let pte = PageTableEntry {
                                                frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                                                flags: Flags {
                                                    is_writable:      l0_RW &&  l1_RW,
                                                    is_supervisor:   !l0_US || !l1_US,
                                                    disable_execute:  l0_XD ||  l1_XD
                                                }
                                            };
                                            assert(valid_pt_walk(mem, addr as u64, pte));
                                        });
                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(
                                    addr as nat,
                                ));
                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                assert(!m2.contains_key(addr as nat));
                            },
                            GhostPageDirectoryEntry::Directory {
                                addr: l1_dir_addr,
                                flag_RW: l1_RW,
                                flag_US: l1_US,
                                flag_XD: l1_XD,
                                ..
                            } => {
                                assert(interp_l1_entry.is_Directory());
                                let l2_base_vaddr = x86_arch_spec.entry_base(
                                    1,
                                    l1_base_vaddr,
                                    l1_idx,
                                );
                                let l1_dir_ghost_pt =
                                    l0_dir_ghost_pt.entries[l1_idx as int].get_Some_0();
                                assert(PT::directories_obey_invariant_at(
                                    &mem,
                                    l0_dir_ghost_pt,
                                    1,
                                    l0_dir_addr,
                                ));
                                assert(PT::inv_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                                PT::lemma_interp_at_facts(
                                    &mem,
                                    l1_dir_ghost_pt,
                                    2,
                                    l1_dir_addr,
                                    l2_base_vaddr,
                                );
                                let interp_l2_dir = PT::interp_at(
                                    &mem,
                                    l1_dir_ghost_pt,
                                    2,
                                    l1_dir_addr,
                                    l2_base_vaddr,
                                );
                                let interp_l2_entry = PT::interp_at_entry(
                                    &mem,
                                    l1_dir_ghost_pt,
                                    2,
                                    l1_dir_addr,
                                    l2_base_vaddr,
                                    l2_idx,
                                );
                                interp_l2_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                                l2_idx);
                                let low_bits: u64 = addr % (L2_ENTRY_SIZE as u64);
                                // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + l2_idx_u64 * L2_ENTRY_SIZE + low_bits
                                assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64
                                    << 21u64) | low_bits == add(
                                    add(
                                        add(
                                            mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                            mul(l1_idx_u64, mul(512, mul(512, 4096))),
                                        ),
                                        mul(l2_idx_u64, mul(512, 4096)),
                                    ),
                                    low_bits,
                                )) by (bit_vector)
                                    requires
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        low_bits == addr % mul(512, 4096),
                                ;
                                assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (
                                l2_idx_u64 << 21u64) | low_bits)) by (bit_vector)
                                    requires
                                        l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                        low_bits == addr % mul(512, 4096),
                                ;
                                match read_entry(mem, l1_dir_addr as nat, 2, l2_idx) {
                                    GhostPageDirectoryEntry::Page {
                                        addr: page_addr,
                                        flag_RW: l2_RW,
                                        flag_US: l2_US,
                                        flag_XD: l2_XD,
                                        ..
                                    } => {
                                        assert_by_contradiction!(!aligned(addr as nat, L2_ENTRY_SIZE as nat), {
                                                    let pte = PageTableEntry {
                                                        frame: MemRegion { base: page_addr as nat, size: L2_ENTRY_SIZE as nat },
                                                        flags: Flags {
                                                            is_writable:      l0_RW &&  l1_RW &&  l2_RW,
                                                            is_supervisor:   !l0_US || !l1_US || !l2_US,
                                                            disable_execute:  l0_XD ||  l1_XD ||  l2_XD
                                                        }
                                                    };
                                                    assert(valid_pt_walk(mem, addr as u64, pte));
                                                });
                                        assert(!interp_l2_dir.interp_of_entry(
                                            l2_idx,
                                        ).map.contains_key(addr as nat));
                                        assert(!interp_l2_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!interp_l1_dir.interp_of_entry(
                                            l1_idx,
                                        ).map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!interp_l0_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!m2.contains_key(addr as nat));
                                    },
                                    GhostPageDirectoryEntry::Directory {
                                        addr: l2_dir_addr,
                                        flag_RW: l2_RW,
                                        flag_US: l2_US,
                                        flag_XD: l2_XD,
                                        ..
                                    } => {
                                        assert(interp_l2_entry.is_Directory());
                                        let l3_base_vaddr = x86_arch_spec.entry_base(
                                            2,
                                            l2_base_vaddr,
                                            l2_idx,
                                        );
                                        let l2_dir_ghost_pt =
                                            l1_dir_ghost_pt.entries[l2_idx as int].get_Some_0();
                                        assert(PT::directories_obey_invariant_at(
                                            &mem,
                                            l1_dir_ghost_pt,
                                            2,
                                            l1_dir_addr,
                                        ));
                                        assert(PT::inv_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr));
                                        PT::lemma_interp_at_facts(
                                            &mem,
                                            l2_dir_ghost_pt,
                                            3,
                                            l2_dir_addr,
                                            l3_base_vaddr,
                                        );
                                        let interp_l3_dir = PT::interp_at(
                                            &mem,
                                            l2_dir_ghost_pt,
                                            3,
                                            l2_dir_addr,
                                            l3_base_vaddr,
                                        );
                                        let interp_l3_entry = PT::interp_at_entry(
                                            &mem,
                                            l2_dir_ghost_pt,
                                            3,
                                            l2_dir_addr,
                                            l3_base_vaddr,
                                            l3_idx,
                                        );
                                        interp_l3_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(
                                        l3_idx);
                                        let low_bits: u64 = addr % (L3_ENTRY_SIZE as u64);
                                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + l2_idx_u64 * L2_ENTRY_SIZE + l3_idx_u64 * L3_ENTRY_SIZE + low_bits
                                        assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (
                                        l2_idx_u64 << 21u64) | (l3_idx_u64 << 12u64) | low_bits
                                            == add(
                                            add(
                                                add(
                                                    add(
                                                        mul(
                                                            l0_idx_u64,
                                                            mul(512, mul(512, mul(512, 4096))),
                                                        ),
                                                        mul(l1_idx_u64, mul(512, mul(512, 4096))),
                                                    ),
                                                    mul(l2_idx_u64, mul(512, 4096)),
                                                ),
                                                mul(l3_idx_u64, 4096),
                                            ),
                                            low_bits,
                                        )) by (bit_vector)
                                            requires
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                low_bits == addr % 4096,
                                        ;
                                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64
                                            << 30u64) | (l2_idx_u64 << 21u64) | (l3_idx_u64
                                            << 12u64) | low_bits)) by (bit_vector)
                                            requires
                                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                addr < mul(
                                                    512u64,
                                                    mul(512, mul(512, mul(512, 4096))),
                                                ),
                                                low_bits == addr % 4096,
                                        ;
                                        match read_entry(mem, l2_dir_addr as nat, 3, l3_idx) {
                                            GhostPageDirectoryEntry::Page {
                                                addr: page_addr,
                                                flag_RW: l3_RW,
                                                flag_US: l3_US,
                                                flag_XD: l3_XD,
                                                ..
                                            } => {
                                                assert_by_contradiction!(!aligned(addr as nat, L3_ENTRY_SIZE as nat), {
                                                            let pte = PageTableEntry {
                                                                frame: MemRegion { base: page_addr as nat, size: L3_ENTRY_SIZE as nat },
                                                                flags: Flags {
                                                                    is_writable:      l0_RW &&  l1_RW &&  l2_RW &&  l3_RW,
                                                                    is_supervisor:   !l0_US || !l1_US || !l2_US || !l3_US,
                                                                    disable_execute:  l0_XD ||  l1_XD ||  l2_XD ||  l3_XD
                                                                }
                                                            };
                                                            assert(valid_pt_walk(mem, addr as u64, pte));
                                                        });
                                                assert(!interp_l3_dir.interp_of_entry(
                                                    l3_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l3_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l2_dir.interp_of_entry(
                                                    l2_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l1_dir.interp_of_entry(
                                                    l1_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l0_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!m2.contains_key(addr as nat));
                                            },
                                            GhostPageDirectoryEntry::Directory {
                                                ..
                                            } => assert(false),
                                            GhostPageDirectoryEntry::Empty => {
                                                assert(!interp_l3_dir.interp_of_entry(
                                                    l3_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l3_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l2_dir.interp_of_entry(
                                                    l2_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l1_dir.interp_of_entry(
                                                    l1_idx,
                                                ).map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!interp_l0_dir.interp().map.contains_key(
                                                    addr as nat,
                                                ));
                                                assert(!m2.contains_key(addr as nat));
                                            },
                                        }
                                    },
                                    GhostPageDirectoryEntry::Empty => {
                                        assert(!interp_l2_dir.interp_of_entry(
                                            l2_idx,
                                        ).map.contains_key(addr as nat));
                                        assert(!interp_l2_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!interp_l1_dir.interp_of_entry(
                                            l1_idx,
                                        ).map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!interp_l0_dir.interp().map.contains_key(
                                            addr as nat,
                                        ));
                                        assert(!m2.contains_key(addr as nat));
                                    },
                                }
                            },
                            GhostPageDirectoryEntry::Empty => {
                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(
                                    addr as nat,
                                ));
                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                assert(!m2.contains_key(addr as nat));
                            },
                        }
                    },
                    GhostPageDirectoryEntry::Page { .. } => assert(false),
                    GhostPageDirectoryEntry::Empty => {
                        let low_bits: u64 = addr % (L0_ENTRY_SIZE as u64);
                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + low_bits
                        assert((l0_idx_u64 << 39u64) | low_bits == add(
                            mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                            low_bits,
                        )) by (bit_vector)
                            requires
                                low_bits == addr % mul(512, mul(512, mul(512, 4096))),
                        ;
                        assert(addr == ((l0_idx_u64 << 39u64) | low_bits)) by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                low_bits == addr % mul(512, mul(512, mul(512, 4096))),
                        ;
                        assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                        assert(!m2.contains_key(addr as nat));
                    },
                };
            }
        }
    };
    assert(m1 =~= m2) by {
        assert forall|addr: nat| m1.dom().contains(addr) <==> m2.dom().contains(addr) by {
            assert(m1.dom().contains(addr) ==> m2.contains_pair(addr, m1[addr]));
            assert(m2.dom().contains(addr) ==> m1.contains_pair(addr, m2[addr]));
        };
        assert forall|addr: nat| #[trigger]
            m1.contains_key(addr) && m2.contains_key(addr) implies m1[addr] == m2[addr] by {
            assert(m1.contains_pair(addr, m1[addr]));
            assert(m2.contains_pair(addr, m1[addr]));
        };
    };
}

proof fn lemma_no_entries_implies_interp_at_aux_no_entries(
    mem: mem::PageTableMemory,
    pt: PTDir,
    layer: nat,
    ptr: usize,
    base_vaddr: nat,
    init: Seq<l1::NodeEntry>,
)
    requires
        mem.regions() == set![mem.cr3_spec()@],
        (forall|i: nat| i < 512 ==> mem.region_view(mem.cr3_spec()@)[i as int] == 0),
        layer == 0,
        PT::inv_at(&mem, pt, layer, ptr),
        forall|i: nat| i < init.len() ==> init[i as int] == l1::NodeEntry::Empty(),
        init.len() <= 512,
    ensures
        ({
            let res = PT::interp_at_aux(&mem, pt, layer, ptr, base_vaddr, init);
            &&& res.len() == 512
            &&& forall|i: nat| i < res.len() ==> res[i as int] == l1::NodeEntry::Empty()
        }),
    decreases 512 - init.len(),
{
    lemma_new_seq::<Option<PTDir>>(512, Option::None);
    let res = PT::interp_at_aux(&mem, pt, layer, ptr, base_vaddr, init);
    if init.len() >= 512 {
    } else {
        let entry = PT::interp_at_entry(&mem, pt, layer, ptr, base_vaddr, init.len());
        assert(PT::ghost_pt_matches_structure(&mem, pt, layer, ptr));
        assert forall|i: nat| i < 512 implies PT::view_at(&mem, pt, layer, ptr, i).is_Empty() by {
            let entry = mem.spec_read(i, pt.region);
            assert((entry & (1u64 << 0)) != (1u64 << 0)) by (bit_vector)
                requires
                    entry == 0u64,
            ;
        };
        assert(entry == l1::NodeEntry::Empty());
        lemma_no_entries_implies_interp_at_aux_no_entries(
            mem,
            pt,
            layer,
            ptr,
            base_vaddr,
            init.push(entry),
        );
    }
}

impl impl_spec::InterfaceSpec for impl_spec::PageTableImpl {
    closed spec fn ispec_inv(&self, mem: &mem::PageTableMemory) -> bool {
        exists|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv()
    }

    proof fn ispec_init_implies_inv(&self, mem: &mem::PageTableMemory) {
        let pt = PTDir {
            region: mem.cr3_spec()@,
            entries: new_seq(512, Option::None),
            used_regions: set![mem.cr3_spec()@],
        };
        lemma_new_seq::<Option<PTDir>>(512, Option::None);
        assert(PT::inv(mem, pt)) by {
            x86_arch_inv();
            axiom_x86_arch_exec_spec();
            PT::lemma_zeroed_page_implies_empty_at(mem, pt, 0, mem.cr3_spec().base);
        };
        lemma_no_entries_implies_interp_at_aux_no_entries(
            *mem,
            pt,
            0,
            mem.cr3_spec().base,
            0,
            seq![],
        );
    }

    fn ispec_map_frame(
        &self,
        mem: &mut mem::PageTableMemory,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (res: MapResult) {
        let mut pt: Ghost<PTDir> = Ghost(
            choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv(),
        );
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH)
                by (compute_only);
            lemma_page_table_walk_interp();
        }
        PT::map_frame(mem, &mut pt, vaddr, pte)
    }

    fn ispec_unmap(&self, mem: &mut mem::PageTableMemory, vaddr: usize) -> (res: UnmapResult) {
        let mut pt: Ghost<PTDir> = Ghost(
            choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv(),
        );
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH)
                by (compute_only);
            lemma_page_table_walk_interp();
        }
        PT::unmap(mem, &mut pt, vaddr)
    }

    fn ispec_resolve(&self, mem: &mem::PageTableMemory, vaddr: usize) -> (res: ResolveResultExec) {
        let pt: Ghost<PTDir> = Ghost(
            choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv(),
        );
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH)
                by (compute_only);
            lemma_page_table_walk_interp();
        }
        match PT::resolve(mem, pt, vaddr) {
            Ok((v, pte)) => ResolveResultExec::Ok(v, pte),
            Err(e) => ResolveResultExec::ErrUnmapped,
        }
    }
}

} // verus!
}

    pub mod spec_pt {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use vstd::prelude::*;
        use vstd::*;

        // trusted: not trusted
        // the interface spec is written in such a way that it guarantees that the impl behaves according
        // to the state machine, and then in the OS state machine we use these definitions, but the actual
        // content of these definitions does not matter because:
        //
        // if we were to mis-specify things in this file, we wouldn't be able to prove the state machine
        // refinement
        //
        // if we split impl <-> system state machines, this becomes trusted for the impl

        use crate::definitions_t::{
            aligned, between, candidate_mapping_in_bounds,
            candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem,
            overlap, Arch, MapResult, PageTableEntry, ResolveResult, UnmapResult,
        };
        use crate::definitions_t::{
            L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_BASE, MAX_PHYADDR, PAGE_SIZE,
            PT_BOUND_HIGH, PT_BOUND_LOW,
        };
        use crate::impl_u::l0;
        use map::*;
        use seq::*;

        verus! {

pub struct PageTableVariables {
    pub map: Map<nat  /* VAddr */ , PageTableEntry>,
}

pub enum PageTableStep {
    Map { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap { vaddr: nat, result: UnmapResult },
    Resolve { vaddr: nat, result: ResolveResult },
    Stutter,
}

pub open spec fn step_Map_enabled(
    map: Map<nat, PageTableEntry>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(map, vaddr, pte)
}

pub open spec fn step_Map(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    pte: PageTableEntry,
    result: MapResult,
) -> bool {
    &&& step_Map_enabled(s1.map, vaddr, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.map, vaddr, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.map === s1.map
    } else {
        &&& result.is_Ok()
        &&& s2.map === s1.map.insert(vaddr, pte)
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH as nat)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    result: UnmapResult,
) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& if s1.map.dom().contains(vaddr) {
        &&& result.is_Ok()
        &&& s2.map === s1.map.remove(vaddr)
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.map === s1.map
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
    &&& vaddr < MAX_BASE
}

pub open spec fn step_Resolve(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    result: ResolveResult,
) -> bool {
    &&& step_Resolve_enabled(vaddr)
    &&& s2 === s1
    &&& match result {
        ResolveResult::Ok(base, pte) => {
            // If result is Ok, it's an existing mapping that contains vaddr..
            &&& s1.map.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
        },
        ResolveResult::ErrUnmapped => {
            // If result is ErrUnmapped, no mapping containing vaddr exists..
            &&& (!exists|base: nat, pte: PageTableEntry|
                s1.map.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size))
        },
    }
}

pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn init(s: PageTableVariables) -> bool {
    s.map === Map::empty()
}

pub open spec fn next_step(
    s1: PageTableVariables,
    s2: PageTableVariables,
    step: PageTableStep,
) -> bool {
    match step {
        PageTableStep::Map { vaddr, pte, result } => step_Map(s1, s2, vaddr, pte, result),
        PageTableStep::Unmap { vaddr, result } => step_Unmap(s1, s2, vaddr, result),
        PageTableStep::Resolve { vaddr, result } => step_Resolve(s1, s2, vaddr, result),
        PageTableStep::Stutter => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

} // verus!
}

    pub mod indexing {
        #![allow(unused_imports)]
        use crate::definitions_t::{
            aligned, between, entry_base_from_index, index_from_base_and_addr, index_from_offset,
            next_entry_base_from_index,
        };
        use crate::extra as lib;
        use builtin::*;
        use builtin_macros::*;
        use vstd::map::*;
        use vstd::modes::*;
        use vstd::option::{Option::*, *};
        use vstd::prelude::*;
        use vstd::result::{Result::*, *};
        use vstd::seq::*;
        use vstd::set::*;
        use vstd::set_lib::*;
        use vstd::vec::*;

        verus! {

///! This module implements an indexing calculus with corresponding lemmas. It only provides spec
///! functions, without any exec versions. The (specialized to specific entry_size) exec versions
///! can be implemented in their own modules and simply assert their equivalence to these spec
///! functions to make use of the lemmas. This is mainly because the absence of overflows may use
///! different bounds depending on the exact context. It also has the benefit that trusted exec
///! functions (e.g. in mem) are fully defined in their own modules
pub open spec fn nat_mul(a: nat, b: nat) -> nat {
    a * b
}

// This lemma has "support" postconditions for lemma_entry_base_from_index. I.e. postconditions
// that may help proving the lhs of some of that lemma's postconditions which are implications.
// However, one of these postconditions triggers on every multiplication, hence this is separated
// in its own lemma.
pub proof fn lemma_entry_base_from_index_support(base: nat, idx: nat, entry_size: nat)
    requires
        entry_size > 0,
    ensures
// forall|nested_es: nat, nested_num: nat|
//     entry_size == nat_mul(nested_es, nested_num)
//     ==> next_entry_base_from_index(base, idx, entry_size)
//         == entry_base_from_index(entry_base_from_index(base, idx, entry_size), nested_num, nested_es),
// Support postconditions:
// Ugly, ugly workaround for mixed triggers.

        forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b),
        forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a),
        forall|a: nat| #[trigger]
            aligned(base, nat_mul(entry_size, a)) && a > 0 ==> aligned(base, entry_size),
{
    assert(forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b)) by (nonlinear_arith);
    assert(forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a)) by (nonlinear_arith);
    assert forall|a: nat| #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0 implies aligned(
        base,
        entry_size,
    ) by {
        lib::mod_mult_zero_implies_mod_zero(base, entry_size, a);
    };
}

pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    requires
        0 < entry_size,
    ensures
        forall|idx2: nat|
            #![trigger entry_base_from_index(base, idx, entry_size), entry_base_from_index(base, idx2, entry_size)]
            idx < idx2 ==> entry_base_from_index(base, idx, entry_size) < entry_base_from_index(
                base,
                idx2,
                entry_size,
            ),
        // // && next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(layer, base, j),
        // TODO: The line above can't be a separate postcondition because it doesn't have any valid triggers.
        // The trigger for it is pretty bad.
        forall|idx2: nat|
            idx < idx2 ==> next_entry_base_from_index(base, idx, entry_size)
                <= entry_base_from_index(base, idx2, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(
            base,
            idx + 1,
            entry_size,
        ),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(
            base,
            idx,
            entry_size,
        ) + entry_size,
        next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(
            base,
            idx,
            entry_size,
        ),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(
                entry_base_from_index(base, idx, entry_size),
                n,
            ),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(
                next_entry_base_from_index(base, idx, entry_size),
                n,
            ),
        aligned(base, entry_size) ==> aligned(
            entry_base_from_index(base, idx, entry_size),
            entry_size,
        ),
        base <= entry_base_from_index(
            base,
            idx,
            entry_size,
        ),
// forall|idx: nat, base: nat, layer: nat|
//     layer < self.layers.len() && idx < self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) < self.upper_vaddr(layer, base),
// forall|idx: nat, base: nat, layer: nat|
// layer < self.layers.len() && idx <= self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) <= self.upper_vaddr(layer, base),
// forall|idx: nat, base: nat, layer: nat|
// layer + 1 < self.layers.len() ==> #[trigger] next_entry_base_from_index(base, idx, entry_size) == self.upper_vaddr(layer + 1, entry_base_from_index(base, idx, entry_size)),
// // Support postconditions:
// forall(|base: nat, n: nat| // Used to infer lhs of next postcondition's implication
//     aligned(base, #[trigger] (entry_size * n)) ==> aligned(base, entry_size)),
// No valid triggers
// Note for thesis report:
// This is really annoying. No mixed triggers means I can't use this postcondition. In the
// less general case (lemma_entry_base) this worked because n happens to be a specific
// function call there on which we can trigger. In other words: the lack of mixed triggers
// makes it impossible to generalize this postcondition.

{
    assert forall|idx2: nat| idx < idx2 implies entry_base_from_index(base, idx, entry_size)
        < entry_base_from_index(base, idx2, entry_size) by {
        assert(entry_base_from_index(base, idx, entry_size) < entry_base_from_index(
            base,
            idx2,
            entry_size,
        )) by (nonlinear_arith)
            requires
                0 < entry_size,
                idx < idx2,
        {
            lib::mult_less_mono_both1(idx, entry_size, idx2, entry_size);
        };
    };
    assert forall|idx2: nat| idx < idx2 implies next_entry_base_from_index(base, idx, entry_size)
        <= entry_base_from_index(base, idx2, entry_size) by {
        assert(next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(
            base,
            idx2,
            entry_size,
        )) by (nonlinear_arith)
            requires
                idx < idx2,
        {};
    };
    assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(
        base,
        idx + 1,
        entry_size,
    ));
    assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(
        base,
        idx,
        entry_size,
    ) + entry_size) by (nonlinear_arith);
    assert(next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(
        base,
        idx,
        entry_size,
    ));
    assert forall|n: nat|
        0 < n && aligned(base, n) && aligned(entry_size, n) implies #[trigger] aligned(
        entry_base_from_index(base, idx, entry_size),
        n,
    ) by {
        assert(aligned(entry_base_from_index(base, idx, entry_size), n)) by (nonlinear_arith)
            requires
                0 < n,
                0 < entry_size,
                aligned(base, n),
                aligned(entry_size, n),
        {
            assert(aligned(idx * entry_size, entry_size)) by {
                lib::mod_of_mul(idx, entry_size);
            };
            assert(aligned(idx * entry_size, n)) by {
                lib::aligned_transitive(idx * entry_size, entry_size, n);
            };
            assert(aligned(base + idx * entry_size, n)) by {
                lib::mod_add_zero(base, idx * entry_size, n);
            };
        };
    };
    assert forall|n: nat|
        0 < n && aligned(base, n) && aligned(entry_size, n) implies #[trigger] aligned(
        next_entry_base_from_index(base, idx, entry_size),
        n,
    ) by {
        assert(aligned(next_entry_base_from_index(base, idx, entry_size), n)) by (nonlinear_arith)
            requires
                0 < n,
                0 < entry_size,
                aligned(base, n),
                aligned(entry_size, n),
        {
            assert(aligned((idx + 1) * entry_size, entry_size)) by {
                lib::mod_of_mul(idx + 1, entry_size);
            };
            assert(aligned((idx + 1) * entry_size, n)) by {
                lib::aligned_transitive((idx + 1) * entry_size, entry_size, n);
            };
            assert(aligned(base + (idx + 1) * entry_size, n)) by {
                lib::mod_add_zero(base, (idx + 1) * entry_size, n);
            };
        };
    };
    assert(aligned(base, entry_size) ==> aligned(
        entry_base_from_index(base, idx, entry_size),
        entry_size,
    ));
    assert(base <= entry_base_from_index(base, idx, entry_size));
}

pub proof fn lemma_index_from_base_and_addr(base: nat, addr: nat, entry_size: nat, num_entries: nat)
    requires
        addr >= base,
        addr < entry_base_from_index(base, num_entries, entry_size),
        entry_size > 0,
    ensures
        ({
            let idx = index_from_base_and_addr(base, addr, entry_size);
            &&& idx < num_entries
            &&& between(
                addr,
                entry_base_from_index(base, idx, entry_size),
                next_entry_base_from_index(base, idx, entry_size),
            )
            &&& aligned(base, entry_size) && aligned(addr, entry_size) ==> addr
                == entry_base_from_index(base, idx, entry_size)
        }),
{
    let idx = index_from_base_and_addr(base, addr, entry_size);
    assert(idx < num_entries) by (nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    {};
    assert(between(
        addr,
        entry_base_from_index(base, idx, entry_size),
        next_entry_base_from_index(base, idx, entry_size),
    )) by (nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    {};
    assert(aligned(base, entry_size) && aligned(addr, entry_size) ==> addr == entry_base_from_index(
        base,
        idx,
        entry_size,
    )) by (nonlinear_arith)
        requires
            addr >= base,
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    {
        if aligned(base, entry_size) && aligned(addr, entry_size) {
            lib::subtract_mod_eq_zero(base, addr, entry_size);
            lib::div_mul_cancel(sub(addr, base), entry_size);
        }
    };
}

} // verus!
}

    pub mod os_refinement {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use vstd::map::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::set::*;
        use vstd::set_lib::*;

        use crate::definitions_t::{
            aligned, between, candidate_mapping_overlaps_existing_pmem,
            candidate_mapping_overlaps_existing_vmem, new_seq, overlap, Arch, MapResult, MemRegion,
            PageTableEntry, RWOp, ResolveResult, UnmapResult,
        };
        use crate::definitions_t::{
            L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, PAGE_SIZE, PT_BOUND_HIGH, PT_BOUND_LOW,
            WORD_SIZE,
        };
        use crate::extra as lib;
        use crate::impl_u::indexing;
        use crate::impl_u::spec_pt;
        use crate::spec_t::mem::word_index_spec;
        use crate::spec_t::os::*;
        use crate::spec_t::{hardware, hlspec};

        verus! {

pub proof fn lemma_pt_mappings_dont_overlap_in_pmem(this: OSVariables, other: OSVariables)
    requires
        this.pt_mappings_dont_overlap_in_pmem(),
        this.pt_entry_sizes_are_valid(),
        other.pt_entry_sizes_are_valid(),
        this.tlb_is_submap_of_pt(),
        other.tlb_is_submap_of_pt(),
    ensures
        forall|base, pte|
            !candidate_mapping_overlaps_existing_pmem(this.interp_pt_mem(), base, pte)
                && other.interp_pt_mem() === this.interp_pt_mem().insert(base, pte)
                ==> other.pt_mappings_dont_overlap_in_pmem(),
        forall|base|
            other.interp_pt_mem() === this.interp_pt_mem().remove(base)
                ==> other.pt_mappings_dont_overlap_in_pmem(),
{
    assert forall|base, pte|
        !candidate_mapping_overlaps_existing_pmem(this.interp_pt_mem(), base, pte)
            && other.interp_pt_mem() === this.interp_pt_mem().insert(
            base,
            pte,
        ) implies other.pt_mappings_dont_overlap_in_pmem() by {
        lemma_effective_mappings_equal_interp_pt_mem(this);
        lemma_effective_mappings_equal_interp_pt_mem(other);
        assert forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            other.interp_pt_mem().contains_pair(b1, pte1) && other.interp_pt_mem().contains_pair(
                b2,
                pte2,
            ) implies ((b1 == b2) || !overlap(pte1.frame, pte2.frame)) by {
            if b1 == b2 {
            } else {
                if b1 == base {
                    assert(!overlap(pte1.frame, pte2.frame));
                } else {
                    assert(this.interp_pt_mem().dom().contains(b1));
                    assert(this.interp_pt_mem().contains_pair(b1, pte1));
                    if b2 == base {
                        assert(pte2 === pte);
                        assert(!candidate_mapping_overlaps_existing_pmem(
                            this.interp_pt_mem(),
                            base,
                            pte,
                        ));
                        assert(forall|b: nat|
                            {
                                this.interp_pt_mem().dom().contains(b) ==> !(#[trigger] overlap(
                                    pte.frame,
                                    this.interp_pt_mem()[b].frame,
                                ))
                            });
                        assert(this.interp_pt_mem()[b1] === pte1);
                        assert(this.interp_pt_mem().dom().contains(b1));
                        assert(!overlap(pte.frame, pte1.frame));
                        assert(pte.frame.size > 0);
                        assert(pte1.frame.size > 0);
                        assert(!overlap(pte1.frame, pte.frame));
                    } else {
                        assert(this.interp_pt_mem().dom().contains(b2));
                        assert(this.interp_pt_mem().contains_pair(b2, pte2));
                        assert(!overlap(pte1.frame, pte2.frame));
                    }
                }
            }
        };
    };
    assert forall|base|
        other.interp_pt_mem() === this.interp_pt_mem().remove(
            base,
        ) implies other.pt_mappings_dont_overlap_in_pmem() by {
        lemma_effective_mappings_equal_interp_pt_mem(this);
        lemma_effective_mappings_equal_interp_pt_mem(other);
        assert forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            other.interp_pt_mem().contains_pair(b1, pte1) && other.interp_pt_mem().contains_pair(
                b2,
                pte2,
            ) implies ((b1 == b2) || !overlap(pte1.frame, pte2.frame)) by {
            if b1 == b2 {
            } else {
                assert(b2 != base);
                if b1 == base {
                    assert(!overlap(pte1.frame, pte2.frame));
                } else {
                    assert(this.interp_pt_mem().dom().contains(b1));
                    assert(this.interp_pt_mem().contains_pair(b1, pte1));
                    assert(this.interp_pt_mem().dom().contains(b2));
                    assert(this.interp_pt_mem().contains_pair(b2, pte2));
                    assert(!overlap(pte1.frame, pte2.frame));
                }
            }
        };
    };
}

pub proof fn lemma_effective_mappings_equal_interp_pt_mem(this: OSVariables)
    requires
        this.tlb_is_submap_of_pt(),
    ensures
        this.effective_mappings() === this.interp_pt_mem(),
{
    let eff = this.effective_mappings();
    let pt = this.interp_pt_mem();
    let tlb = this.hw.tlb;
    assert forall|base| eff.dom().contains(base) implies pt.dom().contains(base) by {
        assert(pt.contains_pair(base, eff[base]));
    };
    assert forall|base| pt.dom().contains(base) implies eff.dom().contains(base) by {
        if tlb.dom().contains(base) {
            if tlb[base] !== pt[base] {
                let pteprime = tlb[base];
                assert(pt.contains_pair(base, pteprime));
                assert(false);
            }
            assert(eff.contains_pair(base, pt[base]));
        } else {
            assert(eff.contains_pair(base, pt[base]));
        }
    };
    assert forall|base|
        eff.dom().contains(base) && pt.dom().contains(base) implies #[trigger] pt[base]
        === #[trigger] eff[base] by {
        let pte = eff[base];
        assert(eff.contains_pair(base, pte));
        assert(pt.contains_pair(base, pte));
    };
    lib::assert_maps_equal_contains_pair::<nat, PageTableEntry>(eff, pt);
}

pub proof fn lemma_effective_mappings_other(this: OSVariables, other: OSVariables)
    requires
        this.tlb_is_submap_of_pt(),
        other.tlb_is_submap_of_pt(),
        this.hw.pt_mem === other.hw.pt_mem,
    ensures
        this.effective_mappings() === other.effective_mappings(),
{
    let eff1 = this.effective_mappings();
    let eff2 = other.effective_mappings();
    let tlb1 = this.hw.tlb;
    let tlb2 = other.hw.tlb;
    let pt1 = this.interp_pt_mem();
    let pt2 = other.interp_pt_mem();
    assert forall|base, pte| eff1.contains_pair(base, pte) implies eff2.contains_pair(
        base,
        pte,
    ) by {
        assert(pt1.contains_pair(base, pte));
        assert(pt2.contains_pair(base, pte));
        if tlb2.dom().contains(base) {
            if tlb2[base] !== pte {
                let pteprime = tlb2[base];
                assert(pt2.contains_pair(base, pteprime));
                assert(false);
            }
            assert(tlb2.contains_pair(base, pte));
            assert(eff2.contains_pair(base, pte));
        } else {
            assert(eff2.contains_pair(base, pte));
        }
        assert(eff2.contains_pair(base, pte));
    };
    assert forall|base, pte| eff2.contains_pair(base, pte) implies eff1.contains_pair(
        base,
        pte,
    ) by {
        assert(pt1.contains_pair(base, pte));
        assert(pt2.contains_pair(base, pte));
        if tlb1.dom().contains(base) {
            if tlb1[base] !== pte {
                let pteprime = tlb1[base];
                assert(pt1.contains_pair(base, pteprime));
                assert(false);
            }
            assert(tlb1.contains_pair(base, pte));
            assert(eff1.contains_pair(base, pte));
        } else {
            assert(eff1.contains_pair(base, pte));
        }
        assert(eff1.contains_pair(base, pte));
    };
    lib::assert_maps_equal_contains_pair::<nat, PageTableEntry>(eff1, eff2);
}

proof fn lemma_interp(this: OSVariables)
    requires
        this.inv(),
    ensures
        this.interp().mappings === this.interp_pt_mem(),
        this.interp().mappings === this.effective_mappings(),
        forall|base: nat, pte: PageTableEntry, vmem_idx: nat|
            {
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                #[trigger] this.interp_pt_mem().contains_pair(base, pte) && between(
                    vaddr,
                    base,
                    base + pte.frame.size,
                ) && pmem_idx < this.hw.mem.len() ==> this.hw.mem[pmem_idx as int]
                    === #[trigger] this.interp().mem[vmem_idx]
            },
{
    lemma_effective_mappings_equal_interp_pt_mem(this);
    assert forall|base: nat, pte: PageTableEntry, vmem_idx: nat|
        {
            let vaddr = vmem_idx * WORD_SIZE as nat;
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            #[trigger] this.interp_pt_mem().contains_pair(base, pte) && between(
                vaddr,
                base,
                base + pte.frame.size,
            ) && pmem_idx < this.hw.mem.len()
        } implies this.hw.mem[word_index_spec(
        (pte.frame.base + ((vmem_idx * WORD_SIZE as nat) - base)) as nat,
    ) as int] === #[trigger] this.interp().mem[vmem_idx] by {
        let pt = this.interp_pt_mem();
        let sys_mem = this.hw.mem;
        let vaddr = vmem_idx * WORD_SIZE as nat;
        let paddr = (pte.frame.base + (vaddr - base)) as nat;
        let pmem_idx = word_index_spec(paddr);
        if this.hw.mem[pmem_idx as int] !== this.interp().mem[vmem_idx] {
            assert(exists|base, pte|
                pt.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size));
            let (base2, pte2): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry|
                #![auto]
                pt.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            if base2 == base {
                assert(pte2 === pte);
                assert(false);
            } else {
                assert(overlap(
                    MemRegion { base: base, size: pte.frame.size },
                    MemRegion { base: base2, size: pte2.frame.size },
                ));
                assert(false);
            }
        }
    }
}

proof fn lemma_interp_other(this: OSVariables, other: OSVariables)
    requires
        other.hw.mem === this.hw.mem,
        forall|base, pte|
            this.effective_mappings().contains_pair(base, pte)
                ==> other.effective_mappings().contains_pair(base, pte),
        this.inv(),
        other.inv(),
    ensures
        forall|word_idx: nat|
            this.interp().mem.dom().contains(word_idx) ==> {
                &&& other.interp().mem.dom().contains(word_idx)
                &&& #[trigger] other.interp().mem[word_idx]
                    == #[trigger] this.interp().mem[word_idx]
            },
{
    assert forall|word_idx: nat| this.interp().mem.dom().contains(word_idx) implies {
        &&& other.interp().mem.dom().contains(word_idx)
        &&& #[trigger] other.interp().mem[word_idx] == #[trigger] this.interp().mem[word_idx]
    } by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let this_mappings = this.effective_mappings();
        let other_mappings = other.effective_mappings();
        let phys_mem_size = this.interp_constants().phys_mem_size;
        assert(hlspec::mem_domain_from_mappings_contains(phys_mem_size, word_idx, this_mappings));
        let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry|
            #![auto]
            this_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
        assert(this_mappings.contains_pair(base, pte));
        assert(between(vaddr, base, base + pte.frame.size));
        assert(other_mappings.contains_pair(base, pte));
        assert(other.interp().mem.dom().contains(word_idx));
        if other.interp().mem[word_idx] !== this.interp().mem[word_idx] {
            let (base2, pte2): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry|
                #![auto]
                other_mappings.contains_pair(base, pte) && between(
                    vaddr,
                    base,
                    base + pte.frame.size,
                );
            assert(other_mappings.contains_pair(base, pte));
            assert(other_mappings.contains_pair(base2, pte2));
            assert(between(vaddr, base2, base2 + pte2.frame.size));
            assert(overlap(
                MemRegion { base: base, size: base + pte.frame.size },
                MemRegion { base: base2, size: base2 + pte2.frame.size },
            ));
            assert(other.pt_mappings_dont_overlap_in_vmem());
            assert(((base == base2) || !overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: base2, size: pte2.frame.size },
            )));
            assert(base != base2);
            assert(false);
        }
    };
}

// not technically necessary, i think
proof fn init_implies_pt_init(s: OSVariables)
    requires
        init(s),
    ensures
        spec_pt::init(s.pt_variables()),
;

proof fn init_implies_inv(s: OSVariables)
    requires
        init(s),
    ensures
        s.inv(),
{
    reveal(OSVariables::pt_entries_aligned);
}

proof fn next_step_preserves_inv(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step),
    ensures
        s2.inv(),
{
    reveal(OSVariables::pt_entries_aligned);
    match step {
        OSStep::HW { step: system_step } => {
            assert(step_HW(s1, s2, system_step));
        },
        OSStep::Map { vaddr, pte, result } => {
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(step_Map(s1, s2, vaddr, pte, result));
            assert(spec_pt::step_Map(pt_s1, pt_s2, vaddr, pte, result));
            assert(!candidate_mapping_overlaps_existing_pmem(pt_s1.map, vaddr, pte));
            if candidate_mapping_overlaps_existing_vmem(pt_s1.map, vaddr, pte) {
                assert(s2.inv());
            } else {
                assert(forall|base, pte|
                    s1.interp_pt_mem().contains_pair(base, pte)
                        ==> s2.interp_pt_mem().contains_pair(base, pte));
                assert forall|base, pteprime|
                    s2.interp_pt_mem().contains_pair(base, pteprime) implies {
                    ||| pteprime.frame.size == L3_ENTRY_SIZE
                    ||| pteprime.frame.size == L2_ENTRY_SIZE
                    ||| pteprime.frame.size == L1_ENTRY_SIZE
                } by {
                    if vaddr == base {
                        assert({
                            ||| pteprime.frame.size == L3_ENTRY_SIZE
                            ||| pteprime.frame.size == L2_ENTRY_SIZE
                            ||| pteprime.frame.size == L1_ENTRY_SIZE
                        });
                    } else {
                        assert(s1.pt_entry_sizes_are_valid());
                        assert(s1.interp_pt_mem().dom().contains(base));
                        assert(s1.interp_pt_mem().contains_pair(base, pteprime));
                        assert({
                            ||| pteprime.frame.size == L3_ENTRY_SIZE
                            ||| pteprime.frame.size == L2_ENTRY_SIZE
                            ||| pteprime.frame.size == L1_ENTRY_SIZE
                        });
                    }
                };
                assert(s2.pt_entry_sizes_are_valid());
                assert(s2.tlb_is_submap_of_pt());
                lemma_pt_mappings_dont_overlap_in_pmem(s1, s2);
                assert(s2.pt_mappings_dont_overlap_in_pmem());
                assert(s2.pt_entries_aligned()) by {
                    assert forall|base2, pte2|
                        s2.interp_pt_mem().contains_pair(base2, pte2) implies aligned(base2, 8)
                        && aligned(pte2.frame.base, 8) by {
                        if base2 === vaddr {
                            assert(pte2 === pte);
                            assert(aligned(vaddr, pte.frame.size));
                            assert(aligned(pte.frame.base, pte.frame.size));
                            if pte.frame.size == L3_ENTRY_SIZE as nat {
                                lib::aligned_transitive(pte.frame.base, L3_ENTRY_SIZE as nat, 8);
                                lib::aligned_transitive(vaddr, L3_ENTRY_SIZE as nat, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            } else if pte.frame.size == L2_ENTRY_SIZE as nat {
                                lib::aligned_transitive(pte.frame.base, L2_ENTRY_SIZE as nat, 8);
                                lib::aligned_transitive(vaddr, L2_ENTRY_SIZE as nat, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            } else {
                                assert(pte.frame.size == L1_ENTRY_SIZE as nat);
                                assert(aligned(L1_ENTRY_SIZE as nat, 8));
                                lib::aligned_transitive(pte.frame.base, L1_ENTRY_SIZE as nat, 8);
                                lib::aligned_transitive(vaddr, L1_ENTRY_SIZE as nat, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            }
                        } else {
                            assert(s1.interp_pt_mem().contains_pair(base2, pte2));
                        }
                    };
                };
                assert(s2.inv());
            }
        },
        OSStep::Unmap { vaddr, result } => {
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(step_Unmap(s1, s2, vaddr, result));
            assert(spec_pt::step_Unmap(pt_s1, pt_s2, vaddr, result));
            if pt_s1.map.dom().contains(vaddr) {
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(vaddr));
                // assert(s2.pt_mappings_dont_overlap_in_vmem());
                assert forall|base2, pte2|
                    s2.hw.tlb.contains_pair(
                        base2,
                        pte2,
                    ) implies #[trigger] s2.interp_pt_mem().contains_pair(base2, pte2) by {
                    assert(s1.hw.tlb.contains_pair(base2, pte2));
                    assert(s1.tlb_is_submap_of_pt());
                    assert(s1.interp_pt_mem().contains_pair(base2, pte2));
                    assert(s2.interp_pt_mem().contains_pair(base2, pte2));
                };
                assert forall|baseprime, pteprime|
                    s2.interp_pt_mem().contains_pair(baseprime, pteprime) implies {
                    ||| pteprime.frame.size == L3_ENTRY_SIZE
                    ||| pteprime.frame.size == L2_ENTRY_SIZE
                    ||| pteprime.frame.size == L1_ENTRY_SIZE
                } by {
                    assert(s1.pt_entry_sizes_are_valid());
                    assert(s1.interp_pt_mem().dom().contains(baseprime));
                    assert(s1.interp_pt_mem().contains_pair(baseprime, pteprime));
                    assert({
                        ||| pteprime.frame.size == L3_ENTRY_SIZE
                        ||| pteprime.frame.size == L2_ENTRY_SIZE
                        ||| pteprime.frame.size == L1_ENTRY_SIZE
                    });
                };
                assert(s2.pt_entry_sizes_are_valid());
                lemma_pt_mappings_dont_overlap_in_pmem(s1, s2);
                assert(s2.pt_entries_aligned()) by {
                    assert forall|base, pte|
                        s2.interp_pt_mem().contains_pair(base, pte) implies aligned(base, 8)
                        && aligned(pte.frame.base, 8) by {
                        assert(s1.interp_pt_mem().contains_pair(base, pte));
                    };
                };
                assert(s2.inv());
            } else {
                assert(s2.inv());
            }
        },
        OSStep::Resolve { vaddr, result } => (),
    }
}

proof fn init_refines_hl_init(s: OSVariables)
    requires
        init(s),
    ensures
        hlspec::init(s.interp()),
{
    lemma_effective_mappings_equal_interp_pt_mem(s);
    assert_maps_equal!(s.interp().mem, Map::empty());
}

proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step),
    ensures
        hlspec::next_step(s1.interp_constants(), s1.interp(), s2.interp(), step.interp()),
{
    next_step_preserves_inv(s1, s2, step);
    lemma_effective_mappings_equal_interp_pt_mem(s1);
    lemma_effective_mappings_equal_interp_pt_mem(s2);
    let abs_s1 = s1.interp();
    let abs_s2 = s2.interp();
    let abs_c = s1.interp_constants();
    let sys_s1 = s1.hw;
    let sys_s2 = s2.hw;
    let pt1 = s1.interp_pt_mem();
    let pt2 = s2.interp_pt_mem();
    let abs_step = step.interp();
    match step {
        OSStep::HW { step: system_step } => {
            lemma_effective_mappings_other(s1, s2);
            match system_step {
                hardware::HWStep::ReadWrite { vaddr, paddr, op, pte } => {
                    // hlspec::AbstractStep::ReadWrite { vaddr, op, pte }
                    let pmem_idx = word_index_spec(paddr);
                    let vmem_idx = word_index_spec(vaddr);
                    assert(sys_s2.pt_mem === sys_s1.pt_mem);
                    assert(sys_s2.tlb === sys_s1.tlb);
                    match pte {
                        Some((base, pte)) => {
                            lemma_interp(s1);
                            lemma_interp(s2);
                            // hw
                            assert(sys_s1.tlb.contains_pair(base, pte));
                            assert(between(vaddr, base, base + pte.frame.size));
                            assert(paddr === (pte.frame.base + (vaddr - base)) as nat);
                            // abs
                            assert(abs_s1.mappings.contains_pair(base, pte));
                            match op {
                                RWOp::Store { new_value, result } => {
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor
                                        && pte.flags.is_writable {
                                        assert(result.is_Ok());
                                        assert(sys_s2.mem === sys_s1.mem.update(
                                            pmem_idx as int,
                                            new_value,
                                        ));
                                        assert(hlspec::mem_domain_from_mappings_contains(
                                            abs_c.phys_mem_size,
                                            vmem_idx,
                                            s1.interp_pt_mem(),
                                        ));
                                        assert(abs_s1.mem.dom() === abs_s2.mem.dom());
                                        assert(sys_s1.mem[pmem_idx as int] == abs_s1.mem[vmem_idx]);
                                        assert(abs_s1.mem.dom().contains(vmem_idx));
                                        assert(abs_s1.mem.insert(vmem_idx, new_value).dom()
                                            === abs_s1.mem.dom().insert(vmem_idx));
                                        assert_sets_equal!(abs_s1.mem.dom(), abs_s1.mem.dom().insert(vmem_idx));
                                        assert(abs_s1.mem.insert(vmem_idx, new_value).dom()
                                            === abs_s2.mem.dom());
                                        assert forall|vmem_idx2: nat|
                                            abs_s2.mem.dom().contains(vmem_idx2)
                                                && abs_s1.mem.insert(
                                                vmem_idx,
                                                new_value,
                                            ).dom().contains(
                                                vmem_idx2,
                                            ) implies #[trigger] abs_s2.mem[vmem_idx2]
                                            == abs_s1.mem.insert(
                                            vmem_idx,
                                            new_value,
                                        )[vmem_idx2] by {
                                            if vmem_idx2 == vmem_idx {
                                                assert(abs_s2.mem[vmem_idx2] == new_value);
                                            } else {
                                                assert(hlspec::mem_domain_from_mappings_contains(
                                                    abs_c.phys_mem_size,
                                                    vmem_idx2,
                                                    pt1,
                                                ));
                                                let vaddr2 = vmem_idx2 * WORD_SIZE as nat;
                                                let (base2, pte2): (nat, PageTableEntry) = choose|
                                                    base2: nat,
                                                    pte2: PageTableEntry,
                                                |
                                                    {
                                                        let paddr2 = (pte2.frame.base + (vaddr2
                                                            - base2)) as nat;
                                                        let pmem_idx2 = word_index_spec(paddr2);
                                                        &&& #[trigger] pt1.contains_pair(
                                                            base2,
                                                            pte2,
                                                        )
                                                        &&& between(
                                                            vaddr2,
                                                            base2,
                                                            base2 + pte2.frame.size,
                                                        )
                                                        &&& pmem_idx2 < abs_c.phys_mem_size
                                                    };
                                                let paddr2 = (pte2.frame.base + (vaddr2
                                                    - base2)) as nat;
                                                let pmem_idx2 = word_index_spec(paddr2);
                                                assert(pt1.contains_pair(base2, pte2));
                                                assert(between(
                                                    vaddr2,
                                                    base2,
                                                    base2 + pte2.frame.size,
                                                ));
                                                assert(pmem_idx2 < abs_c.phys_mem_size);
                                                assert(abs_s1.mem[vmem_idx2]
                                                    == s1.hw.mem[pmem_idx2 as int]);
                                                assert(abs_s2.mem[vmem_idx2]
                                                    == s2.hw.mem[pmem_idx2 as int]);
                                                assert(s2.hw.mem === s1.hw.mem.update(
                                                    pmem_idx as int,
                                                    new_value,
                                                ));
                                                assert(pmem_idx < s1.hw.mem.len());
                                                assert(pmem_idx2 < s1.hw.mem.len());
                                                lib::mod_of_mul(vmem_idx2, WORD_SIZE as nat);
                                                assert(aligned(paddr, 8)) by {
                                                    reveal(OSVariables::pt_entries_aligned);
                                                    assert(aligned(pte.frame.base, 8));
                                                    assert(aligned(base, 8));
                                                    assert(aligned(vaddr, 8));
                                                    lib::subtract_mod_eq_zero(base, vaddr, 8);
                                                    lib::mod_add_zero(
                                                        pte.frame.base,
                                                        sub(vaddr, base),
                                                        8,
                                                    );
                                                };
                                                assert(aligned(paddr2, 8)) by {
                                                    reveal(OSVariables::pt_entries_aligned);
                                                    assert(aligned(pte2.frame.base, 8));
                                                    assert(aligned(base2, 8));
                                                    assert(aligned(vaddr2, 8));
                                                    lib::subtract_mod_eq_zero(base2, vaddr2, 8);
                                                    lib::mod_add_zero(
                                                        pte2.frame.base,
                                                        sub(vaddr2, base2),
                                                        8,
                                                    );
                                                };
                                                if pmem_idx == pmem_idx2 {
                                                    assert(vaddr != vaddr2);
                                                    assert(pte === pte2);
                                                    assert(vaddr - base != vaddr2 - base);
                                                    assert(paddr != paddr2);
                                                    assert(paddr == (pte.frame.base + (vaddr
                                                        - base)) as nat);
                                                    assert(paddr2 == (pte2.frame.base + (vaddr2
                                                        - base2)) as nat);
                                                    assert(false);
                                                }
                                                assert(s1.hw.mem[pmem_idx2 as int]
                                                    == s2.hw.mem[pmem_idx2 as int]);
                                                assert(abs_s2.mem[vmem_idx2]
                                                    == abs_s1.mem[vmem_idx2]);
                                            }
                                        };
                                        assert_maps_equal!(abs_s2.mem, abs_s1.mem.insert(vmem_idx, new_value));
                                        assert(hlspec::step_ReadWrite(
                                            abs_c,
                                            abs_s1,
                                            abs_s2,
                                            vaddr,
                                            op,
                                            Some((base, pte)),
                                        ));
                                        // Generalizing from the previous assert to the
                                        // postcondition seems unstable. Simply assuming the
                                        // statement after the assert somehow fixes it. (As does
                                        // increasing the rlimit to 50, luckily.)
                                        // assume(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(sys_s2.mem === sys_s1.mem);
                                        assert(hlspec::step_ReadWrite(
                                            abs_c,
                                            abs_s1,
                                            abs_s2,
                                            vaddr,
                                            op,
                                            Some((base, pte)),
                                        ));
                                    }
                                },
                                RWOp::Load { is_exec, result } => {
                                    assert(sys_s2.mem === sys_s1.mem);
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor && (
                                    is_exec ==> !pte.flags.disable_execute) {
                                        assert(result.is_Value());
                                        assert(result.get_Value_0() == sys_s1.mem[pmem_idx as int]);
                                        assert(hlspec::mem_domain_from_mappings_contains(
                                            abs_c.phys_mem_size,
                                            vmem_idx,
                                            s1.interp_pt_mem(),
                                        ));
                                        assert(sys_s1.mem[pmem_idx as int] == abs_s1.mem[vmem_idx]);
                                        assert(hlspec::step_ReadWrite(
                                            abs_c,
                                            abs_s1,
                                            abs_s2,
                                            vaddr,
                                            op,
                                            Some((base, pte)),
                                        ));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(hlspec::step_ReadWrite(
                                            abs_c,
                                            abs_s1,
                                            abs_s2,
                                            vaddr,
                                            op,
                                            Some((base, pte)),
                                        ));
                                    }
                                },
                            }
                        },
                        None => {
                            assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, pte));
                        },
                    }
                    assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, pte));
                    assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
                },
                hardware::HWStep::PTMemOp => assert(false),
                hardware::HWStep::TLBFill { vaddr, pte } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
                hardware::HWStep::TLBEvict { vaddr } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
            }
        },
        OSStep::Map { vaddr, pte, result } => {
            // hlspec::AbstractStep::Map { vaddr, pte }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Map { vaddr, pte, result });
            assert(step_Map(s1, s2, vaddr, pte, result));
            assert(spec_pt::step_Map(pt_s1, pt_s2, vaddr, pte, result));
            assert(hlspec::step_Map_enabled(abs_s1.mappings, vaddr, pte));
            if candidate_mapping_overlaps_existing_vmem(pt_s1.map, vaddr, pte) {
                assert(candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            } else {
                assert(!candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(forall|base, pte|
                    s1.interp_pt_mem().contains_pair(base, pte)
                        ==> s2.interp_pt_mem().contains_pair(base, pte));
                assert(forall|base, pte|
                    s1.interp().mappings.contains_pair(base, pte)
                        ==> s2.interp().mappings.contains_pair(base, pte));
                assert(s1.interp().mappings === s1.interp_pt_mem());
                assert(s2.interp().mappings === s2.interp_pt_mem());
                lemma_interp_other(s1, s2);
                assert(result.is_Ok());
                assert(abs_s2.mappings === abs_s1.mappings.insert(vaddr, pte));
                assert forall|word_idx| #[trigger]
                    abs_s1.mem.dom().contains(word_idx) implies abs_s2.mem[word_idx]
                    === abs_s1.mem[word_idx] by {
                    assert(abs_s2.mem.dom().contains(word_idx));
                    assert(abs_s2.mem[word_idx] == abs_s1.mem[word_idx]);
                };
                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                    abs_c.phys_mem_size,
                    abs_s2.mappings,
                ));
                assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            }
            assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
        OSStep::Unmap { vaddr, result } => {
            // hlspec::AbstractStep::Unmap { vaddr }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Unmap { vaddr, result });
            assert(step_Unmap(s1, s2, vaddr, result));
            assert(spec_pt::step_Unmap(pt_s1, pt_s2, vaddr, result));
            assert(hlspec::step_Unmap_enabled(vaddr));
            if pt_s1.map.dom().contains(vaddr) {
                assert(abs_s1.mappings.dom().contains(vaddr));
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(vaddr));
                assert(abs_s2.mappings === abs_s1.mappings.remove(vaddr));
                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                    abs_c.phys_mem_size,
                    abs_s2.mappings,
                ));
                lemma_interp_other(s2, s1);
                assert forall|word_idx| #[trigger]
                    abs_s2.mem.dom().contains(word_idx) implies abs_s1.mem[word_idx]
                    === abs_s2.mem[word_idx] by {
                    assert(abs_s1.mem[word_idx] == abs_s2.mem[word_idx]);
                };
                assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            } else {
                assert(!abs_s1.mappings.dom().contains(vaddr));
                assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            }
            assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
        OSStep::Resolve { vaddr, result } => {
            // hlspec::AbstractStep::Resolve { vaddr, result }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Resolve { vaddr, result });
            assert(step_Resolve(s1, s2, vaddr, result));
            assert(spec_pt::step_Resolve(pt_s1, pt_s2, vaddr, result));
            match result {
                ResolveResult::Ok(base, pte) => {
                    assert(hlspec::step_Resolve(
                        abs_c,
                        abs_s1,
                        abs_s2,
                        vaddr,
                        ResolveResult::Ok(base, pte),
                    ));
                },
                ResolveResult::ErrUnmapped => {
                    let vmem_idx = word_index_spec(vaddr);
                    assert(vmem_idx * WORD_SIZE == vaddr);
                    if hlspec::mem_domain_from_mappings(
                        abs_c.phys_mem_size,
                        abs_s1.mappings,
                    ).contains(vmem_idx) {
                        assert(hlspec::mem_domain_from_mappings_contains(
                            abs_c.phys_mem_size,
                            vmem_idx,
                            abs_s1.mappings,
                        ));
                        let (base, pte): (nat, PageTableEntry) = choose|
                            base: nat,
                            pte: PageTableEntry,
                        |
                            {
                                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                                let pmem_idx = word_index_spec(paddr);
                                &&& #[trigger] abs_s1.mappings.contains_pair(base, pte)
                                &&& between(vaddr, base, base + pte.frame.size)
                                &&& pmem_idx < abs_c.phys_mem_size
                            };
                        assert(pt_s1.map.contains_pair(base, pte));
                        assert(false);
                    }
                    assert(hlspec::step_Resolve(abs_c, abs_s1, abs_s2, vaddr, result));
                },
            }
            assert(hlspec::step_Resolve(abs_c, abs_s1, abs_s2, vaddr, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
    }
}

} // verus!
}
}

pub mod definitions_t {
    #![allow(unused_imports)]
    #![verus::trusted]

    // trusted: these are used in trusted definitions
    //
    // `overlap_sanity_check` hardens a spec, so we don't count it as trusted

    use crate::extra as lib; // THIS HAS TO GO AWAY
    use crate::impl_u::indexing;
    use builtin::*;
    use builtin_macros::*;
    use vstd::map::*;
    use vstd::modes::*;
    use vstd::prelude::*;
    use vstd::seq::*;
    use vstd::seq_lib::*;
    use vstd::set::*;
    use vstd::set_lib::*;
    use vstd::view::View;

    verus! {

macro_rules! bitmask_inc {
        ($low:expr,$high:expr) => {
            (!(!0u64 << (($high+1u64)-$low))) << $low
        }
    }

pub(crate) use bitmask_inc;

macro_rules! bit {
        ($v:expr) => {
            1u64 << $v
        }
    }

pub(crate) use bit;

pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

// The maximum physical address width is between 32 and 52 bits.
#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: u64 = unimplemented!();

#[verifier(external_body)]
pub proof fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;

// We cannot use a dual exec/spec constant for MAX_PHYADDR, because for those Verus currently
// doesn't support manually guiding the no-overflow proofs.
pub spec const MAX_PHYADDR_SPEC: u64 = ((1u64 << MAX_PHYADDR_WIDTH) - 1u64) as u64;

#[verifier::when_used_as_spec(MAX_PHYADDR_SPEC)]
pub exec const MAX_PHYADDR: u64
    ensures
        MAX_PHYADDR == MAX_PHYADDR_SPEC,
{
    axiom_max_phyaddr_width_facts();
    assert(1u64 << 32 == 0x100000000) by (compute);
    assert(forall|m: u64, n: u64| n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
    (1u64 << MAX_PHYADDR_WIDTH) - 1u64
}

pub const WORD_SIZE: usize = 8;

pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

pub spec const PT_BOUND_LOW: nat = 0;

// Upper bound for x86 4-level paging.
// 512 entries, each mapping 512*1024*1024*1024 bytes
pub const PT_BOUND_HIGH: usize = 512 * 512 * 1024 * 1024 * 1024;

pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends
        entry_size > 0,
{
    offset / entry_size
}

pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

pub open spec fn candidate_mapping_in_bounds(base: nat, pte: PageTableEntry) -> bool {
    base + pte.frame.size < x86_arch_spec.upper_vaddr(0, 0)
}

pub open spec fn candidate_mapping_overlaps_existing_vmem(
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry,
) -> bool {
    exists|b: nat|
        #![auto]
        {
            &&& mappings.dom().contains(b)
            &&& overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: b, size: mappings[b].frame.size },
            )
        }
}

pub open spec fn candidate_mapping_overlaps_existing_pmem(
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry,
) -> bool {
    exists|b: nat|
        #![auto]
        {
            &&& mappings.dom().contains(b)
            &&& overlap(pte.frame, mappings.index(b).frame)
        }
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
}

pub open spec fn new_seq<T>(i: nat, e: T) -> Seq<T>
    decreases i,
{
    if i == 0 {
        seq![]
    } else {
        new_seq((i - 1) as nat, e).push(e)
    }
}

#[is_variant]
pub enum MapResult {
    ErrOverlap,
    Ok,
}

#[is_variant]
pub enum UnmapResult {
    ErrNoSuchMapping,
    Ok,
}

#[is_variant]
pub enum ResolveResultExec {
    ErrUnmapped,
    Ok(usize, PageTableEntryExec),
}

impl ResolveResultExec {
    pub open spec fn view(self) -> ResolveResult {
        match self {
            ResolveResultExec::ErrUnmapped => ResolveResult::ErrUnmapped,
            ResolveResultExec::Ok(base, pte) => ResolveResult::Ok(base as nat, pte@),
        }
    }
}

#[is_variant]
pub enum ResolveResult {
    ErrUnmapped,
    Ok(nat, PageTableEntry),
}

#[is_variant]
pub enum LoadResult {
    Pagefault,
    Value(nat),  // word-sized load
}

#[is_variant]
pub enum StoreResult {
    Pagefault,
    Ok,
}

#[is_variant]
pub enum RWOp {
    Store { new_value: nat, result: StoreResult },
    Load { is_exec: bool, result: LoadResult },
}

pub struct MemRegion {
    pub base: nat,
    pub size: nat,
}

impl MemRegion {
    pub open spec fn contains(self, addr: nat) -> bool {
        between(addr, self.base, self.base + self.size)
    }
}

// only well-defined for sizes > 0
pub open spec(checked) fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region2.base < region1.base + region1.size
    } else {
        region1.base < region2.base + region2.size
    }
}

// hardens spec for overlap
#[verus::line_count::ignore]
proof fn overlap_sanity_check() {
    assert(overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 0, size: 4096 }));
    assert(overlap(MemRegion { base: 0, size: 8192 }, MemRegion { base: 0, size: 4096 }));
    assert(overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 0, size: 8192 }));
    assert(overlap(MemRegion { base: 0, size: 8192 }, MemRegion { base: 4096, size: 4096 }));
    assert(!overlap(MemRegion { base: 4096, size: 8192 }, MemRegion { base: 0, size: 4096 }));
    assert(!overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 8192, size: 16384 }));
}

pub struct MemRegionExec {
    pub base: usize,
    pub size: usize,
}

impl MemRegionExec {
    pub open spec fn view(self) -> MemRegion {
        MemRegion { base: self.base as nat, size: self.size as nat }
    }
}

pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

pub struct PageTableEntry {
    pub frame: MemRegion,
    /// The `flags` field on a `PageTableEntry` denotes the combined flags of the entire
    /// translation path to the entry. (See page table walk definition in hardware model,
    /// `spec_t::hardware`.) However, because we always set the flags on directories to be
    /// permissive these flags also correspond to the flags that we set for the frame mapping
    /// corresponding to this `PageTableEntry`.
    pub flags: Flags,
}

pub struct PageTableEntryExec {
    pub frame: MemRegionExec,
    pub flags: Flags,
}

impl PageTableEntryExec {
    pub open spec fn view(self) -> PageTableEntry {
        PageTableEntry { frame: self.frame@, flags: self.flags }
    }
}

pub ghost struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {
    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers.index(layer as int).entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers.index(layer as int).num_entries
    }

    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        self.entry_base(layer, base, self.num_entries(layer))
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= X86_NUM_LAYERS
        &&& forall|i: nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i) <= X86_MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= X86_NUM_ENTRIES
                &&& self.entry_size_is_next_layer_size(i)
            }
    }

    pub open spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends
            i < self.layers.len(),
    {
        i + 1 < self.layers.len() ==> self.entry_size(i) == self.entry_size((i + 1) as nat)
            * self.num_entries((i + 1) as nat)
    }

    pub open spec(checked) fn contains_entry_size_at_index_atleast(
        &self,
        entry_size: nat,
        min_idx: nat,
    ) -> bool {
        exists|i: nat|
            min_idx <= i && i < self.layers.len() && #[trigger] self.entry_size(i) == entry_size
    }

    pub open spec(checked) fn contains_entry_size(&self, entry_size: nat) -> bool {
        self.contains_entry_size_at_index_atleast(entry_size, 0)
    }

    #[verifier(inline)]
    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
        index_from_base_and_addr(base, vaddr, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + idx * self.entry_size(layer)
        entry_base_from_index(base, idx, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + (idx + 1) * self.entry_size(layer)
        next_entry_base_from_index(base, idx, self.entry_size(layer))
    }
}

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

pub struct ArchExec {
    // TODO: This could probably be an array, once we have support for that
    pub layers: Vec<ArchLayerExec>,
}

// Why does this exec_spec function even exist:
// - In some places we need to refer to the `Exec` versions of the structs in spec mode.
// - We can't make x86_arch_exec a const because Verus panics if we initialize the vec directly,
//   i.e. we need to push to a mut vec instead. (Does rust even support vecs in a const? Otherwise
//   would need arrays.)
// - Since x86_arch_exec is a function it has to have a mode, i.e. we need a version for exec usage
//   and a version for spec usage. In the spec version we can't initialize the vec (same problem as
//   above and can't use mut), i.e. we have to axiomatize their equivalence.
// - We can't even have a proof function axiom because we need to show
//   `x86_arch_exec_spec() == x86_arch_exec()`, where the second function call is an exec function.
//   Thus the axiom is an assumed postcondition on the exec function itself.
// - In addition to adding the postcondition, we also need a separate axiom to show that the view
//   of x86_arch_exec_spec is the same as x86_arch_spec. This is provable but only with the
//   postconditions on x86_arch_exec, which is an exec function. Consequently we can't use that
//   postcondition in proof mode.
// - All this mess should go away as soon as we can make that exec function the constant it ought
//   to be.
pub open spec fn x86_arch_exec_spec() -> ArchExec;

#[verifier(external_body)]
pub proof fn axiom_x86_arch_exec_spec()
    ensures
        x86_arch_exec_spec()@ == x86_arch_spec,
;

pub exec fn x86_arch_exec() -> (res: ArchExec)
    ensures
        res.layers@
            == seq![
                ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 },
                ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 },
                ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 },
                ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 },
            ],
        res@ === x86_arch_spec,
        res === x86_arch_exec_spec(),
{
    // Can we somehow just initialize an immutable vec directly? Verus panics when I try do so
    // (unless the function is external_body).
    let mut v = Vec::new();
    v.push(ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 });
    let res = ArchExec { layers: v };
    proof {
        assert_seqs_equal!(res@.layers, x86_arch_spec.layers);
        // This is an axiom to establish the equivalence with x86_arch_exec_spec; See comments
        // further up for explanation why this workaround is necessary.
        assume(res === x86_arch_exec_spec());
    }
    res
}

pub spec const x86_arch_spec: Arch = Arch {
    layers:
        seq![
            ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
            ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
            ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
            ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
        ],
};

} // verus!
}

pub mod definitions_u {
    #![allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;
    use vstd::map::*;
    use vstd::modes::*;
    use vstd::prelude::*;
    use vstd::seq::*;
    use vstd::seq_lib::*;
    use vstd::set::*;
    use vstd::set_lib::*;
    use vstd::view::View;

    use crate::definitions_t::{
        aligned, axiom_max_phyaddr_width_facts, new_seq, ArchExec, ArchLayerExec, Flags,
        MAX_PHYADDR,
    };

    verus! {

pub proof fn lemma_maxphyaddr_facts()
    ensures
        0xFFFFFFFF <= MAX_PHYADDR <= 0xFFFFFFFFFFFFF,
{
    axiom_max_phyaddr_width_facts();
    assert(1u64 << 32 == 0x100000000) by (compute);
    assert(1u64 << 52 == 0x10000000000000) by (compute);
    assert(forall|m: u64, n: u64| n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
}

pub proof fn lemma_new_seq<T>(i: nat, e: T)
    ensures
        new_seq(i, e).len() == i,
        forall|j: nat| j < i ==> new_seq(i, e).index(j as int) === e,
    decreases i,
{
    if i == 0 {
    } else {
        lemma_new_seq::<T>((i - 1) as nat, e);
    }
}

pub exec fn aligned_exec(addr: usize, size: usize) -> (res: bool)
    requires
        size > 0,
    ensures
        res == aligned(addr as nat, size as nat),
{
    addr % size == 0
}

/// We always set permissive flags on directories. Restrictions happen on the frame mapping.
pub spec const permissive_flags: Flags = Flags {
    is_writable: true,
    is_supervisor: false,
    disable_execute: false,
};

// Sometimes z3 needs these concrete bounds to prove the no-overflow VC
pub proof fn overflow_bounds()
    ensures
        X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
        MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
{
    assert(X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
    assert(MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000)
        by (nonlinear_arith);
}

// Architecture
// page_size, next_sizes
// 2**40    , [ 2 ** 30, 2 ** 20 ]
// 2**30    , [ 2 ** 20 ]
// 2**20    , [ ]
// [es0 # es1 , es2 , es3 ] // entry_size
// [1T  # 1G  , 1M  , 1K  ] // pages mapped at this level are this size <--
// [n0  # n1  , n2  , n3  ] // number_of_entries
// [1   # 1024, 1024, 1024]
// es1 == es0 / n1 -- n1 * es1 == es0
// es2 == es1 / n2 -- n2 * es2 == es1
// es3 == es2 / n3 -- n3 * es3 == es2
// [es0  #  es1 , es2 , es3 , es4 ] // entry_size
// [256T #  512G, 1G  , 2M  , 4K  ]
// [n0   #  n1  , n2  , n3  , n4  ] // number_of_entries
// [     #  512 , 512 , 512 , 512 ]
// [     #  9   , 9   , 9   , 9   , 12  ]
use crate::definitions_t::{
    Arch,
    ArchLayer,
    MAX_BASE,
    X86_MAX_ENTRY_SIZE,
    X86_NUM_ENTRIES,
    x86_arch_spec,
    X86_NUM_LAYERS,
};

impl Clone for ArchLayerExec {
    fn clone(&self) -> Self {
        ArchLayerExec { entry_size: self.entry_size, num_entries: self.num_entries }
    }
}

impl ArchLayerExec {
    pub open spec fn view(self) -> ArchLayer {
        ArchLayer { entry_size: self.entry_size as nat, num_entries: self.num_entries as nat }
    }
}

impl ArchExec {
    pub open spec fn view(self) -> Arch {
        Arch { layers: self.layers@.map(|i: int, l: ArchLayerExec| l@) }
    }

    pub fn entry_size(&self, layer: usize) -> (res: usize)
        requires
            layer < self@.layers.len(),
        ensures
            res == self@.entry_size(layer as nat),
    {
        self.layers[layer].entry_size
    }

    pub fn num_entries(&self, layer: usize) -> (res: usize)
        requires
            layer < self@.layers.len(),
        ensures
            res == self@.num_entries(layer as nat),
    {
        self.layers[layer].num_entries
    }

    pub fn index_for_vaddr(&self, layer: usize, base: usize, vaddr: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            vaddr >= base,
        ensures
            res == self@.index_for_vaddr(layer as nat, base as nat, vaddr as nat),
            res == crate::definitions_t::index_from_base_and_addr(
                base as nat,
                vaddr as nat,
                self@.entry_size(layer as nat),
            ),
    {
        let es = self.entry_size(layer);
        let offset = vaddr - base;
        let res = offset / es;
        assert(res as nat == offset as nat / es as nat) by (nonlinear_arith)
            requires
                res == offset / es,
                0 < es as int,
        {};
        res
    }

    #[verifier(nonlinear)]
    pub fn entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= X86_NUM_ENTRIES,
        ensures
            res == self@.entry_base(layer as nat, base as nat, idx as nat),
    {
        proof {
            // FIXME: Weird error message when using the spec const here
            // lib::mult_leq_mono_both(idx as nat, self@.entry_size(layer as nat), X86_NUM_ENTRIES as nat, X86_MAX_ENTRY_SIZE);
            crate::extra::mult_leq_mono_both(
                idx as nat,
                self@.entry_size(layer as nat),
                X86_NUM_ENTRIES as nat,
                512 * 1024 * 1024 * 1024,
            );
        }
        base + idx * self.entry_size(layer)
    }

    pub fn next_entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= X86_NUM_ENTRIES,
        ensures
            res == self@.next_entry_base(layer as nat, base as nat, idx as nat),
    {
        proof {
            overflow_bounds();
            let es = self@.entry_size(layer as nat);
            assert(0 <= (idx + 1) * es <= X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1))
                by (nonlinear_arith)
                requires
                    es <= X86_MAX_ENTRY_SIZE,
                    idx <= X86_NUM_ENTRIES,
            {  /* New instability with z3 4.10.1 */
            };
        }
        let offset = (idx + 1) * self.entry_size(layer);
        proof {
            assert(base + offset <= MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1))
                by (nonlinear_arith)
                requires
                    0 <= offset <= X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1),
                    0 <= base <= MAX_BASE,
            {};
        }
        base + offset
    }
}

impl Arch {
    pub proof fn lemma_entry_sizes_aligned(self, i: nat, j: nat)
        requires
            self.inv(),
            i <= j,
            j < self.layers.len(),
        ensures
            aligned(self.entry_size(i), self.entry_size(j)),
        decreases self.layers.len() - i,
    {
        if i == j {
            assert(aligned(self.entry_size(i), self.entry_size(j))) by (nonlinear_arith)
                requires
                    i == j,
                    self.entry_size(i) > 0,
            {};
        } else {
            assert(forall|a: int, b: int| #[trigger] (a * b) == b * a);
            self.lemma_entry_sizes_aligned(i + 1, j);
            crate::extra::mod_of_mul_auto();
            crate::extra::aligned_transitive_auto();
            assert(aligned(self.entry_size(i), self.entry_size(j)));
        }
    }

    pub proof fn lemma_entry_sizes_aligned_auto(self)
        ensures
            forall|i: nat, j: nat|
                self.inv() && i <= j && j < self.layers.len() ==> aligned(
                    self.entry_size(i),
                    self.entry_size(j),
                ),
    {
        assert_forall_by(
            |i: nat, j: nat|
                {
                    requires(self.inv() && i <= j && j < self.layers.len());
                    ensures(aligned(self.entry_size(i), self.entry_size(j)));
                    self.lemma_entry_sizes_aligned(i, j);
                },
        );
    }

    pub proof fn lemma_entry_sizes_increase(self, i: nat, j: nat)
        requires
            self.inv(),
            i < j,
            j < self.layers.len(),
        ensures
            self.entry_size(i) >= self.entry_size(j),
        decreases j - i,
    {
        assert(self.entry_size(i) >= self.entry_size(i + 1)) by (nonlinear_arith)
            requires
                i + 1 < self.layers.len(),
                self.entry_size_is_next_layer_size(i),
                self.num_entries(i + 1) > 0,
        {};
        if j == i + 1 {
        } else {
            self.lemma_entry_sizes_increase(i + 1, j);
        }
    }
}

#[verifier(nonlinear)]
pub proof fn x86_arch_inv()
    ensures
        x86_arch_spec.inv(),
{
    assert(x86_arch_spec.entry_size(3) == 4096);
    assert(x86_arch_spec.contains_entry_size(4096));
    assert(x86_arch_spec.layers.len() <= X86_NUM_LAYERS);
    assert forall|i: nat| i < x86_arch_spec.layers.len() implies {
        &&& 0 < #[trigger] x86_arch_spec.entry_size(i) <= X86_MAX_ENTRY_SIZE
        &&& 0 < #[trigger] x86_arch_spec.num_entries(i) <= X86_NUM_ENTRIES
        &&& x86_arch_spec.entry_size_is_next_layer_size(i)
    } by {
        assert(0 < #[trigger] x86_arch_spec.entry_size(i) <= X86_MAX_ENTRY_SIZE);
        assert(0 < #[trigger] x86_arch_spec.num_entries(i) <= X86_NUM_ENTRIES);
        assert(x86_arch_spec.entry_size_is_next_layer_size(i));
    }
    assert(x86_arch_spec.inv());
}

} // verus!
}

pub mod spec_t {
    pub mod hlspec {
        #![allow(unused_imports)]
        #![verus::trusted]
        // trusted:
        // this is the process-level specification of the kernel's behaviour

        use crate::definitions_t::{
            aligned, between, candidate_mapping_in_bounds,
            candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem,
            overlap, Flags, LoadResult, MapResult, MemRegion, PageTableEntry, RWOp, ResolveResult,
            StoreResult, UnmapResult,
        };
        use crate::definitions_t::{
            L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, PAGE_SIZE, PT_BOUND_HIGH, PT_BOUND_LOW,
            WORD_SIZE,
        };
        use crate::spec_t::mem::word_index_spec;
        use crate::*;
        use builtin::*;
        use builtin_macros::*;
        use state_machines_macros::*;
        use vstd::map::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::set::*;

        // TODO:
        // - should Unmap be able to unmap when is_supervisor is set?

        verus! {

pub struct AbstractConstants {
    pub phys_mem_size: nat,
}

pub struct AbstractVariables {
    /// Word-indexed virtual memory
    pub mem: Map<nat, nat>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat, PageTableEntry>,
}

pub enum AbstractStep {
    ReadWrite { vaddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    Map { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap { vaddr: nat, result: UnmapResult },
    Resolve { vaddr: nat, result: ResolveResult },
    Stutter,
}

pub open spec fn init(s: AbstractVariables) -> bool {
    &&& s.mem === Map::empty()
    &&& s.mappings === Map::empty()
}

pub open spec fn mem_domain_from_mappings_contains(
    phys_mem_size: nat,
    word_idx: nat,
    mappings: Map<nat, PageTableEntry>,
) -> bool {
    let vaddr = word_idx * WORD_SIZE as nat;
    exists|base: nat, pte: PageTableEntry|
        {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            &&& #[trigger] mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& pmem_idx < phys_mem_size
        }
}

pub open spec fn mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub proof fn lemma_mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry,
)
    requires
        !mappings.dom().contains(base),
    ensures
        (forall|word_idx: nat|
            mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                ==> #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            )),
        (forall|word_idx: nat|
            !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                && #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            ) ==> between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size)),
{
    assert forall|word_idx: nat|
        mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings,
        ) implies #[trigger] mem_domain_from_mappings_contains(
        phys_mem_size,
        word_idx,
        mappings.insert(base, pte),
    ) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base: nat, pte: PageTableEntry|
            {
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                &&& #[trigger] mappings.contains_pair(base, pte)
                &&& between(vaddr, base, base + pte.frame.size)
                &&& pmem_idx < phys_mem_size
            };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
    };
    assert forall|word_idx: nat|
        !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
            && #[trigger] mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings.insert(base, pte),
        ) implies between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base2: nat, pte2: PageTableEntry|
            {
                let paddr = (pte2.frame.base + (vaddr - base2)) as nat;
                let pmem_idx = word_index_spec(paddr);
                &&& #[trigger] mappings.insert(base, pte).contains_pair(base2, pte2)
                &&& between(vaddr, base2, base2 + pte2.frame.size)
                &&& pmem_idx < phys_mem_size
            };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
        assert(between(vaddr, base2, base2 + pte2.frame.size));
        if !between(vaddr, base, base + pte.frame.size) {
            assert(base2 != base || pte2 !== pte);
            if base2 != base {
                assert(mappings.contains_pair(base2, pte2));
                assert(mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings));
            }
            assert(false);
        } else {
        }
    };
}

pub open spec fn step_ReadWrite(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    vaddr: nat,
    op: RWOp,
    pte: Option<(nat, PageTableEntry)>,
) -> bool {
    let vmem_idx = word_index_spec(vaddr);
    &&& aligned(vaddr, 8)
    &&& s2.mappings === s1.mappings
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(
                vaddr,
                base,
                base + pte.frame.size,
            )
            // .. and the result depends on the flags.

            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result.is_Ok()
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec
                        ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem.index(vmem_idx)
                    } else {
                        &&& result.is_Pagefault()
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(
                vmem_idx,
            )
            // .. and the result is always a pagefault and an unchanged memory.

            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result.is_Pagefault(),
                RWOp::Load { is_exec, result } => result.is_Pagefault(),
            }
        },
    }
}

pub open spec fn step_Map_enabled(
    map: Map<nat, PageTableEntry>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(map, vaddr, pte)
}

pub open spec fn step_Map(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    vaddr: nat,
    pte: PageTableEntry,
    result: MapResult,
) -> bool {
    &&& step_Map_enabled(s1.mappings, vaddr, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    } else {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.insert(vaddr, pte)
        &&& (forall|idx: nat| #![auto] s1.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH as nat)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    vaddr: nat,
    result: UnmapResult,
) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& if s1.mappings.dom().contains(vaddr) {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.remove(vaddr)
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
        &&& (forall|idx: nat| #![auto] s2.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
}

pub open spec fn step_Resolve(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    vaddr: nat,
    result: ResolveResult,
) -> bool {
    &&& step_Resolve_enabled(vaddr)
    &&& s2 === s1
    &&& match result {
        ResolveResult::Ok(base, pte) => {
            // If result is Ok, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
        },
        ResolveResult::ErrUnmapped => {
            let vmem_idx = word_index_spec(vaddr);
            // If result is ErrUnmapped, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
        },
    }
}

pub open spec fn step_Stutter(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
) -> bool {
    s1 === s2
}

pub open spec fn next_step(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    step: AbstractStep,
) -> bool {
    match step {
        AbstractStep::ReadWrite { vaddr, op, pte } => step_ReadWrite(c, s1, s2, vaddr, op, pte),
        AbstractStep::Map { vaddr, pte, result } => step_Map(c, s1, s2, vaddr, pte, result),
        AbstractStep::Unmap { vaddr, result } => step_Unmap(c, s1, s2, vaddr, result),
        AbstractStep::Resolve { vaddr, result } => step_Resolve(c, s1, s2, vaddr, result),
        AbstractStep::Stutter => step_Stutter(c, s1, s2),
    }
}

pub open spec fn next(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(c, s1, s2, step)
}

} // verus!
}

    pub mod hardware {
        #![allow(unused_imports)]
        #![verus::trusted]
        // trusted:
        // this defines the page table structure as interpreted by the hardware
        // and the hardware state machine

        use crate::definitions_t::{
            aligned, between, x86_arch_spec, Flags, LoadResult, MemRegion, PageTableEntry, RWOp,
            StoreResult,
        };
        use crate::definitions_t::{
            axiom_max_phyaddr_width_facts, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
            L3_ENTRY_SIZE, MAX_BASE, MAX_PHYADDR, MAX_PHYADDR_WIDTH, PAGE_SIZE, WORD_SIZE,
            X86_NUM_ENTRIES, X86_NUM_LAYERS,
        };
        use crate::definitions_t::{bit, bitmask_inc};
        use crate::impl_u::l0;
        use crate::impl_u::l1;
        use crate::impl_u::l2_impl;
        use crate::spec_t::mem;
        use crate::spec_t::mem::word_index_spec;
        use builtin::*;
        use builtin_macros::*;
        use state_machines_macros::*;
        use vstd::assert_by_contradiction;
        use vstd::map::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::set::*;

        verus! {

pub struct HWVariables {
    /// Word-indexed physical memory
    pub mem: Seq<nat>,
    pub pt_mem: mem::PageTableMemory,
    pub tlb: Map<nat, PageTableEntry>,
}

#[is_variant]
pub enum HWStep {
    ReadWrite { vaddr: nat, paddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    PTMemOp,
    TLBFill { vaddr: nat, pte: PageTableEntry },
    TLBEvict { vaddr: nat },
}

#[is_variant]
pub ghost enum GhostPageDirectoryEntry {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// Dirty; indicates whether software has written to the page referenced by this entry
        flag_D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // flag_PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        flag_G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        flag_PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    /// An `Empty` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
    Empty,
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table
// MASK_FLAG_* are flags valid for entries at all levels.
pub const MASK_FLAG_P: u64 = bit!(0u64);

pub const MASK_FLAG_RW: u64 = bit!(1u64);

pub const MASK_FLAG_US: u64 = bit!(2u64);

pub const MASK_FLAG_PWT: u64 = bit!(3u64);

pub const MASK_FLAG_PCD: u64 = bit!(4u64);

pub const MASK_FLAG_A: u64 = bit!(5u64);

pub const MASK_FLAG_XD: u64 = bit!(63u64);

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
pub const MASK_PG_FLAG_D: u64 = bit!(6u64);

pub const MASK_PG_FLAG_G: u64 = bit!(8u64);

pub const MASK_PG_FLAG_PAT: u64 = bit!(12u64);

pub const MASK_L1_PG_FLAG_PS: u64 = bit!(7u64);

pub const MASK_L2_PG_FLAG_PS: u64 = bit!(7u64);

pub const MASK_L3_PG_FLAG_PAT: u64 = bit!(7u64);

// const MASK_DIR_REFC:           u64 = bitmask_inc!(52u64,62u64); // Ignored bits for storing refcount in L3 and L2
// const MASK_DIR_L1_REFC:        u64 = bitmask_inc!(8u64,12u64); // Ignored bits for storing refcount in L1
// const MASK_DIR_REFC_SHIFT:     u64 = 52u64;
// const MASK_DIR_L1_REFC_SHIFT:  u64 = 8u64;
// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: u64
    ensures
        MASK_ADDR == MASK_ADDR_SPEC,
{
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: u64 = bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: u64
    ensures
        MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC,
{
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L2_PG_ADDR_SPEC: u64 = bitmask_inc!(21u64, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: u64
    ensures
        MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC,
{
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(21u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L3_PG_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: u64
    ensures
        MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC,
{
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_DIR_ADDR_SPEC: u64 = MASK_ADDR;

#[verifier::when_used_as_spec(MASK_DIR_ADDR_SPEC)]
pub exec const MASK_DIR_ADDR: u64
    ensures
        MASK_DIR_ADDR == MASK_DIR_ADDR_SPEC,
{
    MASK_ADDR
}

#[allow(repr_transparent_external_private_fields)]
// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PageDirectoryEntry {
    pub entry: u64,
    pub layer: Ghost<nat>,
}

// This impl defines everything necessary for the page table walk semantics.
// PageDirectoryEntry is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
impl PageDirectoryEntry {
    pub open spec fn view(self) -> GhostPageDirectoryEntry {
        let v = self.entry;
        let flag_P = v & MASK_FLAG_P == MASK_FLAG_P;
        let flag_RW = v & MASK_FLAG_RW == MASK_FLAG_RW;
        let flag_US = v & MASK_FLAG_US == MASK_FLAG_US;
        let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
        let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
        let flag_A = v & MASK_FLAG_A == MASK_FLAG_A;
        let flag_XD = v & MASK_FLAG_XD == MASK_FLAG_XD;
        let flag_D = v & MASK_PG_FLAG_D == MASK_PG_FLAG_D;
        let flag_G = v & MASK_PG_FLAG_G == MASK_PG_FLAG_G;
        if self.layer@ <= 3 {
            if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
                if self.layer == 0 {
                    let addr = (v & MASK_ADDR) as usize;
                    GhostPageDirectoryEntry::Directory {
                        addr,
                        flag_P,
                        flag_RW,
                        flag_US,
                        flag_PWT,
                        flag_PCD,
                        flag_A,
                        flag_XD,
                    }
                } else if self.layer == 1 {
                    if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                        // super page mapping
                        let addr = (v & MASK_L1_PG_ADDR) as usize;
                        let flag_PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                        GhostPageDirectoryEntry::Page {
                            addr,
                            flag_P,
                            flag_RW,
                            flag_US,
                            flag_PWT,
                            flag_PCD,
                            flag_A,
                            flag_D,
                            flag_G,
                            flag_PAT,
                            flag_XD,
                        }
                    } else {
                        let addr = (v & MASK_ADDR) as usize;
                        GhostPageDirectoryEntry::Directory {
                            addr,
                            flag_P,
                            flag_RW,
                            flag_US,
                            flag_PWT,
                            flag_PCD,
                            flag_A,
                            flag_XD,
                        }
                    }
                } else if self.layer == 2 {
                    if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                        // huge page mapping
                        let addr = (v & MASK_L2_PG_ADDR) as usize;
                        let flag_PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                        GhostPageDirectoryEntry::Page {
                            addr,
                            flag_P,
                            flag_RW,
                            flag_US,
                            flag_PWT,
                            flag_PCD,
                            flag_A,
                            flag_D,
                            flag_G,
                            flag_PAT,
                            flag_XD,
                        }
                    } else {
                        let addr = (v & MASK_ADDR) as usize;
                        GhostPageDirectoryEntry::Directory {
                            addr,
                            flag_P,
                            flag_RW,
                            flag_US,
                            flag_PWT,
                            flag_PCD,
                            flag_A,
                            flag_XD,
                        }
                    }
                } else {
                    // TODO: uncomment when we have inline proofs
                    // assert(self.layer == 3);
                    let addr = (v & MASK_L3_PG_ADDR) as usize;
                    let flag_PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                    GhostPageDirectoryEntry::Page {
                        addr,
                        flag_P,
                        flag_RW,
                        flag_US,
                        flag_PWT,
                        flag_PCD,
                        flag_A,
                        flag_D,
                        flag_G,
                        flag_PAT,
                        flag_XD,
                    }
                }
            } else {
                GhostPageDirectoryEntry::Empty
            }
        } else {
            arbitrary()
        }
    }

    /// Returns `true` iff all must-be-zero bits for a given entry are zero.
    #[verifier::opaque]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool
        recommends
            self.layer@ <= 3,
    {
        if self.entry & MASK_FLAG_P == MASK_FLAG_P {
            if self.layer == 0 {  // PML4, always directory
                // 51:M, 7
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                &&& self.entry & bit!(7u64) == 0
            } else if self.layer == 1 {  // PDPT
                if self.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // 51:M, 29:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bitmask_inc!(13u64,29u64) == 0
                } else {
                    // 51:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bit!(7u64) == 0
                }
            } else if self.layer == 2 {  // PD
                if self.entry & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // 62:M, 20:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bitmask_inc!(13u64,20u64) == 0
                } else {
                    // 62:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bit!(7u64) == 0
                }
            } else if self.layer == 3 {  // PT, always frame
                // 62:M
                self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
            } else {
                arbitrary()
            }
        } else {
            // No bits are reserved for unused entries
            true
        }
    }

    pub open spec fn layer(self) -> nat {
        self.layer@
    }
}

#[allow(unused_macros)]
        macro_rules! l0_bits {
            ($addr:expr) => { ($addr & bitmask_inc!(39u64,47u64)) >> 39u64 }
        }

pub(crate) use l0_bits;

#[allow(unused_macros)]
        macro_rules! l1_bits {
            ($addr:expr) => { ($addr & bitmask_inc!(30u64,38u64)) >> 30u64 }
        }

pub(crate) use l1_bits;

#[allow(unused_macros)]
        macro_rules! l2_bits {
            ($addr:expr) => { ($addr & bitmask_inc!(21u64,29u64)) >> 21u64 }
        }

pub(crate) use l2_bits;

#[allow(unused_macros)]
        macro_rules! l3_bits {
            ($addr:expr) => { ($addr & bitmask_inc!(12u64,20u64)) >> 12u64 }
        }

pub(crate) use l3_bits;

pub open spec fn read_entry(
    pt_mem: mem::PageTableMemory,
    dir_addr: nat,
    layer: nat,
    idx: nat,
) -> GhostPageDirectoryEntry {
    let region = MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat };
    PageDirectoryEntry { entry: pt_mem.spec_read(idx, region), layer: Ghost(layer) }@
}

/// TODO: list 4-level paging no HLAT etc. as assumptions (+ the register to enable XD semantics,
/// it's mb0 otherwise)
///
/// The intended semantics for valid_pt_walk is this:
/// Given a `PageTableMemory` `pt_mem`, the predicate is true for those `addr` and `pte` where the
/// MMU's page table walk arrives at an entry mapping the frame `pte.frame`. The properties in
/// `pte.flags` reflect the properties along the translation path. I.e. `pte.flags.is_writable` is
/// true iff the RW flag is set in all directories along the translation path and in the frame
/// mapping. Similarly, `pte.flags.is_supervisor` is true iff the US flag is unset in all those
/// structures and `pte.flags.disable_execute` is true iff the XD flag is set in at least one of
/// those structures.
///
/// In practice, we always set these flags to their more permissive state in directories and only
/// make more restrictive settings in the frame mappings. (Ensured in the invariant, see conjunct
/// `directories_have_flags` in refinement layers 1 and 2.) But in the hardware model we still
/// define the full, correct semantics to ensure the implementation sets the flags correctly.
pub open spec fn valid_pt_walk(
    pt_mem: mem::PageTableMemory,
    addr: u64,
    pte: PageTableEntry,
) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    let l3_idx: nat = l3_bits!(addr) as nat;
    match read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        GhostPageDirectoryEntry::Directory {
            addr: dir_addr,
            flag_RW: l0_RW,
            flag_US: l0_US,
            flag_XD: l0_XD,
            ..
        } => {
            match read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
                GhostPageDirectoryEntry::Page {
                    addr: page_addr,
                    flag_RW: l1_RW,
                    flag_US: l1_US,
                    flag_XD: l1_XD,
                    ..
                } => {
                    aligned(addr as nat, L1_ENTRY_SIZE as nat) && pte == PageTableEntry {
                        frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                        flags: Flags {
                            is_writable: l0_RW && l1_RW,
                            is_supervisor: !l0_US || !l1_US,
                            disable_execute: l0_XD || l1_XD,
                        },
                    }
                },
                GhostPageDirectoryEntry::Directory {
                    addr: dir_addr,
                    flag_RW: l1_RW,
                    flag_US: l1_US,
                    flag_XD: l1_XD,
                    ..
                } => {
                    match read_entry(pt_mem, dir_addr as nat, 2, l2_idx) {
                        GhostPageDirectoryEntry::Page {
                            addr: page_addr,
                            flag_RW: l2_RW,
                            flag_US: l2_US,
                            flag_XD: l2_XD,
                            ..
                        } => {
                            aligned(addr as nat, L2_ENTRY_SIZE as nat) && pte == PageTableEntry {
                                frame: MemRegion {
                                    base: page_addr as nat,
                                    size: L2_ENTRY_SIZE as nat,
                                },
                                flags: Flags {
                                    is_writable: l0_RW && l1_RW && l2_RW,
                                    is_supervisor: !l0_US || !l1_US || !l2_US,
                                    disable_execute: l0_XD || l1_XD || l2_XD,
                                },
                            }
                        },
                        GhostPageDirectoryEntry::Directory {
                            addr: dir_addr,
                            flag_RW: l2_RW,
                            flag_US: l2_US,
                            flag_XD: l2_XD,
                            ..
                        } => {
                            match read_entry(pt_mem, dir_addr as nat, 3, l3_idx) {
                                GhostPageDirectoryEntry::Page {
                                    addr: page_addr,
                                    flag_RW: l3_RW,
                                    flag_US: l3_US,
                                    flag_XD: l3_XD,
                                    ..
                                } => {
                                    aligned(addr as nat, L3_ENTRY_SIZE as nat) && pte
                                        == PageTableEntry {
                                        frame: MemRegion {
                                            base: page_addr as nat,
                                            size: L3_ENTRY_SIZE as nat,
                                        },
                                        flags: Flags {
                                            is_writable: l0_RW && l1_RW && l2_RW && l3_RW,
                                            is_supervisor: !l0_US || !l1_US || !l2_US || !l3_US,
                                            disable_execute: l0_XD || l1_XD || l2_XD || l3_XD,
                                        },
                                    }
                                },
                                GhostPageDirectoryEntry::Directory { .. } => false,
                                GhostPageDirectoryEntry::Empty => false,
                            }
                        },
                        GhostPageDirectoryEntry::Empty => false,
                    }
                },
                GhostPageDirectoryEntry::Empty => false,
            }
        },
        _ => false,
    }
}

// Can't use `n as u64` in triggers because it's an arithmetic expression
pub open spec fn nat_to_u64(n: nat) -> u64
    recommends
        n <= u64::MAX,
{
    n as u64
}

/// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry> {
    Map::new(
        |addr: nat|
            addr
                < MAX_BASE
            // Casting addr to u64 is okay since addr < MAX_BASE < u64::MAX
             && exists|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte),
        |addr: nat| choose|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte),
    )
}

pub open spec fn init(s: HWVariables) -> bool {
    &&& s.tlb.dom() === Set::empty()
    &&& interp_pt_mem(s.pt_mem) === Map::empty()
}

// We only allow aligned accesses. Can think of unaligned accesses as two aligned accesses. When we
// get to concurrency we may have to change that.
pub open spec fn step_ReadWrite(
    s1: HWVariables,
    s2: HWVariables,
    vaddr: nat,
    paddr: nat,
    op: RWOp,
    pte: Option<(nat, PageTableEntry)>,
) -> bool {
    &&& aligned(vaddr, 8)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.tlb === s1.tlb
    &&& match pte {
        Some((base, pte)) => {
            let pmem_idx = word_index_spec(paddr);
            // If pte is Some, it's a cached mapping that maps vaddr to paddr..
            &&& s1.tlb.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& paddr === (pte.frame.base + (vaddr
                - base)) as nat
            // .. and the result depends on the flags.

            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result.is_Ok()
                        &&& s2.mem === s1.mem.update(pmem_idx as int, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && (is_exec
                        ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem[pmem_idx as int]
                    } else {
                        &&& result.is_Pagefault()
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& (!exists|base, pte|
                {
                    &&& interp_pt_mem(s1.pt_mem).contains_pair(base, pte)
                    &&& between(vaddr, base, base + pte.frame.size)
                })
            // .. and the result is always a pagefault and an unchanged memory.

            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result.is_Pagefault(),
                RWOp::Load { is_exec, result } => result.is_Pagefault(),
            }
        },
    }
}

pub open spec fn step_PTMemOp(s1: HWVariables, s2: HWVariables) -> bool {
    &&& s2.mem === s1.mem
    // s2.tlb is a submap of s1.tlb

    &&& forall|base: nat, pte: PageTableEntry|
        s2.tlb.contains_pair(base, pte) ==> s1.tlb.contains_pair(
            base,
            pte,
        )
    // pt_mem may change arbitrarily

}

pub open spec fn step_TLBFill(
    s1: HWVariables,
    s2: HWVariables,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& interp_pt_mem(s1.pt_mem).contains_pair(vaddr, pte)
    &&& s2.tlb === s1.tlb.insert(vaddr, pte)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn step_TLBEvict(s1: HWVariables, s2: HWVariables, vaddr: nat) -> bool {
    &&& s1.tlb.dom().contains(vaddr)
    &&& s2.tlb === s1.tlb.remove(vaddr)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn next_step(s1: HWVariables, s2: HWVariables, step: HWStep) -> bool {
    match step {
        HWStep::ReadWrite { vaddr, paddr, op, pte } => step_ReadWrite(
            s1,
            s2,
            vaddr,
            paddr,
            op,
            pte,
        ),
        HWStep::PTMemOp => step_PTMemOp(s1, s2),
        HWStep::TLBFill { vaddr, pte } => step_TLBFill(s1, s2, vaddr, pte),
        HWStep::TLBEvict { vaddr } => step_TLBEvict(s1, s2, vaddr),
    }
}

pub open spec fn next(s1: HWVariables, s2: HWVariables) -> bool {
    exists|step: HWStep| next_step(s1, s2, step)
}

// pub closed spec fn inv(s: HWVariables) -> bool {
//     true
// }
//
// proof fn init_implies_inv(s: HWVariables)
//     requires
//         init(s),
//     ensures
//         inv(s)
// { }
//
// proof fn next_preserves_inv(s1: HWVariables, s2: HWVariables)
//     requires
//         next(s1, s2),
//         inv(s1),
//     ensures
//         inv(s2),
// {
//     let step = choose|step: HWStep| next_step(s1, s2, step);
//     match step {
//         HWStep::ReadWrite { vaddr, paddr, op , pte} => (),
//         HWStep::PTMemOp                             => (),
//         HWStep::TLBFill  { vaddr, pte }             => (),
//         HWStep::TLBEvict { vaddr }                  => (),
//     }
// }

} // verus!
}

    pub mod os {
        #![allow(unused_imports)]
        #![verus::trusted]
        // trusted:
        // describes how the whole system behaves
        //
        // this refers to definitions in an untrusted file, but uses them in a way that the
        // state-machine refinement can check

        use builtin::*;
        use builtin_macros::*;
        use map::*;
        use seq::*;
        use set_lib::*;
        use vstd::prelude::*;
        use vstd::*;

        use crate::definitions_t::{
            aligned, between, candidate_mapping_overlaps_existing_pmem,
            candidate_mapping_overlaps_existing_vmem, new_seq, overlap, Arch, MapResult, MemRegion,
            PageTableEntry, RWOp, ResolveResult, UnmapResult,
        };
        use crate::definitions_t::{
            L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, PAGE_SIZE, PT_BOUND_HIGH, PT_BOUND_LOW,
            WORD_SIZE,
        };
        use crate::impl_u::spec_pt;
        use crate::spec_t::mem::word_index_spec;
        use crate::spec_t::{hardware, hlspec};

        verus! {

pub struct OSVariables {
    pub hw: hardware::HWVariables,
}

impl OSVariables {
    pub open spec fn pt_mappings_dont_overlap_in_vmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(
                b2,
                pte2,
            ) ==> ((b1 == b2) || !overlap(
                MemRegion { base: b1, size: pte1.frame.size },
                MemRegion { base: b2, size: pte2.frame.size },
            ))
    }

    pub open spec fn pt_mappings_dont_overlap_in_pmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(
                b2,
                pte2,
            ) ==> ((b1 == b2) || !overlap(pte1.frame, pte2.frame))
    }

    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, pte|
            self.hw.tlb.contains_pair(base, pte) ==> #[trigger] self.interp_pt_mem().contains_pair(
                base,
                pte,
            )
    }

    pub open spec fn pt_entry_sizes_are_valid(self) -> bool {
        forall|base, pte|
            self.interp_pt_mem().contains_pair(base, pte) ==> {
                ||| pte.frame.size == L3_ENTRY_SIZE
                ||| pte.frame.size == L2_ENTRY_SIZE
                ||| pte.frame.size == L1_ENTRY_SIZE
            }
    }

    #[verifier(opaque)]
    pub open spec fn pt_entries_aligned(self) -> bool {
        forall|base, pte|
            self.interp_pt_mem().contains_pair(base, pte) ==> aligned(base, 8) && aligned(
                pte.frame.base,
                8,
            )
    }

    pub open spec fn inv(self) -> bool {
        &&& self.pt_mappings_dont_overlap_in_vmem()
        &&& self.pt_mappings_dont_overlap_in_pmem()
        &&& self.pt_entry_sizes_are_valid()
        &&& self.pt_entries_aligned()
        &&& self.tlb_is_submap_of_pt()
    }

    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables { map: self.interp_pt_mem() }
    }

    pub open spec fn interp_pt_mem(self) -> Map<nat, PageTableEntry> {
        hardware::interp_pt_mem(self.hw.pt_mem)
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PageTableEntry> {
        Map::new(
            |base: nat|
                self.hw.tlb.dom().contains(base) || self.interp_pt_mem().dom().contains(base),
            |base: nat|
                if self.hw.tlb.dom().contains(base) {
                    self.hw.tlb.index(base)
                } else {
                    self.interp_pt_mem().index(base)
                },
        )
    }

    pub open spec fn interp_vmem(self) -> Map<nat, nat> {
        let phys_mem_size = self.interp_constants().phys_mem_size;
        let mappings: Map<nat, PageTableEntry> = self.effective_mappings();
        Map::new(
            |vmem_idx: nat|
                hlspec::mem_domain_from_mappings_contains(phys_mem_size, vmem_idx, mappings),
            |vmem_idx: nat|
                {
                    let vaddr = vmem_idx * WORD_SIZE as nat;
                    let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry|
                        #![auto]
                        mappings.contains_pair(base, pte) && between(
                            vaddr,
                            base,
                            base + pte.frame.size,
                        );
                    let paddr = (pte.frame.base + (vaddr - base)) as nat;
                    let pmem_idx = word_index_spec(paddr);
                    self.hw.mem[pmem_idx as int]
                },
        )
    }

    pub open spec fn interp(self) -> hlspec::AbstractVariables {
        let mappings: Map<nat, PageTableEntry> = self.effective_mappings();
        let mem: Map<nat, nat> = self.interp_vmem();
        hlspec::AbstractVariables { mem, mappings }
    }

    pub open spec fn interp_constants(self) -> hlspec::AbstractConstants {
        hlspec::AbstractConstants { phys_mem_size: self.hw.mem.len() }
    }
}

pub open spec fn step_HW(s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& hardware::next_step(s1.hw, s2.hw, system_step)
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

pub open spec fn step_Map(
    s1: OSVariables,
    s2: OSVariables,
    base: nat,
    pte: PageTableEntry,
    result: MapResult,
) -> bool {
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}

pub open spec fn step_Unmap(
    s1: OSVariables,
    s2: OSVariables,
    base: nat,
    result: UnmapResult,
) -> bool {
    // The hw step tells us that s2.tlb is a submap of s1.tlb, so all we need to specify is
    // that s2.tlb doesn't contain this particular entry.
    &&& !s2.hw.tlb.dom().contains(base)
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

pub open spec fn step_Resolve(
    s1: OSVariables,
    s2: OSVariables,
    base: nat,
    result: ResolveResult,
) -> bool {
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}

pub enum OSStep {
    HW { step: hardware::HWStep },
    Map { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap { vaddr: nat, result: UnmapResult },
    Resolve { vaddr: nat, result: ResolveResult },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { step } => match step {
                hardware::HWStep::ReadWrite {
                    vaddr,
                    paddr,
                    op,
                    pte,
                } => hlspec::AbstractStep::ReadWrite { vaddr, op, pte },
                hardware::HWStep::PTMemOp => arbitrary(),
                hardware::HWStep::TLBFill { vaddr, pte } => hlspec::AbstractStep::Stutter,
                hardware::HWStep::TLBEvict { vaddr } => hlspec::AbstractStep::Stutter,
            },
            OSStep::Map { vaddr, pte, result } => hlspec::AbstractStep::Map { vaddr, pte, result },
            OSStep::Unmap { vaddr, result } => hlspec::AbstractStep::Unmap { vaddr, result },
            OSStep::Resolve { vaddr, result } => hlspec::AbstractStep::Resolve { vaddr, result },
        }
    }
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW { step } => step_HW(s1, s2, step),
        OSStep::Map { vaddr, pte, result } => step_Map(s1, s2, vaddr, pte, result),
        OSStep::Unmap { vaddr, result } => step_Unmap(s1, s2, vaddr, result),
        OSStep::Resolve { vaddr, result } => step_Resolve(s1, s2, vaddr, result),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

pub open spec fn init(s: OSVariables) -> bool {
    hardware::init(s.hw)
}

} // verus!
}

    pub mod impl_spec {
        #![allow(unused_imports)]
        #![verus::trusted]
        // trusted:
        // these are the interface specifications, they are part of the theorem

        use crate::definitions_t::{
            MapResult, PageTableEntry, PageTableEntryExec, ResolveResult, ResolveResultExec,
            UnmapResult,
        };
        use crate::impl_u::spec_pt;
        use crate::spec_t::hardware::interp_pt_mem;
        use crate::spec_t::hlspec;
        use crate::spec_t::mem;
        use builtin::*;
        use builtin_macros::*;
        use vstd::prelude::*;
        use vstd::set::*;

        verus! {

pub trait InterfaceSpec {
    spec fn ispec_inv(&self, mem: &mem::PageTableMemory) -> bool;

    proof fn ispec_init_implies_inv(&self, mem: &mem::PageTableMemory)
        requires
            mem.inv(),
            mem.regions() === set![mem.cr3_spec()@],
            mem.region_view(mem.cr3_spec()@).len() == 512,
            (forall|i: nat| i < 512 ==> mem.region_view(mem.cr3_spec()@)[i as int] == 0),
        ensures
            self.ispec_inv(mem),
    ;

    fn ispec_map_frame(
        &self,
        mem: &mut mem::PageTableMemory,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (res: MapResult)
        requires
            old(mem).alloc_available_pages() >= 3,
            spec_pt::step_Map_enabled(interp_pt_mem(*old(mem)), vaddr as nat, pte@),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Map(
                spec_pt::PageTableVariables { map: interp_pt_mem(*old(mem)) },
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                vaddr as nat,
                pte@,
                res,
            ),
    ;

    fn ispec_unmap(&self, mem: &mut mem::PageTableMemory, vaddr: usize) -> (res: UnmapResult)
        requires
            spec_pt::step_Unmap_enabled(vaddr as nat),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Unmap(
                spec_pt::PageTableVariables { map: interp_pt_mem(*old(mem)) },
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                vaddr as nat,
                res,
            ),
    ;

    fn ispec_resolve(&self, mem: &mem::PageTableMemory, vaddr: usize) -> (res: ResolveResultExec)
        requires
            spec_pt::step_Resolve_enabled(vaddr as nat),
            self.ispec_inv(mem),
        ensures
            spec_pt::step_Resolve(
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                vaddr as nat,
                res@,
            ),
    ;
}

pub struct PageTableImpl {}

pub closed spec fn implements_interface_spec<T: InterfaceSpec>() -> bool {
    true
}

// ensure that there's an implementation of the InterfaceSpec trait
pub proof fn theorem()
    ensures
        implements_interface_spec::<PageTableImpl>(),
{
}

} // verus!
}

    pub mod mem {
        #![allow(unused_imports)]
        #![verus::trusted]
        // trusted:
        // these are wrappers for the interface with the memory
        // `check_overflow` is a proof to harden the specification, it reduces the overall
        // trusted-ness of this file, but not in a quantifiable fashion; for this reason we deem
        // it appropriate to exclude it from P:C accounting

        use builtin::*;
        use builtin_macros::*;
        use vstd::map::*;
        use vstd::modes::*;
        use vstd::prelude::*;
        use vstd::seq::*;
        use vstd::set::*;
        use vstd::set_lib::*;

        use crate::definitions_t::{
            aligned, between, new_seq, overlap, Arch, MemRegion, MemRegionExec, PageTableEntry,
        };
        use crate::definitions_t::{MAX_PHYADDR, PAGE_SIZE, WORD_SIZE};
        use crate::impl_u::indexing;
        use crate::impl_u::l0::ambient_arith;
        use crate::impl_u::l1;

        verus! {

pub fn word_index(addr: usize) -> (res: usize)
    requires
        aligned(addr as nat, 8),
    ensures
        res as nat === word_index_spec(addr as nat),
        // Prove this equivalence to use the indexing lemmas
        res as nat === crate::definitions_t::index_from_offset(addr as nat, WORD_SIZE as nat),
        word_index_spec(addr as nat) === crate::definitions_t::index_from_offset(
            addr as nat,
            WORD_SIZE as nat,
        ),
{
    addr / WORD_SIZE
}

pub open spec fn word_index_spec(addr: nat) -> nat
    recommends
        aligned(addr, 8),
{
    addr / (WORD_SIZE as nat)
}

pub struct TLB {}

impl TLB {
    pub spec fn view(self) -> Map<nat, PageTableEntry>;

    /// Invalidates any TLB entries containing `vbase`.
    #[verifier(external_body)]
    pub fn invalidate_entry(&mut self, vbase: usize)
        ensures
            forall|base, pte|
                self.view().contains_pair(base, pte) ==> old(self).view().contains_pair(base, pte),
            !self.view().dom().contains(vbase as nat),
    {
        unimplemented!()
    }
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `phys_mem_ref` is the starting address of the physical memory linear mapping
    phys_mem_ref: *mut u64,
    cr3: u64,
}

impl PageTableMemory {
    pub spec fn alloc_available_pages(self) -> nat;

    pub spec fn regions(self) -> Set<MemRegion>;

    pub spec fn region_view(self, r: MemRegion) -> Seq<u64>;

    pub open spec fn inv(self) -> bool {
        &&& self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000
        &&& forall|s1: MemRegion, s2: MemRegion|
            self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(
                s1,
                s2,
            )
        &&& aligned(self.cr3_spec().base as nat, PAGE_SIZE as nat)
        &&& self.cr3_spec().size == PAGE_SIZE
    }

    pub open spec fn init(self) -> bool {
        &&& self.inv()
    }

    /// `cr3` returns a MemRegion whose base is the address at which the layer 0 page directory is mapped
    #[verifier(external_body)]
    pub fn cr3(&self) -> (res: MemRegionExec)
        ensures
            res === self.cr3_spec(),
    {
        MemRegionExec { base: self.cr3 as usize, size: PAGE_SIZE }
    }

    pub open spec fn cr3_spec(&self) -> MemRegionExec;

    // We assume that alloc_page never fails. In practice we can just keep a buffer of 3+ pages
    // that are allocated before we use map_frame.
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> (r: MemRegionExec)
        requires
            old(self).inv(),
            0 < old(self).alloc_available_pages(),
        ensures
            self.alloc_available_pages() == old(self).alloc_available_pages() - 1,
            r@.size == PAGE_SIZE,
            r@.base + PAGE_SIZE <= MAX_PHYADDR,
            aligned(r@.base, PAGE_SIZE as nat),
            !old(self).regions().contains(r@),
            self.regions() === old(self).regions().insert(r@),
            self.region_view(r@) === new_seq::<u64>(512nat, 0u64),
            forall|r2: MemRegion|
                r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
            self.inv(),
    {
        unimplemented!()
    }

    /// Deallocates a page
    #[verifier(external_body)]
    pub fn dealloc_page(&mut self, r: MemRegionExec)
        requires
            old(self).inv(),
            old(self).regions().contains(r@),
        ensures
            self.regions() === old(self).regions().remove(r@),
            forall|r2: MemRegion|
                r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
            self.inv(),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    /// Write value to physical address `pbase + idx * WORD_SIZE`
    pub fn write(&mut self, pbase: usize, idx: usize, region: Ghost<MemRegion>, value: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            old(self).inv(),
            old(self).regions().contains(region@),
            idx < 512,
        ensures
            self.region_view(region@) === old(self).region_view(region@).update(idx as int, value),
            forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
            self.regions() === old(self).regions(),
            self.alloc_available_pages() == old(self).alloc_available_pages(),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe {
            self.phys_mem_ref.offset(word_offset).write(value);
        }
    }

    #[verifier(external_body)]
    /// Read value at physical address `pbase + idx * WORD_SIZE`
    pub fn read(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
        ensures
            res == self.spec_read(idx as nat, region@),
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).read() }
    }

    pub open spec fn spec_read(self, idx: nat, region: MemRegion) -> (res: u64) {
        self.region_view(region)[idx as int]
    }

    /// This function manually does the address computation which `read` and `write` rely on not
    /// overflowing. Since this function is not `external_body`, Verus checks that there's no
    /// overflow. The preconditions are those of `read`, which are a subset of the `write`
    /// preconditions.
    /// (This is an exec function so it generates the normal overflow VCs.)
    #[verus::line_count::ignore]
    fn check_overflow(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>)
        requires
            pbase <= MAX_PHYADDR,
            self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000,
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
    {
        proof {
            crate::definitions_u::lemma_maxphyaddr_facts();
        }
        // https://dev-doc.rust-lang.org/beta/std/primitive.pointer.html#method.offset
        // The raw pointer offset computation needs to fit in an isize.
        // isize::MAX is   0x7FFF_FFFF_FFFF_FFFF
        //
        // `pbase` is a physical address, so we know it's <= MAX_PHYADDR (2^52-1).
        // The no-overflow assertions below require phys_mem_ref <= 0x7FEFFFFFFFFFF009.
        // In the invariant we require the (arbitrarily chosen) nicer number
        // 0x7FE0_0000_0000_0000 as an upper bound for phys_mem_ref.
        // (In practice the address has to be smaller anyway, because the address space
        // isn't that large.) NrOS uses 0x4000_0000_0000.
        assert(word_index_spec(pbase as nat) < 0x2_0000_0000_0000) by (nonlinear_arith)
            requires
                aligned(pbase as nat, WORD_SIZE as nat),
                pbase <= MAX_PHYADDR,
                MAX_PHYADDR <= 0xFFFFFFFFFFFFF,
        ;
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        assert(word_offset < 0x2_0000_0000_01FF) by (nonlinear_arith)
            requires
                idx < 512,
                word_offset == word_index_spec(pbase as nat) + idx,
                word_index_spec(pbase as nat) < 0x2_0000_0000_0000,
        ;
        let phys_mem_ref: isize = self.phys_mem_ref_as_usize() as isize;
        assert(word_offset * WORD_SIZE < 0x10_0000_0000_0FF8) by (nonlinear_arith)
            requires
                word_offset < 0x2_0000_0000_01FF,
        ;
        let byte_offset: isize = word_offset * (WORD_SIZE as isize);
        let raw_ptr_offset = phys_mem_ref + word_offset * (WORD_SIZE as isize);
    }

    #[verifier(external_body)]
    pub spec fn phys_mem_ref_as_usize_spec(&self) -> usize;

    #[verifier(external_body)]
    fn phys_mem_ref_as_usize(&self) -> (res: usize)
        ensures
            res == self.phys_mem_ref_as_usize_spec(),
    {
        unsafe { self.phys_mem_ref as usize }
    }
}

} // verus!
}
}

pub mod extra {
    #![allow(unused_imports)]
    use crate::definitions_t::{aligned, bit, bitmask_inc};
    use builtin::*;
    use builtin_macros::*;
    use vstd::map::*;
    use vstd::prelude::*;

    verus! {

pub proof fn mod_of_mul_integer_ring(a: int, b: int)
    by (integer_ring)
    ensures
        (a * b) % b == 0,
{
}

pub proof fn mod_of_mul(a: nat, b: nat)
    by (nonlinear_arith)
    requires
        b > 0,
    ensures
        aligned(a * b, b),
{
    mod_of_mul_integer_ring(a as int, b as int);
    assert((a * b) % b == 0);
}

pub proof fn mod_of_mul_auto()
    ensures
        forall|a: nat, b: nat| b > 0 ==> aligned(#[trigger] (a * b), b),
{
    assert forall|a: nat, b: nat| b > 0 implies aligned(#[trigger] (a * b), b) by {
        mod_of_mul(a, b);
    }
}

pub proof fn mod_add_zero_integer_ring(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % c == 0,
        b % c == 0,
    ensures
        (a + b) % c == 0,
{
}

pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    requires
        aligned(a, c),
        aligned(b, c),
        c > 0,
    ensures
        aligned(a + b, c),
{
    mod_add_zero_integer_ring(a as int, b as int, c as int);
}

pub proof fn mod_mult_zero_implies_mod_zero_integer_ring(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % (b * c) == 0,
    ensures
        a % b == 0,
{
}

pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        aligned(a, b * c),
        b > 0,
        c > 0,
    ensures
        aligned(a, b),
{
    mod_mult_zero_implies_mod_zero_integer_ring(a as int, b as int, c as int);
}

pub proof fn subtract_mod_eq_zero_integer_ring(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % c == 0,
        b % c == 0,
    ensures
        (b - a) % c == 0,
{
}

pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    requires
        aligned(a, c),
        aligned(b, c),
        a <= b,
        c > 0,
    ensures
        aligned((b - a) as nat, c),
{
    subtract_mod_eq_zero_integer_ring(a as int, b as int, c as int)
}

pub proof fn leq_add_aligned_less(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        0 < b,
        a < c,
        aligned(a, b),
        aligned(c, b),
    ensures
        a + b <= c,
{
    assert(a == b * (a / b) + a % b);
    assert(c == b * (c / b) + c % b);
}

pub proof fn aligned_transitive_auto()
    ensures
        forall|a: nat, b: nat, c: nat|
            0 < b && 0 < c && aligned(a, b) && aligned(b, c) ==> aligned(a, c),
{
    assert forall|a: nat, b: nat, c: nat|
        0 < b && 0 < c && aligned(a, b) && aligned(b, c) implies aligned(a, c) by {
        aligned_transitive(a, b, c);
    }
}

pub proof fn lemma_aligned_iff_eq_mul_div(a: nat, b: nat)
    requires
        b > 0,
    ensures
        aligned(a, b) <==> a == b * (a / b),
{
    assert(a % b == 0 ==> a == b * (a / b)) by (nonlinear_arith)
        requires
            b > 0,
    ;
    assert(a == b * (a / b) ==> a % b == 0) by (nonlinear_arith)
        requires
            b > 0,
    ;
}

pub proof fn aligned_transitive(a: nat, b: nat, c: nat)
    requires
        0 < b,
        0 < c,
        aligned(a, b),
        aligned(b, c),
    ensures
        aligned(a, c),
{
    lemma_aligned_iff_eq_mul_div(a, b);
    lemma_aligned_iff_eq_mul_div(b, c);
    lemma_aligned_iff_eq_mul_div(a, c);
    let i = a / b;
    let j = b / c;
    assert((c * j) * i == c * (j * i)) by (nonlinear_arith);
    assert(a / c == j * i) by (nonlinear_arith)
        requires
            0 < c,
            a == c * (j * i),
    ;
}

#[verifier(nonlinear)]
pub proof fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[verifier(nonlinear)]
pub proof fn aligned_zero()
    ensures
        forall|a: nat| a != 0 ==> aligned(0, a),
{
}

#[verifier(nonlinear)]
pub proof fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[verifier(nonlinear)]
pub proof fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}

#[verifier(nonlinear)]
pub proof fn div_mul_cancel(a: nat, b: nat) {
    requires([aligned(a, b), b != 0]);
    ensures(a / b * b == a);
}

#[verifier(nonlinear)]
pub proof fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono_both(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b <= d,
    ensures
// Including `0 <=` here because it's used in a place where this is part of an overflow VC
// and non-nonlinear z3 can't even deal with that.

        0 <= a * b <= c * d,
;

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both1(a: nat, b: nat, c: nat, d: nat)
    requires
        a < c,
        b <= d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d,
;

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both2(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b < d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d,
;

pub proof fn assert_maps_equal_contains_pair<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k: K, v: V| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k: K, v: V| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2,
{
    assert forall|k| m1.dom().contains(k) implies m2.dom().contains(k) by {
        assert(m2.contains_pair(k, m1.index(k)));
    };
    assert forall|k| m2.dom().contains(k) implies m1.dom().contains(k) by {
        assert(m1.contains_pair(k, m2.index(k)));
    };
    assert forall|k| m1.dom().contains(k) && m2.dom().contains(k) implies #[trigger] m2.index(k)
        === #[trigger] m1.index(k) by {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    };
    assert_maps_equal!(m1, m2);
}

} // verus!
}

use vstd::prelude::verus;

verus! {

global size_of usize == 8;

} // verus!
fn main() {}
