#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::slice::*;

pub mod infinitelog_t {
    /*

      This file models the abstraction of an infinite log that our log
      implementation is supposed to implement.

    */

    use crate::pmemspec_t::*;
    use builtin::*;
    use builtin_macros::*;
    use vstd::prelude::*;
    use vstd::set::*;

    verus! {
        #[verifier::ext_equal]
        pub struct AbstractInfiniteLogState {
            pub head: int,
            pub log: Seq<u8>,
            pub capacity: int,
        }

        impl AbstractInfiniteLogState {
            pub open spec fn initialize(capacity: int) -> Self {
                Self{ head: 0int, log: Seq::<u8>::empty(), capacity: capacity }
            }

            pub open spec fn append(self, bytes: Seq<u8>) -> Self {
                Self{ head: self.head, log: self.log + bytes, capacity: self.capacity }
            }

            pub open spec fn advance_head(self, new_head: int) -> Self
            {
                if self.head <= new_head <= self.head + self.log.len() {
                    let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
                    Self{ head: new_head, log: new_log, capacity: self.capacity }
                }
                else {
                    self
                }
            }
        }

    }
}

pub mod logimpl_v {
    use crate::infinitelog_t::*;
    use crate::main_t::*;
    use crate::math::*;
    use crate::pmemspec_t::*;
    use crate::sccf::CheckPermission;
    use builtin::*;
    use builtin_macros::*;
    use core::convert::TryInto;
    use std::f32::consts::E;
    use std::fmt::Write;
    use vstd::bytes::*;
    use vstd::prelude::*;
    use vstd::seq::*;
    use vstd::set::*;
    use vstd::slice::*;

    verus! {

        // entire header structure:
        // bytes 0-7: incorruptible boolean
        // bytes 8-39: header 1
        // bytes 40-71: header 2

        // header version structure:
        // 0-7: header CRC
        // 8-15: logical head
        // 16-23: logical tail
        // 24-31: log size

        pub const incorruptible_bool_pos: u64 = 0;
        pub const header1_pos: u64 = 8;
        pub const header2_pos: u64 = 40;

        // offsets of fields within the header structure
        pub const header_crc_offset: u64 = 0;
        pub const header_head_offset: u64 = 8;
        pub const header_tail_offset: u64 = 16;
        pub const header_log_size_offset: u64 = 24;

        pub const header_size: u64 = 32;

        /// Converts the view of a PM region into its incorruptible Boolean, a view of its header,
        /// and a data region.
        pub open spec fn pm_to_views(pm: Seq<u8>) -> (u64, HeaderView, Seq<u8>)
        {
            let incorruptible_bool = spec_u64_from_le_bytes(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
            // read the CRC, then read the rest of the metadata, then combine them
            let crc1 = spec_u64_from_le_bytes(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));
            let crc2 = spec_u64_from_le_bytes(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

            let header1_metadata = spec_bytes_to_metadata(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
            let header2_metadata = spec_bytes_to_metadata(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
            let header_view = HeaderView {
                header1: PersistentHeader {
                    crc: crc1,
                    metadata: header1_metadata,
                },
                header2: PersistentHeader {
                    crc: crc2,
                    metadata: header2_metadata,
                }
            };
            let data_view = pm.subrange(contents_offset as int, pm.len() as int);
            (
                incorruptible_bool,
                header_view,
                data_view
            )
        }

        pub open spec fn spec_get_live_header(pm: Seq<u8>) -> PersistentHeader
        {
            let (ib, headers, _) = pm_to_views(pm);
            if ib == cdb0_val {
                headers.header1
            } else {
                headers.header2
            }
        }

        pub open spec fn permissions_depend_only_on_recovery_view<Perm: CheckPermission<Seq<u8>>>(perm: &Perm) -> bool
        {
            forall |s1, s2| recovery_view()(s1) == recovery_view()(s2) ==> perm.check_permission(s1) == perm.check_permission(s2)
        }

        pub proof fn lemma_same_permissions<Perm: CheckPermission<Seq<u8>>>(pm1: Seq<u8>, pm2: Seq<u8>, perm: &Perm)
            requires
                recovery_view()(pm1) =~= recovery_view()(pm2),
                perm.check_permission(pm1),
                permissions_depend_only_on_recovery_view(perm)
            ensures
                perm.check_permission(pm2)
        {}

        /// Proves that a PM region has the given header at the given position. Useful for
        /// associating a region with a header structure when the struct will be used later
        /// in a proof.
        pub proof fn lemma_header_match(pm: Seq<u8>, header_pos: int, header: PersistentHeader)
            requires
                pm.len() > contents_offset,
                header_pos == header1_pos || header_pos == header2_pos,
                spec_bytes_to_header(pm.subrange(header_pos as int, header_pos + header_size)) == header,
            ensures
                ({
                    let (_, headers, _) = pm_to_views(pm);
                    &&& header_pos == header1_pos ==>
                            headers.header1 == header
                    &&& header_pos == header2_pos ==>
                            headers.header2 == header
                })
        {
            assert(pm.subrange(header_pos as int, header_pos + header_size) =~=
                    pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) +
                    pm.subrange(header_pos + header_head_offset, header_pos + header_size)
                );
            lemma_bytes_combine_into_header(
                pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8),
                pm.subrange(header_pos + header_head_offset, header_pos + header_size),
                header
            );
        }

        /// Proves that a given header structure consists of a CRC given in bytes as `crc_bytes` and a metadata structure
        /// given in bytes as `metadata_bytes`.
        pub proof fn lemma_bytes_combine_into_header(crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, header: PersistentHeader)
            requires
                crc_bytes.len() == 8,
                metadata_bytes.len() == header_size - 8,
                spec_bytes_to_header((crc_bytes + metadata_bytes)) == header,
            ensures
                ({
                    let combined_header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
                    header == combined_header
                })
        {
            let crc_val = spec_u64_from_le_bytes(crc_bytes);
            let metadata = spec_bytes_to_metadata(metadata_bytes);
            lemma_seq_addition(crc_bytes, metadata_bytes);

            let combined_header = spec_bytes_to_header((crc_bytes + metadata_bytes));
            assert(combined_header.crc == crc_val);
            assert(metadata == spec_bytes_to_metadata((crc_bytes + metadata_bytes).subrange(header_head_offset as int, header_size as int)));
            assert(combined_header.metadata == metadata);
        }

        /// Converse of lemma_bytes_combine_into_header; proves that the byte representation of a header consists of
        /// the byte representations of its CRC and metadata
        pub proof fn lemma_header_split_into_bytes(crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, header_bytes: Seq<u8>)
            requires
                crc_bytes.len() == 8,
                metadata_bytes.len() == header_size - 8,
                header_bytes.len() == header_size,
                ({
                    let header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
                    spec_bytes_to_header(header_bytes) == header
                }),
            ensures
                crc_bytes + metadata_bytes =~= header_bytes
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            let header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
            assert(header.crc == spec_u64_from_le_bytes(crc_bytes));
            assert(header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= spec_u64_to_le_bytes(header.crc));
            assert(crc_bytes =~= spec_u64_to_le_bytes(header.crc));

            assert(header.metadata == spec_bytes_to_metadata(metadata_bytes));
            assert(header.metadata == spec_bytes_to_metadata(header_bytes.subrange(header_head_offset as int, header_size as int)));
            lemma_metadata_bytes_eq(metadata_bytes, header_bytes.subrange(header_head_offset as int, header_size as int), header.metadata);
            assert(header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes);

        }

        pub proof fn lemma_seq_addition(bytes1: Seq<u8>, bytes2: Seq<u8>)
            ensures
                ({
                    let i = bytes1.len() as int;
                    let j = bytes2.len() as int;
                    &&& (bytes1 + bytes2).subrange(0, i) =~= bytes1
                    &&& (bytes1 + bytes2).subrange(i, i + j) =~= bytes2
                })
        {
            assert(forall |i: int| #![auto] 0 <= i < bytes1.len() ==> (bytes1 + bytes2)[i] == bytes1[i]);
            assert(forall |i: int| #![auto] 0 <= i < bytes2.len() ==> (bytes1 + bytes2)[bytes1.len() + i] == bytes2[i]);
        }

        #[verifier::ext_equal]
        pub struct PersistentHeader {
            pub crc: u64,
            pub metadata: PersistentHeaderMetadata,
        }

        #[verifier::ext_equal]
        pub struct PersistentHeaderMetadata {
            pub head: u64,
            pub tail: u64,
            pub log_size: u64,
        }

        #[verifier::ext_equal]
        pub struct HeaderView {
            pub header1: PersistentHeader,
            pub header2: PersistentHeader,
        }

        /// Spec code only converts byte representations to structures and does not go the other way
        /// to simplify reasoning about persistent structures (although the opposite direction is
        /// implemented in exec code).

        exec fn bytes_to_header(bytes: &[u8]) -> (out: PersistentHeader)
            requires
                bytes@.len() == header_size
            ensures
                out == spec_bytes_to_header(bytes@)
        {
            let crc_bytes = slice_subrange(bytes, header_crc_offset as usize, (header_crc_offset + 8) as usize);
            let metadata_bytes = slice_subrange(bytes, header_head_offset as usize, header_size as usize);

            PersistentHeader {
                crc: u64_from_le_bytes(crc_bytes),
                metadata: bytes_to_metadata(metadata_bytes),
            }
        }

        exec fn header_to_bytes(header: &PersistentHeader) -> (out: Vec<u8>)
            ensures
                header == spec_bytes_to_header(out@),
                spec_u64_from_le_bytes(out@.subrange(header_crc_offset as int, header_crc_offset + 8)) == header.crc,
                spec_bytes_to_metadata(out@.subrange(header_head_offset as int, header_size as int)) == header.metadata,
                out@.len() == header_size
        {
            proof { lemma_auto_spec_u64_to_from_le_bytes(); }

            let mut metadata_bytes = metadata_to_bytes(&header.metadata);
            let mut crc_bytes = u64_to_le_bytes(header.crc);
            let ghost old_metadata_bytes = metadata_bytes@;
            let ghost old_crc_bytes = crc_bytes@;
            crc_bytes.append(&mut metadata_bytes);
            proof {
                lemma_auto_spec_u64_to_from_le_bytes();
                assert(old_crc_bytes =~= crc_bytes@.subrange(header_crc_offset as int, header_crc_offset + 8));
                assert(old_metadata_bytes =~= crc_bytes@.subrange(header_head_offset as int, header_size as int));
            }
            crc_bytes
        }

        exec fn bytes_to_metadata(bytes: &[u8]) -> (out: PersistentHeaderMetadata)
            requires
                bytes@.len() == header_size - 8
            ensures
                out == spec_bytes_to_metadata(bytes@)
        {
            let head_bytes = slice_subrange(bytes, (header_head_offset - 8) as usize, (header_head_offset - 8 + 8) as usize);
            let tail_bytes = slice_subrange(bytes, (header_tail_offset - 8) as usize, (header_tail_offset - 8+ 8) as usize);
            let log_size_bytes = slice_subrange(bytes, (header_log_size_offset - 8) as usize, (header_log_size_offset - 8 + 8) as usize);

            PersistentHeaderMetadata {
                head: u64_from_le_bytes(head_bytes),
                tail: u64_from_le_bytes(tail_bytes),
                log_size: u64_from_le_bytes(log_size_bytes),
            }
        }

        exec fn metadata_to_bytes(metadata: &PersistentHeaderMetadata) -> (out: Vec<u8>)
            ensures
                metadata == spec_bytes_to_metadata(out@),
                out@.len() == header_size - 8,
        {
            let mut bytes: Vec<u8> = Vec::new();
            let ghost old_bytes = bytes@;

            let mut head_bytes = u64_to_le_bytes(metadata.head);
            let ghost old_head_bytes = head_bytes@;
            let mut tail_bytes = u64_to_le_bytes(metadata.tail);
            let ghost old_tail_bytes = tail_bytes@;
            let mut log_size_bytes = u64_to_le_bytes(metadata.log_size);
            let ghost old_log_size_bytes = log_size_bytes@;

            bytes.append(&mut head_bytes);
            bytes.append(&mut tail_bytes);
            bytes.append(&mut log_size_bytes);

            proof {
                lemma_auto_spec_u64_to_from_le_bytes();
                assert(old_bytes == Seq::<u8>::empty());
                assert(old_head_bytes =~= bytes@.subrange(header_head_offset - 8, header_head_offset - 8 + 8));
                assert(old_tail_bytes =~= bytes@.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));
                assert(old_log_size_bytes =~= bytes@.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
            }
            bytes
        }

        exec fn crc_and_metadata_bytes_to_header(crc_bytes: &[u8], header_bytes: &[u8]) -> (out: PersistentHeader)
            requires
                crc_bytes@.len() == 8,
                header_bytes@.len() == header_size - 8
            ensures
                out.crc == spec_u64_from_le_bytes(crc_bytes@),
                out.metadata == spec_bytes_to_metadata(header_bytes@)
        {
            let head_bytes = slice_subrange(header_bytes, (header_head_offset - 8) as usize, (header_head_offset + 8 - 8) as usize);
            let tail_bytes = slice_subrange(header_bytes, (header_tail_offset - 8) as usize, (header_tail_offset + 8 - 8) as usize);
            let log_size_bytes = slice_subrange(header_bytes, (header_log_size_offset - 8) as usize, (header_log_size_offset + 8 - 8) as usize);

            PersistentHeader {
                crc: u64_from_le_bytes(crc_bytes),
                metadata: PersistentHeaderMetadata {
                    head: u64_from_le_bytes(head_bytes),
                    tail: u64_from_le_bytes(tail_bytes),
                    log_size: u64_from_le_bytes(log_size_bytes)
                }
            }
        }

        pub open spec(checked) fn spec_bytes_to_metadata(header_seq: Seq<u8>) -> PersistentHeaderMetadata
            recommends
                header_seq.len() == 3*8
        {
            let head = spec_u64_from_le_bytes(header_seq.subrange(header_head_offset - 8, header_head_offset - 8 + 8));
            let tail = spec_u64_from_le_bytes(header_seq.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));
            let log_size = spec_u64_from_le_bytes(header_seq.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
            PersistentHeaderMetadata {
                head,
                tail,
                log_size
            }
        }

        /// Proves that two sequences of bytes (assumed to be the subrange of a persistent memory device containing
        /// the PersistentHeaderMetadata) are equivalent if their PersistentHeaderMetadata representations are equivalent
        pub proof fn lemma_metadata_bytes_eq(bytes1: Seq<u8>, bytes2: Seq<u8>, metadata: PersistentHeaderMetadata)
            requires
                bytes1.len() == header_size - 8,
                bytes2.len() == header_size - 8,
                metadata == spec_bytes_to_metadata(bytes1),
                metadata == spec_bytes_to_metadata(bytes2),
            ensures
                bytes1 =~= bytes2
        {
            let metadata1 = spec_bytes_to_metadata(bytes1);
            let metadata2 = spec_bytes_to_metadata(bytes2);

            // TODO: could write a lemma that triggers on from instead of to - might help here
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(spec_u64_to_le_bytes(metadata1.head) == spec_u64_to_le_bytes(metadata2.head));
            assert(metadata1.head == spec_u64_from_le_bytes(bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8)));
            assert(metadata2.head == spec_u64_from_le_bytes(bytes2.subrange(header_head_offset - 8, header_head_offset - 8 + 8)));
            assert(bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8) =~= bytes2.subrange(header_head_offset - 8, header_head_offset - 8 + 8));

            assert(spec_u64_to_le_bytes(metadata1.tail) == spec_u64_to_le_bytes(metadata2.tail));
            assert(metadata1.tail == spec_u64_from_le_bytes(bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8)));
            assert(metadata2.tail == spec_u64_from_le_bytes(bytes2.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8)));
            assert(bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8) =~= bytes2.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));

            assert(spec_u64_to_le_bytes(metadata1.log_size) == spec_u64_to_le_bytes(metadata2.log_size));
            assert(metadata1.log_size == spec_u64_from_le_bytes(bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8)));
            assert(metadata2.log_size == spec_u64_from_le_bytes(bytes2.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8)));
            assert(bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8) =~= bytes2.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));

            assert(bytes1 =~= bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8) +
                                bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8) +
                                bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
        }

        pub open spec(checked) fn spec_bytes_to_header(header_seq: Seq<u8>) -> PersistentHeader
            recommends
                header_seq.len() == header_size
        {
            let crc_val = spec_u64_from_le_bytes(header_seq.subrange(header_crc_offset as int, header_crc_offset +8));
            let metadata = spec_bytes_to_metadata(header_seq.subrange(header_head_offset as int, header_size as int));
            PersistentHeader {
                crc: crc_val,
                metadata
            }
        }

        /// Proves that a write to data that does not touch any metadata is crash safe.
        pub proof fn lemma_data_write_is_safe<Perm>(pm: Seq<u8>, bytes: Seq<u8>, write_addr: int, perm: &Perm)
            where
                Perm: CheckPermission<Seq<u8>>,
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                pm.len() > contents_offset,
                contents_offset <= write_addr < pm.len(),
                perm.check_permission(pm),
                permissions_depend_only_on_recovery_view(perm),
                ({
                    // write must be a valid write and not overlap the live log
                    let live_header = spec_get_live_header(pm);
                    let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                    &&& physical_head <= physical_tail ==> {
                        &&& write_addr + bytes.len() <= live_header.metadata.log_size + contents_offset
                        &&& write_addr < physical_head ==> write_addr + bytes.len() <= physical_head
                        &&& (physical_tail <= write_addr || write_addr < physical_head)
                    }
                    &&& physical_tail < physical_head ==> {
                        &&& physical_tail <= write_addr <= write_addr + bytes.len() < physical_head
                    }
                }),
            ensures
                UntrustedLogImpl::recover(pm).is_Some(),
                forall |chunks_flushed| {
                    let new_pm = #[trigger] update_contents_to_reflect_partially_flushed_write(
                        pm, write_addr, bytes, chunks_flushed);
                    perm.check_permission(new_pm)
                },
                ({
                    let new_pm = update_contents_to_reflect_write(pm, write_addr, bytes);
                    perm.check_permission(new_pm)
                }),
                update_data_view_postcond(pm, bytes, write_addr),
        {
            let new_pm = update_contents_to_reflect_write(pm, write_addr, bytes);
            lemma_append_data_update_view(pm, bytes, write_addr);
            lemma_same_log_state(pm, new_pm);

            assert forall |chunks_flushed| {
                let new_pm = #[trigger] update_contents_to_reflect_partially_flushed_write(
                    pm, write_addr, bytes, chunks_flushed);
                perm.check_permission(new_pm)
            } by {
                let new_pm = update_contents_to_reflect_partially_flushed_write(
                    pm, write_addr, bytes, chunks_flushed);
                lemma_append_data_update_view_crash(pm, bytes, write_addr, chunks_flushed);
                lemma_same_log_state(pm, new_pm);
                lemma_same_permissions(pm, new_pm, perm);
            }
        }

        pub open spec fn update_data_view_postcond(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int) -> bool
        {
            let new_pm = update_contents_to_reflect_write(pm, write_addr, new_bytes);
            let (old_ib, old_headers, old_data) = pm_to_views(pm);
            let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
            let live_header = spec_get_live_header(pm);
            let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
            let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
            &&& old_ib == new_ib
            &&& old_headers == new_headers
            &&& new_data.len() == old_data.len()
            &&& new_data.subrange(write_addr - contents_offset, write_addr - contents_offset + new_bytes.len()) =~= new_bytes
            &&& new_data.subrange(0, write_addr - contents_offset) =~= old_data.subrange(0, write_addr - contents_offset)
            &&& new_data.subrange(write_addr - contents_offset + new_bytes.len(), new_data.len() as int) =~=
                    old_data.subrange(write_addr - contents_offset + new_bytes.len(), old_data.len() as int)
            &&& UntrustedLogImpl::recover(new_pm).is_Some()

            &&& physical_head < physical_tail ==>
                    new_data.subrange(physical_head - contents_offset, physical_tail - contents_offset) =~= old_data.subrange(physical_head - contents_offset, physical_tail - contents_offset)
            &&& physical_tail < physical_head ==> {
                    &&& old_data.subrange(physical_head - contents_offset, live_header.metadata.log_size as int) =~= new_data.subrange(physical_head - contents_offset, live_header.metadata.log_size as int)
                    &&& old_data.subrange(0, physical_tail - contents_offset) =~= new_data.subrange(0, physical_tail - contents_offset)
            }
        }

        /// Proves that a non-crashing data write updates data bytes but no log metadata.
        pub proof fn lemma_append_data_update_view(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int)
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                pm.len() > contents_offset,
                contents_offset <= write_addr < pm.len(),
                ({
                    // write must be a valid write and not overlap the live log
                    let live_header = spec_get_live_header(pm);
                    let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                    &&& physical_head <= physical_tail ==> {
                            &&& write_addr + new_bytes.len() <= live_header.metadata.log_size + contents_offset
                            &&& write_addr < physical_head ==> write_addr + new_bytes.len() <= physical_head
                            &&& (physical_tail <= write_addr || write_addr < physical_head)
                    }
                    &&& physical_tail < physical_head ==> {
                            &&& physical_tail <= write_addr <= write_addr + new_bytes.len() < physical_head
                    }
                }),
            ensures
                UntrustedLogImpl::recover(pm).is_Some(),
                update_data_view_postcond(pm, new_bytes, write_addr),
        {
            let live_header = spec_get_live_header(pm);
            let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
            let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
            let new_pm = update_contents_to_reflect_write(pm, write_addr, new_bytes);
            lemma_headers_unchanged(pm, new_pm);
            lemma_incorruptible_bool_unchanged(pm, new_pm);
            assert(live_header == spec_get_live_header(new_pm));
            assert(new_pm.subrange(0, write_addr) =~= pm.subrange(0, write_addr));
            assert(new_pm.subrange(write_addr + new_bytes.len(), new_pm.len() as int) =~= pm.subrange(write_addr + new_bytes.len(), pm.len() as int));
            lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, 0, write_addr);
            lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, write_addr + new_bytes.len(), new_pm.len() as int);
            if physical_head < physical_tail {
                assert(new_pm.subrange(physical_head as int, physical_tail as int) =~= pm.subrange(physical_head as int, physical_tail as int));
            }
        }

        /// Proves that a crashing data write updates data bytes but no log metadata.
        pub proof fn lemma_append_data_update_view_crash(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int, chunks_flushed: Set<int>)
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                pm.len() > contents_offset,
                contents_offset <= write_addr < pm.len(),
                ({
                    // write must be a valid write and not overlap the live log
                    let live_header = spec_get_live_header(pm);
                    let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                    &&& physical_head <= physical_tail ==> write_addr + new_bytes.len() <= live_header.metadata.log_size + contents_offset
                    &&& physical_tail < physical_head ==> write_addr + new_bytes.len() < physical_head
                })
            ensures
                UntrustedLogImpl::recover(pm).is_Some(),
                ({
                    let new_pm = update_contents_to_reflect_partially_flushed_write(pm, write_addr, new_bytes, chunks_flushed);
                    let (old_ib, old_headers, old_data) = pm_to_views(pm);
                    let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                    &&& old_ib == new_ib
                    &&& old_headers == new_headers
                    &&& new_data.len() == old_data.len()
                    &&& new_data.subrange(0, write_addr - contents_offset) =~= old_data.subrange(0, write_addr - contents_offset)
                    &&& new_data.subrange(write_addr - contents_offset + new_bytes.len(), new_data.len() as int) =~=
                            old_data.subrange(write_addr - contents_offset + new_bytes.len(), old_data.len() as int)
                    &&& UntrustedLogImpl::recover(new_pm).is_Some()
                })
        {
            let live_header = spec_get_live_header(pm);
            let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
            let new_pm = update_contents_to_reflect_partially_flushed_write(pm, write_addr, new_bytes, chunks_flushed);
            lemma_headers_unchanged(pm, new_pm);
            lemma_incorruptible_bool_unchanged(pm, new_pm);
            assert(new_pm.subrange(0, write_addr) =~= pm.subrange(0, write_addr));
            assert(new_pm.subrange(write_addr + new_bytes.len(), new_pm.len() as int) =~= pm.subrange(write_addr + new_bytes.len(), pm.len() as int));
            lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, 0, write_addr);
        }

        /// Proves that a non-crashing update to the inactive header does not change any visible PM state.
        pub proof fn lemma_inactive_header_update_view(pm: Seq<u8>, new_header_bytes: Seq<u8>, header_pos: int)
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                header_pos == header1_pos || header_pos == header2_pos,
                ({
                    // the new bytes must be written to the inactive header
                    let (old_ib, old_headers, old_data) = pm_to_views(pm);
                    &&& old_ib == cdb0_val ==> header_pos == header2_pos
                    &&& old_ib == cdb1_val ==> header_pos == header1_pos
                }),
                new_header_bytes.len() == header_size,
                pm.len() > contents_offset,
            ensures
                ({
                    let new_pm = update_contents_to_reflect_write(pm, header_pos, new_header_bytes);
                    let (old_ib, old_headers, old_data) = pm_to_views(pm);
                    let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                    &&& old_ib == new_ib
                    &&& old_data =~= old_data
                    &&& header_pos == header1_pos ==>
                        old_headers.header2 == new_headers.header2
                    &&& header_pos == header2_pos ==>
                        old_headers.header1 == new_headers.header1
                    &&& UntrustedLogImpl::recover(new_pm).is_Some()
                })
        {
            let new_pm = update_contents_to_reflect_write(pm, header_pos, new_header_bytes);
            let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
            assert(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
            if header_pos == header1_pos {
                // we wrote to header1, so header2 should have stayed the same
                assert(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~=
                    new_pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

                assert(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size) =~=
                    new_pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
            } else {
                // we wrote to header2, so header1 should have stayed the same
                assert(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~=
                    new_pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));

                assert(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~=
                    new_pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
            }
        }

        /// Proves that a crashing update to the inactive header does not change any visible PM state.
        pub proof fn lemma_inactive_header_update_view_crash(pm: Seq<u8>, new_header_bytes: Seq<u8>, header_pos: int, chunks_flushed: Set<int>)
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                header_pos == header1_pos || header_pos == header2_pos,
                ({
                    // the new bytes must be written to the inactive header
                    let (old_ib, old_headers, old_data) = pm_to_views(pm);
                    &&& old_ib == cdb0_val ==> header_pos == header2_pos
                    &&& old_ib == cdb1_val ==> header_pos == header1_pos
                }),
                new_header_bytes.len() == header_size,
                pm.len() > contents_offset,
            ensures
                ({
                    let new_pm = update_contents_to_reflect_partially_flushed_write(
                        pm, header_pos, new_header_bytes, chunks_flushed);
                    let (old_ib, old_headers, old_data) = pm_to_views(pm);
                    let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                    &&& old_ib == new_ib
                    &&& old_data =~= old_data
                    &&& header_pos == header1_pos ==>
                        old_headers.header2 == new_headers.header2
                    &&& header_pos == header2_pos ==>
                        old_headers.header1 == new_headers.header1
                    &&& UntrustedLogImpl::recover(new_pm).is_Some()
                })
        {
            let new_pm = update_contents_to_reflect_partially_flushed_write(
                pm, header_pos, new_header_bytes, chunks_flushed);
            assert(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
            if header_pos == header1_pos {
                // we wrote to header1, so header2 should have stayed the same
                assert(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~=
                    new_pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

                assert(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size) =~=
                    new_pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
            } else {
                // we wrote to header2, so header1 should have stayed the same
                assert(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~=
                    new_pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));

                assert(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~=
                    new_pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
            }
        }

        /// Proves that an update to the incorruptible boolean is crash-safe and switches the log's
        /// active header. This lemma does most of the work to prove that untrusted_append is
        /// implemented correctly.
        pub proof fn lemma_append_ib_update<Perm: CheckPermission<Seq<u8>>>(
            pm: Seq<u8>,
            new_ib: u64,
            bytes_to_append: Seq<u8>,
            new_header_bytes: Seq<u8>,
            perm: &Perm
        )
            requires
                pm.len() > contents_offset,
                UntrustedLogImpl::recover(pm).is_Some(),
                new_ib == cdb0_val || new_ib == cdb1_val,
                new_ib == cdb0_val ==>
                    pm.subrange(header1_pos as int, header1_pos + header_size) == new_header_bytes,
                new_ib == cdb1_val ==>
                    pm.subrange(header2_pos as int, header2_pos + header_size) == new_header_bytes,
                new_header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) ==
                    spec_crc_bytes(new_header_bytes.subrange(header_head_offset as int, header_size as int)),
                ({
                    let new_header = spec_bytes_to_header(new_header_bytes);
                    let live_header = spec_get_live_header(pm);
                    &&& new_header.metadata.tail == live_header.metadata.tail + bytes_to_append.len()
                    &&& new_header.metadata.head == live_header.metadata.head
                    &&& new_header.metadata.log_size == live_header.metadata.log_size
                    &&& new_header.metadata.tail - new_header.metadata.head < new_header.metadata.log_size
                }),
                perm.check_permission(pm),
                permissions_depend_only_on_recovery_view(perm),
                ({
                    let live_header = spec_get_live_header(pm);
                    let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                    let contents_end = (live_header.metadata.log_size + contents_offset) as int;
                    let append_size = bytes_to_append.len();
                    let len1 = (contents_end - physical_tail);
                    let len2 = bytes_to_append.len() - len1;

                    &&& physical_tail + append_size >= contents_end ==> {
                        &&& pm.subrange(physical_tail, contents_end) =~= bytes_to_append.subrange(0, len1)
                        &&& pm.subrange(contents_offset as int, contents_offset + len2) =~= bytes_to_append.subrange(len1 as int, append_size as int)
                        &&& bytes_to_append =~= pm.subrange(physical_tail, contents_end) + pm.subrange(contents_offset as int, contents_offset + len2)
                    }
                    &&& physical_head <= physical_tail && physical_tail + append_size < contents_end ==> {
                        pm.subrange(physical_tail, physical_tail + append_size) =~= bytes_to_append
                    }
                    &&& physical_tail < physical_head ==> {
                        &&& physical_tail + append_size < physical_head
                        &&& pm.subrange(physical_tail, physical_tail + append_size) =~= bytes_to_append
                    }
                }),
                ({
                    let old_log_state = UntrustedLogImpl::recover(pm);
                    forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                        let log_state = UntrustedLogImpl::recover(pm_state);
                        log_state == old_log_state || log_state == Some(old_log_state.unwrap().append(bytes_to_append))
                    }
                }),
            ensures
                ({
                    let ib_bytes = spec_u64_to_le_bytes(new_ib);
                    let new_pm = update_contents_to_reflect_write(pm, incorruptible_bool_pos as int, ib_bytes);
                    let old_log_state = UntrustedLogImpl::recover(pm);
                    let new_log_state = UntrustedLogImpl::recover(new_pm);
                    let new_live_header = spec_get_live_header(new_pm);
                    let (new_pm_ib, _, _) = pm_to_views(new_pm);
                    &&& match (old_log_state, new_log_state) {
                            (Some(old_log_state), Some(new_log_state)) => {
                                &&& new_log_state =~= old_log_state.append(bytes_to_append)
                                &&& perm.check_permission(new_pm)
                            }
                            _ => false,
                        }
                    &&& new_live_header == spec_bytes_to_header(new_header_bytes)
                    &&& new_ib == new_pm_ib
                }),
                forall |chunks_flushed| {
                    let new_pm = #[trigger] update_contents_to_reflect_partially_flushed_write(
                        pm, incorruptible_bool_pos as int, spec_u64_to_le_bytes(new_ib), chunks_flushed);
                    &&& perm.check_permission(new_pm)
                }
        {
            let ib_bytes = spec_u64_to_le_bytes(new_ib);
            let live_header = spec_get_live_header(pm);
            let append_size = bytes_to_append.len();
            let contents_end = live_header.metadata.log_size + contents_offset;
            let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);

            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_single_write_crash(pm, incorruptible_bool_pos as int, ib_bytes);
            assert(perm.check_permission(pm));

            let new_pm = update_contents_to_reflect_write(pm, incorruptible_bool_pos as int, ib_bytes);
            lemma_headers_unchanged(pm, new_pm);
            assert(new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= ib_bytes);

            let new_header = spec_bytes_to_header(new_header_bytes);
            let (ib, headers, data) = pm_to_views(new_pm);
            let header_pos = if new_ib == cdb0_val {
                header1_pos
            } else {
                header2_pos
            };
            assert(new_pm.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes);
            lemma_header_match(new_pm, header_pos as int, new_header);
            lemma_header_correct(new_pm, new_header_bytes, header_pos as int);

            // prove that new pm has the append update
            let new_log_state = UntrustedLogImpl::recover(new_pm);
            let old_log_state = UntrustedLogImpl::recover(pm);

            match (new_log_state, old_log_state) {
                (Some(new_log_state), Some(old_log_state)) => {
                    lemma_pm_state_header(new_pm);
                    lemma_pm_state_header(pm);

                    let old_header = spec_get_live_header(pm);
                    let live_header = spec_get_live_header(new_pm);
                    assert(live_header == new_header);

                    assert(live_header.metadata.head == old_header.metadata.head);
                    assert(live_header.metadata.tail == old_header.metadata.tail + bytes_to_append.len());

                    let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                    let new_physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                    let old_physical_tail = spec_addr_logical_to_physical(old_header.metadata.tail as int, old_header.metadata.log_size as int);
                    assert(old_physical_tail == physical_tail);

                    let (_, _, old_data) = pm_to_views(pm);
                    let (_, _, new_data) = pm_to_views(pm);

                    if physical_head <= old_physical_tail {
                        if old_physical_tail + append_size >= contents_end {
                            assert(new_log_state.log =~= new_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) +
                                                        new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) +
                                                        new_data.subrange(0, new_physical_tail - contents_offset));
                            assert(new_log_state.log =~= old_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) +
                                                        new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) +
                                                        new_data.subrange(0, new_physical_tail - contents_offset));
                            let len1 = (contents_end - old_physical_tail);
                            let len2 = bytes_to_append.len() - len1;
                            assert(bytes_to_append =~= new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) +
                                                        new_data.subrange(0, new_physical_tail - contents_offset));
                            assert(new_log_state.log =~= old_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) + bytes_to_append);
                        } else {
                            assert(old_data.subrange(0, old_physical_tail - contents_offset) =~= new_data.subrange(0, old_physical_tail - contents_offset));
                            assert(new_data.subrange(old_physical_tail - contents_offset, old_physical_tail - contents_offset + append_size) =~= bytes_to_append);
                        }
                    } else { // physical_tail < physical_head
                        assert(old_physical_tail + append_size < physical_head);
                    }
                    assert(new_log_state =~= old_log_state.append(bytes_to_append));
                    assert(perm.check_permission(new_pm));
                }
                _ => assert(false),
            }
        }

        pub open spec fn live_data_view_eq(old_pm: Seq<u8>, new_pm: Seq<u8>) -> bool
        {
            let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
            let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
            let old_live_header = spec_get_live_header(old_pm);
            let new_live_header = spec_get_live_header(new_pm);
            let physical_head = spec_addr_logical_to_physical(old_live_header.metadata.head as int, old_live_header.metadata.log_size as int);
            let physical_tail = spec_addr_logical_to_physical(old_live_header.metadata.tail as int, old_live_header.metadata.log_size as int);
            let log_size = old_live_header.metadata.log_size;
            let physical_data_head = physical_head - contents_offset;
            let physical_data_tail = physical_tail - contents_offset;

            &&& new_live_header == old_live_header
            &&& physical_head < physical_tail ==>
                    old_data.subrange(physical_data_head, physical_data_tail) =~= new_data.subrange(physical_data_head, physical_data_tail)
            &&& physical_tail < physical_head ==> {
                    &&& old_data.subrange(physical_data_head as int, log_size as int) =~= new_data.subrange(physical_data_head as int, log_size as int)
                    &&& old_data.subrange(0, physical_data_tail as int) =~= new_data.subrange(0, physical_data_tail as int)
            }
            &&& physical_tail == physical_head ==>
                    physical_data_head == physical_data_tail
        }

        pub proof fn lemma_same_log_state(old_pm: Seq<u8>, new_pm: Seq<u8>)
            requires
                UntrustedLogImpl::recover(old_pm).is_Some(),
                UntrustedLogImpl::recover(new_pm).is_Some(),
                live_data_view_eq(old_pm, new_pm),
                ({
                    let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
                    let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                    &&& old_ib == cdb0_val || old_ib == cdb1_val
                    &&& old_ib == new_ib
                    &&& old_ib == cdb0_val ==> {
                        &&& old_headers.header1 == new_headers.header1
                    }
                    &&& old_ib == cdb1_val ==> {
                        &&& old_headers.header2 == new_headers.header2
                    }
                })
            ensures
                UntrustedLogImpl::recover(old_pm) =~=
                    UntrustedLogImpl::recover(new_pm)
        {
            let old_state = UntrustedLogImpl::recover(old_pm);
            let new_state = UntrustedLogImpl::recover(new_pm);
            let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
            let (new_ib, new_headers, new_data) = pm_to_views(new_pm);

            assert(old_state.is_Some());
            assert(new_state.is_Some());
            match (old_state, new_state) {
                (Some(old_state), Some(new_state)) => {
                    let (old_live_header, new_live_header) = if old_ib == cdb0_val {
                        (old_headers.header1, new_headers.header1)
                    } else {
                        (old_headers.header2, new_headers.header2)
                    };

                    assert(old_state.head == old_live_header.metadata.head);
                    assert(new_state.head == new_live_header.metadata.head);
                    assert(old_live_header.metadata.tail == new_live_header.metadata.tail);
                    let physical_head = spec_addr_logical_to_physical(old_live_header.metadata.head as int, old_live_header.metadata.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(old_live_header.metadata.tail as int, old_live_header.metadata.log_size as int);
                    let contents_end = old_live_header.metadata.log_size + contents_offset;

                    if physical_head < physical_tail {
                        assert(old_pm.subrange(physical_head, physical_tail) =~= old_data.subrange(physical_head - contents_offset, physical_tail - contents_offset));
                        assert(old_pm.subrange(physical_head, physical_tail) =~= new_pm.subrange(physical_head, physical_tail));
                    } else if physical_tail < physical_head {
                        assert(old_pm.subrange(physical_head, contents_end) =~= old_data.subrange(physical_head - contents_offset, contents_end - contents_offset));
                        assert(old_pm.subrange(contents_offset as int, physical_tail) =~= old_data.subrange(contents_offset - contents_offset, physical_tail - contents_offset));
                        assert(old_pm.subrange(physical_head, contents_end) + old_pm.subrange(contents_offset as int, physical_tail) =~=
                            new_pm.subrange(physical_head, contents_end) + new_pm.subrange(contents_offset as int, physical_tail));
                    } else {
                        assert(physical_head == physical_tail);
                        assert(old_state.log.len() == 0);
                        assert(new_state.log.len() == 0);
                    }
                }
                _ => assert(false),
            }
        }

        pub proof fn lemma_subrange_equality_implies_index_equality<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
            requires
                0 <= i <= j <= s1.len(),
                j <= s2.len(),
                s1.subrange(i, j) == s2.subrange(i, j)
            ensures
                forall |k| i <= k < j ==> s1[k] == s2[k]
        {
            assert forall |k| i <= k < j implies s1[k] == s2[k] by {
                // Trigger axiom_seq_subrange_index
                assert (s1[k] == s1.subrange(i, j)[k - i]);
                assert (s2[k] == s2.subrange(i, j)[k - i]);
            }
        }

        pub proof fn lemma_subrange_equality_implies_subsubrange_equality<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
            requires
                0 <= i <= j <= s1.len(),
                j <= s2.len(),
                s1.subrange(i, j) == s2.subrange(i, j)
            ensures
                forall |k, m| i <= k <= m <= j ==> s1.subrange(k, m) == s2.subrange(k, m)
        {
            lemma_subrange_equality_implies_index_equality(s1, s2, i, j);
            assert forall |k, m| i <= k <= m <= j implies s1.subrange(k, m) == s2.subrange(k, m) by {
                assert (s1.subrange(k, m) =~= s2.subrange(k, m));
            }
        }

        pub proof fn lemma_subrange_equality_implies_subsubrange_equality_forall<T>()
            ensures
                forall |s1: Seq<T>, s2: Seq<T>, i: int, j: int, k: int, m: int|
                    {
                        &&& 0 <= i <= j <= s1.len()
                        &&& j <= s2.len()
                        &&& s1.subrange(i, j) == s2.subrange(i, j)
                        &&& i <= k <= m <= j
                    }
                    ==> s1.subrange(k, m) == s2.subrange(k, m)
        {
            assert forall |s1: Seq<T>, s2: Seq<T>, i: int, j: int, k: int, m: int|
                       {
                           &&& 0 <= i <= j <= s1.len()
                           &&& j <= s2.len()
                           &&& s1.subrange(i, j) == s2.subrange(i, j)
                           &&& i <= k <= m <= j
                       }
                       implies s1.subrange(k, m) == s2.subrange(k, m) by {
                lemma_subrange_equality_implies_subsubrange_equality(s1, s2, i, j);
            }
        }

        pub proof fn lemma_headers_unchanged(old_pm: Seq<u8>, new_pm: Seq<u8>)
            requires
                old_pm.len() == new_pm.len(),
                old_pm.len() >= contents_offset,
                old_pm.subrange(header1_pos as int, header1_pos + header_size) =~= new_pm.subrange(header1_pos as int, header1_pos + header_size),
                old_pm.subrange(header2_pos as int, header2_pos + header_size) =~= new_pm.subrange(header2_pos as int, header2_pos + header_size),
            ensures
                ({
                    let (_, old_headers, _) = pm_to_views(old_pm);
                    let (_, new_headers, _) = pm_to_views(new_pm);
                    old_headers == new_headers
                })
        {
            lemma_subrange_equality_implies_subsubrange_equality_forall::<u8>();
        }

        pub proof fn lemma_incorruptible_bool_unchanged(old_pm: Seq<u8>, new_pm: Seq<u8>)
            requires
                old_pm.len() == new_pm.len(),
                old_pm.len() >= contents_offset,
                old_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8)
            ensures
                ({
                    let (old_ib, _, _) = pm_to_views(old_pm);
                    let (new_ib, _, _) = pm_to_views(new_pm);
                    old_ib == new_ib
                })
        {}

        pub proof fn lemma_header_crc_correct(header_bytes: Seq<u8>, crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>)
            requires
                header_bytes.len() == header_size,
                crc_bytes.len() == 8,
                metadata_bytes.len() == header_size - 8,
                crc_bytes =~= spec_crc_bytes(metadata_bytes),
                header_bytes =~= crc_bytes + metadata_bytes
            ensures
                header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= crc_bytes,
                header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes,
                header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~=
                    spec_crc_bytes(header_bytes.subrange(header_head_offset as int, header_size as int))
        {
            assert(header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= crc_bytes);
            assert(header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes);
        }

        pub proof fn lemma_header_correct(pm: Seq<u8>, header_bytes: Seq<u8>, header_pos: int)
            requires
                pm.len() > contents_offset,
                header_bytes.len() == header_size,
                header_pos == header1_pos || header_pos == header2_pos,
                header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~=
                    spec_crc_bytes(header_bytes.subrange(header_head_offset as int, header_size as int)),
                pm.subrange(header_pos, header_pos + header_size) =~= header_bytes
            ensures
                pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~=
                    header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8),
                pm.subrange(header_pos + header_head_offset, header_pos + header_size) =~=
                    header_bytes.subrange(header_head_offset as int, header_size as int),
                pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~=
                    spec_crc_bytes(pm.subrange(header_pos + header_head_offset, header_pos + header_size))
        {
            assert(pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~=
                header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8));
            assert(pm.subrange(header_pos + header_head_offset, header_pos + header_size) =~=
                header_bytes.subrange(header_head_offset as int, header_size as int));
        }

        pub proof fn lemma_u64_bytes_eq(val1: u64, val2: u64)
            requires
                val1 == val2
            ensures
                spec_u64_to_le_bytes(val1) =~= spec_u64_to_le_bytes(val2)
        {}

        pub proof fn lemma_subrange_eq<T>(bytes1: Seq<T>, bytes2: Seq<T>)
            requires
                bytes1 =~= bytes2
            ensures
                forall |i: int, j: int| 0 <= i < j < bytes1.len() ==> bytes1.subrange(i, j) =~= bytes2.subrange(i, j)
        {}

        /// If our write is persistence_chunk_size-sized and -aligned, then there are only 2 possible
        /// resulting crash states, one with the write and one without.
        pub proof fn lemma_single_write_crash(pm: Seq<u8>, write_addr: int, bytes_to_write: Seq<u8>)
            requires
                bytes_to_write.len() == persistence_chunk_size,
                write_addr % persistence_chunk_size == 0, // currently seems to succeed without nonlinear arith
                0 <= write_addr < pm.len(),
                write_addr + bytes_to_write.len() <= pm.len()
            ensures
                ({
                    forall |chunks_flushed: Set<int>| {
                        let new_crash_contents = #[trigger] update_contents_to_reflect_partially_flushed_write(
                            pm, write_addr, bytes_to_write, chunks_flushed);
                        let new_contents = update_contents_to_reflect_write(pm, write_addr, bytes_to_write);
                        new_crash_contents =~= pm || new_crash_contents =~= new_contents
                    }
                })
        {}

        pub proof fn lemma_pm_state_header(pm: Seq<u8>)
            requires
                UntrustedLogImpl::recover(pm).is_Some(),
                ({
                    let header = spec_get_live_header(pm);
                    header.metadata.tail - header.metadata.head < header.metadata.log_size
                })
            ensures
                ({
                    let pm_state = UntrustedLogImpl::recover(pm);
                    let header = spec_get_live_header(pm);
                    match pm_state {
                        Some(pm_state) => {
                            &&& header.metadata.head == pm_state.head
                            &&& pm_state.log.len() == header.metadata.tail - header.metadata.head
                        }
                        None => false
                    }
                })
        {
            let pm_state = UntrustedLogImpl::recover(pm);
            let header = spec_get_live_header(pm);
            lemma_mod_range(header.metadata.head as int, header.metadata.log_size as int);
            lemma_mod_range(header.metadata.tail as int, header.metadata.log_size as int);
            let head = header.metadata.head as int;
            let tail = header.metadata.tail as int;
            let log_size = header.metadata.log_size as int;
            let physical_head = spec_addr_logical_to_physical(head, log_size);
            let physical_tail = spec_addr_logical_to_physical(tail, log_size);
            match pm_state {
                Some(pm_state) => {
                    if physical_head < physical_tail {
                        // log does not wrap
                        lemma_mod_difference_equal(head, tail, log_size);
                    } else if physical_tail < physical_head {
                        // log wraps
                        lemma_mod_wrapped_len(head, tail, log_size);
                    } else {
                        // size is 0
                        lemma_mod_equal(head, tail, log_size);
                    }
                }
                None => assert(false),
            }
        }

        pub open spec fn spec_addr_logical_to_physical(addr: int, log_size: int) -> int {
            (addr % log_size) + contents_offset
        }

        pub struct UntrustedLogImpl {
            pub incorruptible_bool: u64,
            // header fields are stored separately because of limitations
            // on deriving Copy/Clone for the header structures
            pub header_crc: u64,
            pub head: u64,
            pub tail: u64,
            pub log_size: u64,
        }

        // offset of actual log contents from the beginning of the device
        pub const contents_offset: u64 = header2_pos + header_log_size_offset + 8;

        impl UntrustedLogImpl {

            pub exec fn addr_logical_to_physical(addr: u64, log_size: u64) -> (out: u64)
                requires
                    addr <= u64::MAX,
                    log_size > 0,
                    log_size + contents_offset <= u64::MAX,
                ensures
                    out == spec_addr_logical_to_physical(addr as int, log_size as int)
            {
                (addr % log_size) + contents_offset
            }

            pub open spec fn log_state_is_valid(pm: Seq<u8>) -> bool {
                let (ib, headers, data) = pm_to_views(pm);
                let live_header = if ib == cdb0_val {
                    headers.header1
                } else {
                    headers.header2
                };

                let head = live_header.metadata.head as int;
                let tail = live_header.metadata.tail as int;
                let log_size = live_header.metadata.log_size as int;

                &&& ib == cdb0_val || ib == cdb1_val
                &&& log_size + contents_offset <= u64::MAX
                &&& log_size > 0
                &&& log_size + contents_offset == pm.len()
                &&& tail - head < log_size
                &&& ib == cdb0_val ==> {
                        &&& live_header.crc == spec_u64_from_le_bytes(spec_crc_bytes(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size)))
                        &&& pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~= spec_crc_bytes(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size))
                    }
                &&& ib == cdb1_val ==> {
                    &&& live_header.crc == spec_u64_from_le_bytes(spec_crc_bytes(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size)))
                    &&& pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~= spec_crc_bytes(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size))
                }
                &&& head <= tail
            }

            pub open spec fn recover(pm: Seq<u8>) -> Option<AbstractInfiniteLogState>
            {
                let (ib, headers, data) = pm_to_views(pm);
                if !Self::log_state_is_valid(pm) {
                    None
                } else {
                    let live_header = if ib == cdb0_val {
                        headers.header1
                    } else {
                        headers.header2
                    };

                    let head = live_header.metadata.head as int;
                    let tail = live_header.metadata.tail as int;
                    let log_size = live_header.metadata.log_size as int;
                    let contents_end = log_size + contents_offset;
                    let physical_head = spec_addr_logical_to_physical(head, log_size);
                    let physical_tail = spec_addr_logical_to_physical(tail, log_size);

                    let abstract_log = if physical_head < physical_tail {
                        pm.subrange(physical_head, physical_tail)
                    } else if physical_tail < physical_head {
                        let range1 = pm.subrange(physical_head, contents_end);
                        let range2 = pm.subrange(contents_offset as int, physical_tail);
                        range1 + range2
                    } else {
                        Seq::empty()
                    };

                    Some(AbstractInfiniteLogState { head: head, log: abstract_log, capacity: log_size - 1 })
                }
            }

            // This is the invariant that the untrusted log implementation
            // maintains between its local state and the contents of
            // persistent memory.
            pub open spec fn inv_pm_contents(self, contents: Seq<u8>) -> bool
            {
                let (ib, headers, data) = pm_to_views(contents);
                let header_pos = if ib == cdb0_val { header1_pos } else { header2_pos };
                let header = spec_get_live_header(contents);
                let head = header.metadata.head;
                let tail = header.metadata.tail;
                let log_size = header.metadata.log_size;
                &&& ib == cdb0_val || ib == cdb1_val
                &&& spec_crc_bytes(contents.subrange(header_pos + header_head_offset, header_pos + header_size)) ==
                      contents.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8)
                &&& log_size + contents_offset <= u64::MAX
                &&& tail - head < log_size
                &&& log_size + contents_offset == contents.len()
                &&& self.header_crc == header.crc
                &&& self.head == head
                &&& self.tail == tail
                &&& self.log_size == log_size
                &&& self.incorruptible_bool == ib
                &&& match Self::recover(contents) {
                       Some(inf_log) => tail == head + inf_log.log.len(),
                       None => false,
                   }
            }

            // This is the invariant that the untrusted log implementation
            // maintains between its local state and the write-restricted
            // persistent memory.
            pub open spec fn inv<Perm, PM>(self, wrpm: &WriteRestrictedPersistentMemory<Perm, PM>) -> bool
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
            {
                &&& wrpm.inv()
                &&& self.inv_pm_contents(wrpm@)
            }

            pub exec fn read_incorruptible_boolean<PM: PersistentMemory>(pm: &PM) -> (result: Result<u64, InfiniteLogErr>)
                requires
                    Self::recover(pm@).is_Some(),
                    pm.inv(),
                    pm@.len() > contents_offset
                ensures
                    match result {
                        Ok(ib) => {
                            let (spec_ib, _, _) = pm_to_views(pm@);
                            ib == spec_ib
                        }
                        Err(InfiniteLogErr::CRCMismatch) => !pm.constants().impervious_to_corruption,
                        _ => false,
                    }
            {
                let bytes = pm.read(incorruptible_bool_pos, 8);
                let ib = u64_from_le_bytes(bytes.as_slice());
                let ghost addrs = Seq::<int>::new(8, |i: int| i + incorruptible_bool_pos);
                if ib == cdb0_val || ib == cdb1_val {
                    proof {
                        let (spec_ib, _, _) = pm_to_views(pm@);
                        lemma_auto_spec_u64_to_from_le_bytes();
                        if !pm.constants().impervious_to_corruption {
                            axiom_corruption_detecting_boolean(ib, spec_ib, addrs);
                        }
                    }
                    Ok(ib)
                } else {
                    Err(InfiniteLogErr::CRCMismatch)
                }
            }

            exec fn update_header<Perm, PM>
            (
                &mut self,
                wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                Tracked(perm): Tracked<&Perm>,
                new_header_bytes: &Vec<u8>
            )
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    permissions_depend_only_on_recovery_view(perm),
                    contents_offset < old(wrpm)@.len(),
                    old(self).inv(&*old(wrpm)),
                    Self::recover(old(wrpm)@).is_Some(),
                    new_header_bytes@.subrange(header_crc_offset as int, header_crc_offset + 8) =~=
                        spec_crc_bytes(new_header_bytes@.subrange(header_head_offset as int, header_size as int)),
                    new_header_bytes.len() == header_size,
                    match Self::recover(old(wrpm)@) {
                        Some(log_state) => perm.check_permission(old(wrpm)@),
                        None => false
                    }
                ensures
                    self.inv(wrpm),
                    Self::recover(wrpm@).is_Some(),
                    wrpm.constants() == old(wrpm).constants(),
                    match (Self::recover(old(wrpm)@), Self::recover(wrpm@)) {
                        (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                        _ => false
                    },
                    ({
                        let (old_pm_ib, old_metadata, old_data) = pm_to_views(old(wrpm)@);
                        let (new_pm_ib, new_metadata, new_data) = pm_to_views(wrpm@);
                        let new_header = spec_bytes_to_header(new_header_bytes@);
                        &&& old_pm_ib == new_pm_ib
                        &&& old_pm_ib == cdb0_val ==> {
                            &&& new_metadata.header1 == old_metadata.header1
                            &&& new_metadata.header2 == new_header
                            &&& wrpm@.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~=
                                    spec_crc_bytes(wrpm@.subrange(header2_pos + header_head_offset, header2_pos + header_size))
                            &&& wrpm@.subrange(header2_pos as int, header2_pos + header_size) =~= new_header_bytes@
                        }
                        &&& old_pm_ib == cdb1_val ==> {
                            &&& new_metadata.header1 == new_header
                            &&& new_metadata.header2 == old_metadata.header2
                            &&& wrpm@.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~=
                                    spec_crc_bytes(wrpm@.subrange(header1_pos + header_head_offset, header1_pos + header_size))
                            &&& wrpm@.subrange(header1_pos as int, header1_pos + header_size) =~= new_header_bytes@
                        }
                        &&& old_data =~= new_data
                    }),

            {
                let ghost original_wrpm = wrpm@;

                // write to the header that is NOT pointed to by the IB
                let header_pos = if self.incorruptible_bool == cdb0_val {
                    header2_pos
                } else {
                    header1_pos
                };

                // TODO: we could probably roll all of this into a single lemma that contains all of the proofs
                proof {
                    let new_pm = update_contents_to_reflect_write(wrpm@, header_pos as int, new_header_bytes@);
                    lemma_inactive_header_update_view(wrpm@, new_header_bytes@, header_pos as int);
                    lemma_same_log_state(wrpm@, new_pm);
                    assert(Self::recover(wrpm@) =~= Self::recover(new_pm));

                    // prove crash consistency
                    assert forall |chunks_flushed| {
                        let new_pm = #[trigger] update_contents_to_reflect_partially_flushed_write(
                            wrpm@, header_pos as int, new_header_bytes@, chunks_flushed);
                        perm.check_permission(new_pm)
                    } by {
                        let new_pm = update_contents_to_reflect_partially_flushed_write(
                            wrpm@, header_pos as int, new_header_bytes@, chunks_flushed);
                        lemma_inactive_header_update_view_crash(wrpm@, new_header_bytes@, header_pos as int, chunks_flushed);
                        lemma_same_log_state(wrpm@, new_pm);
                        assert(permissions_depend_only_on_recovery_view(perm));
                        lemma_same_permissions(wrpm@, new_pm, perm);
                    }
                }
                wrpm.write(header_pos, new_header_bytes.as_slice(), Tracked(perm));
                proof {
                    // TODO: clean up once ib update is done. put this all in a lemma
                    assert(Self::recover(wrpm@).is_Some());
                    let (_, headers, _) = pm_to_views(wrpm@);
                    assert(wrpm@.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes@);
                    lemma_header_correct(wrpm@, new_header_bytes@, header_pos as int);

                    // live header is unchanged
                    let live_header_pos = if header_pos == header1_pos {
                        header2_pos
                    } else {
                        assert(header_pos == header2_pos);
                        header1_pos
                    };

                    // TODO: refactor into a lemma (ideally lemma_header_correct)
                    assert(old(wrpm)@.subrange(live_header_pos as int, live_header_pos + header_size) =~=
                            wrpm@.subrange(live_header_pos as int, live_header_pos + header_size));
                    assert(old(wrpm)@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~=
                        spec_crc_bytes(old(wrpm)@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size)));
                    assert(old(wrpm)@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~=
                        wrpm@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8));
                    assert(old(wrpm)@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size) =~=
                        wrpm@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size));

                    assert(wrpm@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~=
                        spec_crc_bytes(wrpm@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size)));
                }
            }

            // Since untrusted_setup doesn't take a WriteRestrictedPersistentMemory, it is not guaranteed
            // to perform crash-safe updates.
            pub exec fn untrusted_setup<PM>(pm: &mut PM, device_size: u64) -> (result: Result<u64, InfiniteLogErr>)
                where
                    PM: PersistentMemory
                requires
                    old(pm).inv(),
                    old(pm)@.len() == device_size
                ensures
                    pm.inv(),
                    pm.constants() == old(pm).constants(),
                    pm@.len() == device_size,
                    match result {
                        Ok(capacity) => Self::recover(pm@) ==
                                    Some(AbstractInfiniteLogState::initialize(capacity as int)),
                        Err(InfiniteLogErr::InsufficientSpaceForSetup{ required_space }) => device_size < required_space,
                        _ => false
                    }
            {
                if device_size <= contents_offset {
                    return Err(InfiniteLogErr::InsufficientSpaceForSetup { required_space: contents_offset + 1 });
                }

                let log_size = device_size - contents_offset;

                let log_header_metadata = PersistentHeaderMetadata {
                    head: 0,
                    tail: 0,
                    log_size
                };
                let metadata_bytes = metadata_to_bytes(&log_header_metadata);
                let crc_bytes = bytes_crc(&metadata_bytes);
                let log_header = PersistentHeader {
                    crc: u64_from_le_bytes(crc_bytes.as_slice()),
                    metadata: log_header_metadata,
                };
                let header_bytes = header_to_bytes(&log_header);

                let initial_ib_bytes = u64_to_le_bytes(cdb0_val);
                pm.write(header1_pos, header_bytes.as_slice());
                pm.write(incorruptible_bool_pos, initial_ib_bytes.as_slice());

                proof {
                    lemma_auto_spec_u64_to_from_le_bytes();
                    assert(pm@.subrange(header1_pos as int, header1_pos + header_size) =~= header_bytes@);
                    assert(pm@.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= initial_ib_bytes@);
                    lemma_header_split_into_bytes(crc_bytes@, metadata_bytes@, header_bytes@);
                    assert(pm@.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~= metadata_bytes@);
                    lemma_header_match(pm@, header1_pos as int, log_header);
                    let log_state = Self::recover(pm@);
                    match log_state {
                        Some(log_state) => {
                            assert(log_state.head == 0);
                            assert(log_state.log == Seq::<u8>::empty());
                            assert(log_state.capacity == log_size - 1);
                        }
                        None => assert(false),
                    }
                }

                Ok(log_size - 1)
            }

            pub exec fn untrusted_start<Perm, PM>(wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                                                  device_size: u64,
                                                  Tracked(perm): Tracked<&Perm>)
                                                  -> (result: Result<UntrustedLogImpl, InfiniteLogErr>)
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    Self::recover(old(wrpm)@).is_Some(),
                    old(wrpm).inv(),
                    old(wrpm)@.len() == device_size,
                    header_crc_offset < header_crc_offset + crc_size <= header_head_offset < header_tail_offset < header_log_size_offset,
                    // The restriction on writing persistent memory during initialization is
                    // that it can't change the interpretation of that memory's contents.
                    ({
                        forall |pm_state| #[trigger] perm.check_permission(pm_state) <==>
                            Self::recover(pm_state) ==
                            Self::recover(old(wrpm)@)
                    }),
                ensures
                    Self::recover(old(wrpm)@) == Self::recover(wrpm@),
                    wrpm.constants() == old(wrpm).constants(),
                    match result {
                        Ok(log_impl) => log_impl.inv(wrpm),
                        Err(InfiniteLogErr::CRCMismatch) => !wrpm.constants().impervious_to_corruption,
                        _ => false
                    }
            {
                let pm = wrpm.get_pm_ref();
                assert (device_size > contents_offset);

                let ib = match Self::read_incorruptible_boolean(pm) {
                    Ok(ib) => ib,
                    Err(e) => return Err(e)
                };

                let header_pos = if ib == cdb0_val {
                    header1_pos
                } else {
                    assert(ib == cdb1_val);
                    header2_pos
                };
                let crc_bytes = pm.read(header_pos + header_crc_offset, 8);
                let ghost crc_addrs = Seq::<int>::new(8, |i: int| i + header_pos + header_crc_offset);
                let header_bytes = pm.read(header_pos + header_head_offset, header_size - header_head_offset);
                let ghost header_addrs = Seq::<int>::new((header_size - header_head_offset) as nat, |i: int| i + header_pos + header_head_offset);

                let header = if u64_from_le_bytes(bytes_crc(&header_bytes).as_slice()) == u64_from_le_bytes(crc_bytes.as_slice()) {
                    proof {
                        lemma_auto_spec_u64_to_from_le_bytes();
                        lemma_u64_bytes_eq(spec_u64_from_le_bytes(spec_crc_bytes(header_bytes@)), spec_u64_from_le_bytes(crc_bytes@));
                        if !wrpm.constants().impervious_to_corruption {
                            axiom_bytes_uncorrupted(
                                header_bytes@,
                                pm@.subrange(header_pos + header_head_offset, header_pos + header_size),
                                header_addrs,
                                crc_bytes@,
                                pm@.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8),
                                crc_addrs,
                            );
                        }
                    }
                    crc_and_metadata_bytes_to_header(crc_bytes.as_slice(), header_bytes.as_slice())
                } else {
                    return Err(InfiniteLogErr::CRCMismatch);
                };

                let head = header.metadata.head;
                let tail = header.metadata.tail;
                let log_size = header.metadata.log_size;
                // check log validity now that we have its uncorrupted metadata
                assert(device_size == log_size + contents_offset);
                assert(head <= tail);
                assert(tail - head < log_size);

                let untrusted_log = UntrustedLogImpl {
                    incorruptible_bool: ib,
                    header_crc: u64_from_le_bytes(crc_bytes.as_slice()),
                    head,
                    tail,
                    log_size
                };

                proof { lemma_pm_state_header(pm@); }
                Ok(untrusted_log)
            }

            pub exec fn untrusted_append<Perm, PM>(
                &mut self,
                wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                bytes_to_append: &Vec<u8>,
                Tracked(perm): Tracked<&Perm>
            ) -> (result: Result<u64, InfiniteLogErr>)
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    old(self).inv(&*old(wrpm)),
                    Self::recover(old(wrpm)@).is_Some(),
                    ({
                        let old_log_state = Self::recover(old(wrpm)@);
                        forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                            let log_state = Self::recover(pm_state);
                            log_state == old_log_state || log_state == Some(old_log_state.unwrap().append(bytes_to_append@))
                        }
                    }),
                ensures
                    self.inv(wrpm),
                    wrpm.constants() == old(wrpm).constants(),
                    ({
                        let old_log_state = Self::recover(old(wrpm)@);
                        let new_log_state = Self::recover(wrpm@);
                        match (result, old_log_state, new_log_state) {
                            (Ok(offset), Some(old_log_state), Some(new_log_state)) => {
                                &&& offset as nat == old_log_state.log.len() + old_log_state.head
                                &&& new_log_state == old_log_state.append(bytes_to_append@)
                            },
                            (Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space }), _, _) => {
                                &&& new_log_state == old_log_state
                                &&& available_space < bytes_to_append@.len()
                                &&& {
                                       let log = old_log_state.unwrap();
                                       ||| available_space == log.capacity - log.log.len()
                                       ||| available_space == u64::MAX - log.head - log.log.len()
                                   }
                            },
                            (_, _, _) => false
                        }
                    }),
            {
                assert(permissions_depend_only_on_recovery_view(perm));

                let pm = wrpm.get_pm_ref();
                let ghost original_pm = wrpm@;

                let physical_head = Self::addr_logical_to_physical(self.head, self.log_size);
                let physical_tail = Self::addr_logical_to_physical(self.tail, self.log_size);
                let contents_end = self.log_size + contents_offset;
                let append_size: u64 = bytes_to_append.len() as u64;
                let old_logical_tail = self.tail;

                if self.tail > u64::MAX - append_size {
                    Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space: u64::MAX - self.tail })
                }
                else if append_size >= self.log_size - (self.tail - self.head) {
                    Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space: self.log_size - 1 - (self.tail - self.head) })
                } else {
                    let mut header_metadata =
                        PersistentHeaderMetadata { head: self.head, tail: self.tail, log_size: self.log_size };
                    assert(header_metadata == spec_get_live_header(wrpm@).metadata);

                    if physical_head <= physical_tail {
                        if physical_tail >= contents_end - append_size {
                            // wrap case
                            self.append_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                        } else {
                            // no wrap
                            self.append_no_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                        }
                    } else { // physical_tail < physical_head
                        if physical_tail + append_size >= physical_head {
                            return Err(InfiniteLogErr::InsufficientSpaceForAppend { available_space: physical_head - physical_tail });
                        }
                        // no wrap
                        self.append_no_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                    }

                    let new_tail = self.tail + append_size;
                    header_metadata.tail = new_tail;

                    let mut metadata_bytes = metadata_to_bytes(&header_metadata);
                    let new_crc_bytes = bytes_crc(&metadata_bytes);
                    let new_crc_val = u64_from_le_bytes(new_crc_bytes.as_slice());
                    let ghost old_metadata_bytes = metadata_bytes@;
                    let mut new_header_bytes = new_crc_bytes;
                    new_header_bytes.append(&mut metadata_bytes);

                    proof { lemma_header_crc_correct(new_header_bytes@, new_crc_bytes@, old_metadata_bytes); }

                    self.update_header(wrpm, Tracked(perm), &new_header_bytes);

                    // update incorruptible boolean
                    let old_ib = self.incorruptible_bool;
                    let new_ib = if old_ib == cdb0_val {
                        cdb1_val
                    } else {
                        assert(old_ib == cdb1_val);
                        cdb0_val
                    };
                    let new_ib_bytes = u64_to_le_bytes(new_ib);

                    proof {
                        lemma_append_ib_update(wrpm@, new_ib, bytes_to_append@, new_header_bytes@, perm);
                    }

                    wrpm.write(incorruptible_bool_pos, new_ib_bytes.as_slice(), Tracked(perm));
                    self.incorruptible_bool = new_ib;
                    self.tail = new_tail;
                    self.header_crc = new_crc_val;

                    Ok(old_logical_tail)
                }
            }

            exec fn append_no_wrap<Perm, PM>(
                &mut self,
                wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                bytes_to_append: &Vec<u8>,
                old_header: &PersistentHeaderMetadata,
                Tracked(perm): Tracked<&Perm>
            )
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    permissions_depend_only_on_recovery_view(perm),
                    perm.check_permission(old(wrpm)@),
                    old(self).inv(&*old(wrpm)),
                    Self::recover(old(wrpm)@).is_Some(),
                    old_header == spec_get_live_header(old(wrpm)@).metadata,
                    // TODO: clean up
                    ({
                        let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                        physical_tail + bytes_to_append@.len() < old_header.log_size + contents_offset
                    }),
                    ({
                        let physical_head = spec_addr_logical_to_physical(old_header.head as int, old_header.log_size as int);
                        let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                        let contents_end = old_header.log_size + contents_offset;
                        &&& physical_head <= physical_tail ==> physical_tail + bytes_to_append@.len() < contents_end
                        &&& physical_tail < physical_head ==> physical_tail <= physical_tail + bytes_to_append@.len() < physical_head
                    })
                ensures
                    self.inv(wrpm),
                    wrpm.constants() == old(wrpm).constants(),
                    Self::recover(wrpm@).is_Some(),
                    match (Self::recover(old(wrpm)@), Self::recover(wrpm@)) {
                        (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                        _ => false
                    },
                    ({
                        let (old_ib, old_headers, old_data) = pm_to_views(old(wrpm)@);
                        let (new_ib, new_headers, new_data) = pm_to_views(wrpm@);
                        let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                        &&& old_ib == new_ib
                        &&& old_headers == new_headers
                        &&& new_data.subrange(physical_tail - contents_offset, physical_tail - contents_offset + bytes_to_append@.len() as int) =~= bytes_to_append@
                        &&& new_data.subrange(0, physical_tail - contents_offset) =~= old_data.subrange(0, physical_tail - contents_offset)
                        &&& new_data.subrange(physical_tail - contents_offset + bytes_to_append@.len(), new_data.len() as int) =~=
                                old_data.subrange(physical_tail - contents_offset + bytes_to_append@.len(), old_data.len() as int)
                    })
            {
                let physical_tail = Self::addr_logical_to_physical(old_header.tail, old_header.log_size);
                proof { lemma_data_write_is_safe(wrpm@, bytes_to_append@, physical_tail as int, perm); }
                wrpm.write(physical_tail, bytes_to_append.as_slice(), Tracked(perm));
                proof {
                    assert(wrpm@.subrange(0, physical_tail as int) =~= old(wrpm)@.subrange(0, physical_tail as int));
                    lemma_subrange_equality_implies_subsubrange_equality(wrpm@, old(wrpm)@, 0, physical_tail as int);
                }
            }

            pub exec fn append_wrap<Perm, PM>(
                &mut self,
                wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                bytes_to_append: &Vec<u8>,
                old_header: &PersistentHeaderMetadata,
                Tracked(perm): Tracked<&Perm>
            )
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    permissions_depend_only_on_recovery_view(perm),
                    perm.check_permission(old(wrpm)@),
                    old(self).inv(&*old(wrpm)),
                    Self::recover(old(wrpm)@).is_Some(),
                    old_header == spec_get_live_header(old(wrpm)@).metadata,
                    ({
                        let physical_head = spec_addr_logical_to_physical(old_header.head as int, old_header.log_size as int);
                        let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                        let contents_end = old_header.log_size + contents_offset;
                        &&& contents_offset < physical_head
                        &&& physical_tail + bytes_to_append@.len() >= contents_end
                        &&& physical_head <= physical_tail
                        &&& bytes_to_append@.len() <= old_header.log_size - (old_header.tail - old_header.head)
                    }),
                ensures
                    self.inv(wrpm),
                    Self::recover(wrpm@).is_Some(),
                    wrpm.constants() == old(wrpm).constants(),
                    match (Self::recover(old(wrpm)@), Self::recover(wrpm@)) {
                        (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                        _ => false
                    },
                    ({
                        let (old_ib, old_headers, old_data) = pm_to_views(old(wrpm)@);
                        let (new_ib, new_headers, new_data) = pm_to_views(wrpm@);
                        let contents_end = old_header.log_size + contents_offset;
                        let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                        let len1 = (contents_end - physical_tail);
                        let len2 = bytes_to_append@.len() - len1;
                        &&& old_ib == new_ib
                        &&& old_headers == new_headers
                        &&& new_data.subrange(physical_tail - contents_offset, contents_end - contents_offset) =~= bytes_to_append@.subrange(0, len1)
                        &&& new_data.subrange(0, len2 as int) =~= bytes_to_append@.subrange(len1 as int, bytes_to_append@.len() as int)
                        &&& new_data.subrange(len2 as int, physical_tail - contents_offset) =~= old_data.subrange(len2 as int, physical_tail - contents_offset)
                        &&& bytes_to_append@ =~= new_data.subrange(physical_tail - contents_offset, contents_end - contents_offset) + new_data.subrange(0, len2 as int)
                    })
            {
                let physical_head = Self::addr_logical_to_physical(old_header.head, old_header.log_size);
                let physical_tail = Self::addr_logical_to_physical(old_header.tail, old_header.log_size);
                let contents_end = old_header.log_size + contents_offset;
                let append_size = bytes_to_append.len();

                let len1 = (contents_end - physical_tail) as usize;
                let len2 = bytes_to_append.len() - len1;
                let append_bytes_slice = bytes_to_append.as_slice();
                let bytes1 = slice_subrange(append_bytes_slice, 0, len1);
                let bytes2 = slice_subrange(append_bytes_slice, len1, append_size);

                proof { lemma_data_write_is_safe(wrpm@, bytes1@, physical_tail as int, perm); }
                wrpm.write(physical_tail, bytes1, Tracked(perm));

                proof { lemma_data_write_is_safe(wrpm@, bytes2@, contents_offset as int, perm); }
                wrpm.write(contents_offset, bytes2, Tracked(perm));

                proof {
                    assert(wrpm@.subrange(0, contents_offset as int) =~= old(wrpm)@.subrange(0, contents_offset as int));
                    lemma_subrange_equality_implies_subsubrange_equality(wrpm@, old(wrpm)@, 0, contents_offset as int);
                }
            }

            pub exec fn untrusted_advance_head<Perm, PM>(
                &mut self,
                wrpm: &mut WriteRestrictedPersistentMemory<Perm, PM>,
                new_head: u64,
                Tracked(perm): Tracked<&Perm>
            ) -> (result: Result<(), InfiniteLogErr>)
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    old(self).inv(&*old(wrpm)),
                    Self::recover(old(wrpm)@).is_Some(),
                    ({
                        let old_log_state = Self::recover(old(wrpm)@);
                        forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                            let log_state = Self::recover(pm_state);
                            ||| log_state == old_log_state
                            ||| log_state == Some(old_log_state.unwrap().advance_head(new_head as int))
                        }
                    })
                ensures
                    self.inv(wrpm),
                    wrpm.constants() == old(wrpm).constants(),
                    ({
                        let old_log_state = Self::recover(old(wrpm)@);
                        let new_log_state = Self::recover(wrpm@);
                        match (result, old_log_state, new_log_state) {
                            (Ok(_), Some(old_log_state), Some(new_log_state)) => {
                                &&& old_log_state.head <= new_head <= old_log_state.head + old_log_state.log.len()
                                &&& new_log_state == old_log_state.advance_head(new_head as int)
                            },
                            (Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head }), Some(old_log_state), Some(new_log_state)) => {
                                &&& new_log_state == old_log_state
                                &&& head == old_log_state.head
                                &&& new_head < head
                            },
                            (Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail }), Some(old_log_state), Some(new_log_state)) => {
                                &&& new_log_state == old_log_state
                                &&& tail == old_log_state.head + old_log_state.log.len()
                                &&& new_head > tail
                            },
                            (_, _, _) => false
                        }
                    })
            {
                let pm = wrpm.get_pm_ref();
                let ghost original_pm = wrpm@;

                let live_header = PersistentHeader {
                    crc: self.header_crc,
                    metadata: PersistentHeaderMetadata { head: self.head, tail: self.tail, log_size: self.log_size }
                };

                if new_head < live_header.metadata.head {
                    assert(self.header_crc == old(self).header_crc);
                    return Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head: live_header.metadata.head });
                }

                if new_head > live_header.metadata.tail {
                    assert(self.header_crc == old(self).header_crc);
                    return Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail: live_header.metadata.tail });
                }

                // copy the header and update it
                let mut new_header = live_header;
                new_header.metadata.head = new_head;
                let mut metadata_bytes = metadata_to_bytes(&new_header.metadata);
                let new_crc_bytes = bytes_crc(&metadata_bytes);
                let new_crc_val = u64_from_le_bytes(new_crc_bytes.as_slice());
                let ghost old_metadata_bytes = metadata_bytes@;
                let mut new_header_bytes = new_crc_bytes;
                new_header_bytes.append(&mut metadata_bytes);

                proof { lemma_header_crc_correct(new_header_bytes@, new_crc_bytes@, old_metadata_bytes); }

                self.update_header(wrpm, Tracked(perm), &new_header_bytes);

                // TODO: put ib update in a lemma
                let old_ib = self.incorruptible_bool;
                let new_ib = if old_ib == cdb0_val {
                    cdb1_val
                } else {
                    assert(old_ib == cdb1_val);
                    cdb0_val
                };
                let new_ib_bytes = u64_to_le_bytes(new_ib);

                proof {
                    lemma_auto_spec_u64_to_from_le_bytes();
                    lemma_single_write_crash(wrpm@, incorruptible_bool_pos as int, new_ib_bytes@);
                    assert(perm.check_permission(old(wrpm)@));
                    let new_pm = update_contents_to_reflect_write(wrpm@, incorruptible_bool_pos as int, new_ib_bytes@);
                    lemma_headers_unchanged(wrpm@, new_pm);
                    assert(new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_ib_bytes@);

                    let new_header = spec_bytes_to_header(new_header_bytes@);
                    let (ib, headers, data) = pm_to_views(new_pm);
                    let header_pos = if new_ib == cdb0_val {
                        header1_pos
                    } else {
                        header2_pos
                    };
                    assert(new_pm.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes@);
                    lemma_header_match(new_pm, header_pos as int, new_header);
                    lemma_header_correct(new_pm, new_header_bytes@, header_pos as int);

                    // prove that new pm has the advance head update
                    let new_log_state = Self::recover(new_pm);
                    let old_log_state = Self::recover(old(wrpm)@);
                    match (new_log_state, old_log_state) {
                        (Some(new_log_state), Some(old_log_state)) => {
                            lemma_pm_state_header(new_pm);
                            lemma_pm_state_header(old(wrpm)@);
                            assert(new_log_state =~= old_log_state.advance_head(new_head as int));
                            assert(perm.check_permission(new_pm));
                        }
                        _ => assert(false),
                    }
                }

                wrpm.write(incorruptible_bool_pos, new_ib_bytes.as_slice(), Tracked(perm));
                self.incorruptible_bool = new_ib;
                self.head = new_head;
                self.header_crc = new_crc_val;

                Ok(())
            }

            pub exec fn untrusted_read<Perm, PM>(
                &self,
                wrpm: &WriteRestrictedPersistentMemory<Perm, PM>,
                pos: u64,
                len: u64
            ) -> (result: Result<Vec<u8>, InfiniteLogErr>)
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    self.inv(wrpm),
                    Self::recover(wrpm@).is_Some(),
                ensures
                    ({
                        let log = Self::recover(wrpm@).unwrap();
                        match result {
                            Ok(bytes) => {
                                let true_bytes = log.log.subrange(pos - log.head, pos + len - log.head);
                                &&& pos >= log.head
                                &&& pos + len <= log.head + log.log.len()
                                &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                                 wrpm.constants().impervious_to_corruption)
                            },
                            Err(InfiniteLogErr::CantReadBeforeHead{ head: head_pos }) => {
                                &&& pos < log.head
                                &&& head_pos == log.head
                            },
                            Err(InfiniteLogErr::CantReadPastTail{ tail }) => {
                                &&& pos + len > log.head + log.log.len()
                                &&& tail == log.head + log.log.len()
                            },
                            _ => false
                        }
                    })
            {
                let pm = wrpm.get_pm_ref();
                let physical_pos = Self::addr_logical_to_physical(pos, self.log_size);
                let contents_end = self.log_size + contents_offset;
                if pos < self.head {
                    Err(InfiniteLogErr::CantReadBeforeHead{ head: self.head })
                } else if pos > u64::MAX - len {
                    Err(InfiniteLogErr::CantReadPastTail{ tail: self.tail })
                } else if pos + len > self.tail {
                    Err(InfiniteLogErr::CantReadPastTail{ tail: self.tail })
                } else {
                    proof {
                        // we get a type error if we calculate physical head and tail in non-ghost code and use them here,
                        // so we need to calculate them here for the proof and again later for execution
                        let physical_head = spec_addr_logical_to_physical(self.head as int, self.log_size as int);
                        let physical_tail = spec_addr_logical_to_physical(self.tail as int, self.log_size as int);
                        if physical_head == physical_tail {
                            lemma_mod_equal(self.head as int, self.tail as int, self.log_size as int);
                            assert(len == 0);
                        } else if physical_head < physical_tail {
                            // read cannot wrap around
                            lemma_mod_between(self.log_size as int, self.head as int, self.tail as int, pos as int);
                            lemma_mod_difference_equal(self.head as int, pos as int, self.log_size as int);
                        } else {
                            // read may wrap around
                            lemma_mod_not_between(self.log_size as int, self.head as int, self.tail as int, pos as int);
                            if physical_pos <= physical_tail {
                                lemma_mod_wrapped_len(self.head as int, pos as int, self.log_size as int);
                            } else {
                                lemma_mod_difference_equal(self.head as int, pos as int, self.log_size as int);
                            }
                        }
                    }

                    let physical_head = Self::addr_logical_to_physical(self.head, self.log_size);
                    let physical_tail = Self::addr_logical_to_physical(self.tail, self.log_size);

                    let ghost log = Self::recover(pm@).unwrap();
                    let ghost true_bytes = log.log.subrange(pos - log.head, pos + len - log.head);
                    if physical_head == physical_tail {
                        assert (Seq::<u8>::empty() =~= log.log.subrange(pos - log.head, pos + len - log.head));
                        let buf = Vec::new();
                        let ghost addrs = Seq::<int>::empty();
                        assert (if wrpm.constants().impervious_to_corruption { buf@ == true_bytes }
                                else { maybe_corrupted(buf@, true_bytes, addrs) });
                        Ok(buf)
                    } else if physical_pos >= physical_head && physical_pos >= contents_end - len {
                        let r1_len: u64 = contents_end - physical_pos;
                        let r2_len: u64 = len - r1_len;

                        let mut r1 = pm.read(physical_pos, r1_len);
                        let mut r2 = pm.read(contents_offset, r2_len);
                        let ghost r1_addrs = Seq::<int>::new(r1_len as nat, |i: int| i + physical_pos as int);
                        let ghost r2_addrs = Seq::<int>::new(r2_len as nat, |i: int| i + contents_offset as int);
                        let ghost addrs: Seq<int> = r1_addrs.add(r2_addrs);

                        r1.append(&mut r2);
                        assert (pm@.subrange(physical_pos as int, physical_pos + r1_len)
                                    + pm@.subrange(contents_offset as int, contents_offset + r2_len)
                                    =~= log.log.subrange(pos - log.head, pos + len - log.head));
                        assert (if wrpm.constants().impervious_to_corruption { r1@ == true_bytes }
                                else { maybe_corrupted(r1@, true_bytes, addrs) });
                        Ok(r1)
                    } else {
                        assert (pm@.subrange(physical_pos as int, physical_pos + len) =~=
                                    log.log.subrange(pos - log.head, pos + len - log.head));
                        let ghost addrs = Seq::<int>::new(len as nat, |i: int| i + physical_pos);
                        let buf = pm.read(physical_pos, len);
                        assert (if wrpm.constants().impervious_to_corruption { buf@ == true_bytes }
                                else { maybe_corrupted(buf@, true_bytes, addrs) });
                        Ok(buf)
                    }
                }
            }

            pub exec fn untrusted_get_head_and_tail<Perm, PM>(
                &self,
                wrpm: &WriteRestrictedPersistentMemory<Perm, PM>
            ) -> (result: Result<(u64, u64, u64), InfiniteLogErr>)
                where
                    Perm: CheckPermission<Seq<u8>>,
                    PM: PersistentMemory
                requires
                    self.inv(wrpm),
                    Self::recover(wrpm@).is_Some()
                ensures
                    match result {
                        Ok((result_head, result_tail, result_capacity)) =>
                            match Self::recover(wrpm@).unwrap() {
                                AbstractInfiniteLogState{ head: head, log: log, capacity: capacity } => {
                                    &&& result_head == head
                                    &&& result_tail == head + log.len()
                                    &&& result_capacity == capacity
                                }
                            },
                        Err(_) => false,
                    }
            {
                let pm = wrpm.get_pm_ref();
                proof { lemma_pm_state_header(pm@); }
                Ok((self.head, self.tail, self.log_size - 1))
            }
        }
    }
}

pub mod main_t {
    use std::fmt::Write;

    use crate::infinitelog_t::*;
    use crate::logimpl_v::*;
    use crate::pmemspec_t::*;
    use crate::sccf::CheckPermission;
    use builtin::*;
    use builtin_macros::*;
    use vstd::prelude::*;
    use vstd::set::*;
    use vstd::slice::*;

    verus! {

        pub open spec fn recovery_view() -> (result: FnSpec(Seq<u8>) -> Option<AbstractInfiniteLogState>)
        {
            |c| UntrustedLogImpl::recover(c)
        }

        pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                        impervious_to_corruption: bool) -> bool
        {
            if impervious_to_corruption {
                bytes == true_bytes
            }
            else {
                exists |addrs: Seq<int>| {
                    &&& all_elements_unique(addrs)
                    &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
                }
            }
        }

        /// A `TrustedPermission` indicates what states of persistent
        /// memory are permitted. The struct isn't public, so it can't be
        /// created outside of this file. As a further defense against one
        /// being created outside this file, its fields aren't public, and
        /// the constructor `TrustedPermission::new` isn't public.

        struct TrustedPermission {
            ghost is_state_allowable: FnSpec(Seq<u8>) -> bool
        }

        impl CheckPermission<Seq<u8>> for TrustedPermission {
            closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
                (self.is_state_allowable)(state)
            }
        }

        impl TrustedPermission {
            proof fn new(cur: Seq<u8>, next: FnSpec(AbstractInfiniteLogState, AbstractInfiniteLogState) -> bool)
                         -> (tracked perm: Self)
                ensures
                    forall |s| #[trigger] perm.check_permission(s) <==>
                        crate::sccf::is_state_allowable(cur, s, recovery_view(), next)
            {
                Self { is_state_allowable: |s| crate::sccf::is_state_allowable(cur, s, recovery_view(), next) }
            }
        }

        /// A `InfiniteLogImpl` wraps an `UntrustedLogImpl` to provide the
        /// executable interface that turns a persistent memory region
        /// into an effectively infinite log. It provides a simple
        /// interface to higher-level code.
        pub struct InfiniteLogImpl<PM: PersistentMemory> {
            untrusted_log_impl: UntrustedLogImpl,
            wrpm: WriteRestrictedPersistentMemory<TrustedPermission, PM>,
        }

        pub enum InfiniteLogErr {
            InsufficientSpaceForSetup { required_space: u64 },
            CantReadBeforeHead { head: u64 },
            CantReadPastTail { tail: u64 },
            InsufficientSpaceForAppend { available_space: u64 },
            CRCMismatch,
            CantAdvanceHeadPositionBeforeHead { head: u64 },
            CantAdvanceHeadPositionBeyondTail { tail: u64 },
        }

        impl <PM: PersistentMemory> InfiniteLogImpl<PM> {
            pub closed spec fn view(self) -> Option<AbstractInfiniteLogState>
            {
                recovery_view()(self.wrpm@)
            }

            pub closed spec fn constants(self) -> PersistentMemoryConstants
            {
                self.wrpm.constants()
            }

            pub closed spec fn valid(self) -> bool {
                &&& self.untrusted_log_impl.inv(&self.wrpm)
                &&& recovery_view()(self.wrpm@).is_Some()
            }

            /// This static function takes a `PersistentMemory` and writes
            /// to it such that its state represents an empty log starting
            /// at head position 0. This function is meant to be called
            /// exactly once per log, to create and initialize it.
            pub exec fn setup(pm: &mut PM, device_size: u64) -> (result: Result<u64, InfiniteLogErr>)
                requires
                    old(pm).inv(),
                    old(pm)@.len() == device_size
                ensures
                    pm.inv(),
                    pm.constants() == old(pm).constants(),
                    pm@.len() == device_size,
                    match result {
                        Ok(log_capacity) =>
                            recovery_view()(pm@) == Some(AbstractInfiniteLogState::initialize(log_capacity as int)),
                        Err(InfiniteLogErr::InsufficientSpaceForSetup{ required_space }) => device_size < required_space,
                        _ => false
                    }
            {
                UntrustedLogImpl::untrusted_setup(pm, device_size)
            }

            /// This static function takes a `PersistentMemory` and wraps
            /// it into an `InfiniteLogImpl`. It's meant to be called after
            /// setting up the persistent memory or after crashing and
            /// restarting.
            pub exec fn start(pm: PM, device_size: u64) -> (result: Result<InfiniteLogImpl<PM>, InfiniteLogErr>)
                requires
                    pm.inv(),
                    pm@.len() == device_size,
                    recovery_view()(pm@).is_Some()
                ensures
                    match result {
                        Ok(trusted_log_impl) => {
                            &&& trusted_log_impl.valid()
                            &&& trusted_log_impl@ == recovery_view()(pm@)
                            &&& trusted_log_impl.constants() == pm.constants()
                        },
                        Err(InfiniteLogErr::CRCMismatch) => !pm.constants().impervious_to_corruption,
                        _ => false
                    }
            {
                // The untrusted `start` routine may write to persistent memory, as long
                // as it keeps its abstraction as a log unchanged.
                let mut wrpm = WriteRestrictedPersistentMemory::new(pm);
                let tracked perm = TrustedPermission::new(pm@, |s1, s2| false);
                match UntrustedLogImpl::untrusted_start(&mut wrpm, device_size, Tracked(&perm)) {
                    Ok(untrusted_log_impl) => Ok(InfiniteLogImpl { untrusted_log_impl, wrpm }),
                    Err(e) => Err(e)
                }
            }

            /// This function appends to the log and returns the offset at
            /// which the append happened.
            pub exec fn append(&mut self, bytes_to_append: &Vec<u8>) -> (result: Result<u64, InfiniteLogErr>)
                requires
                    old(self).valid()
                ensures
                    self.valid(),
                    self.constants() == old(self).constants(),
                    match result {
                        Ok(offset) =>
                            match (old(self)@, self@) {
                                (Some(old_log), Some(new_log)) => {
                                    &&& offset as nat == old_log.log.len() + old_log.head
                                    &&& new_log == old_log.append(bytes_to_append@)
                                },
                                _ => false
                            },
                        Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space }) => {
                            &&& self@ == old(self)@
                            &&& available_space < bytes_to_append.len()
                            &&& {
                                   let log = old(self)@.unwrap();
                                   ||| available_space == log.capacity - log.log.len()
                                   ||| available_space == u64::MAX - log.head - log.log.len()
                               }
                        },
                        _ => false
                    }
            {
                // For crash safety, we must restrict the untrusted code's
                // writes to persistent memory. We must only let it write
                // such that, if a crash happens in the middle of a write,
                // the view of the persistent state is either the current
                // state or the current state with `bytes_to_append`
                // appended.

                let tracked perm = TrustedPermission::new(self.wrpm@,
                    |s1: AbstractInfiniteLogState, s2| s2 == s1.append(bytes_to_append@));
                self.untrusted_log_impl.untrusted_append(&mut self.wrpm, bytes_to_append, Tracked(&perm))
            }

            /// This function advances the head index of the log.
            pub exec fn advance_head(&mut self, new_head: u64) -> (result: Result<(), InfiniteLogErr>)
                requires
                    old(self).valid()
                ensures
                    self.valid(),
                    self.constants() == old(self).constants(),
                    match result {
                        Ok(offset) => {
                            match (old(self)@, self@) {
                                (Some(old_log), Some(new_log)) => {
                                    &&& old_log.head <= new_head <= old_log.head + old_log.log.len()
                                    &&& new_log == old_log.advance_head(new_head as int)
                                },
                                _ => false
                            }
                        }
                        Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head }) => {
                            &&& self@ == old(self)@
                            &&& head == self@.unwrap().head
                            &&& new_head < head
                        },
                        Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail }) => {
                            &&& self@ == old(self)@
                            &&& tail == self@.unwrap().head + self@.unwrap().log.len()
                            &&& new_head > tail
                        },
                        _ => false
                    }
            {
                // For crash safety, we must restrict the untrusted code's
                // writes to persistent memory. We must only let it write
                // such that, if a crash happens in the middle of a write,
                // the view of the persistent state is either the current
                // state or the current state with the head advanced to
                // `new_head`.

                let tracked perm = TrustedPermission::new(self.wrpm@,
                    |s1: AbstractInfiniteLogState, s2| s2 == s1.advance_head(new_head as int));
                self.untrusted_log_impl.untrusted_advance_head(&mut self.wrpm, new_head, Tracked(&perm))
            }

            /// This function reads `len` bytes from byte position `pos`
            /// in the log. It returns a vector of those bytes.
            pub exec fn read(&self, pos: u64, len: u64) -> (result: Result<Vec<u8>, InfiniteLogErr>)
                requires
                    self.valid(),
                    pos + len <= u64::MAX
                ensures
                    ({
                        let state = self@.unwrap();
                        let head = state.head;
                        let log = state.log;
                        match result {
                            Ok(bytes) => {
                                let true_bytes = log.subrange(pos - head, pos + len - head);
                                &&& pos >= head
                                &&& pos + len <= head + log.len()
                                &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                                 self.constants().impervious_to_corruption)
                            },
                            Err(InfiniteLogErr::CantReadBeforeHead{ head: head_pos }) => {
                                &&& pos < head
                                &&& head_pos == head
                            },
                            Err(InfiniteLogErr::CantReadPastTail{ tail }) => {
                                &&& pos + len > head + log.len()
                                &&& tail == head + log.len()
                            },
                            _ => false
                        }
                    })
            {
                // We don't need to provide permission to write to the
                // persistent memory because the untrusted code is only
                // getting a non-mutable reference to it and thus can't
                // write it. Note that the `UntrustedLogImpl` itself *is*
                // mutable, so it can freely update its in-memory state
                // (e.g., its cache) if it chooses.
                self.untrusted_log_impl.untrusted_read(&self.wrpm, pos, len)
            }

            /// This function returns a tuple consisting of the head and
            /// tail positions of the log.
            pub exec fn get_head_and_tail(&self) -> (result: Result<(u64, u64, u64), InfiniteLogErr>)
                requires
                    self.valid()
                ensures
                    match result {
                        Ok((result_head, result_tail, result_capacity)) => {
                            let inf_log = self@.unwrap();
                            &&& result_head == inf_log.head
                            &&& result_tail == inf_log.head + inf_log.log.len()
                            &&& result_capacity == inf_log.capacity
                        },
                        Err(_) => false
                    }
            {
                // We don't need to provide permission to write to the
                // persistent memory because the untrusted code is only
                // getting a non-mutable reference to it and thus can't
                // write it. Note that the `UntrustedLogImpl` itself *is*
                // mutable, so it can freely update its in-memory state
                // (e.g., its local copy of head and tail) if it chooses.
                self.untrusted_log_impl.untrusted_get_head_and_tail(&self.wrpm)
            }
        }
    }
}

pub mod math {
    #![allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;
    use vstd::prelude::*;

    verus! {

        /*
          From Ironfleet's math library's mul_nonlinear.i.dfy
        */

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_strictly_positive(x: int, y: int)
            ensures
                (0 < x && 0 < y) ==> (0 < x*y)
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_nonzero(x: int, y: int)
            ensures
                x*y != 0 <==> x != 0 && y != 0
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
            ensures
                x * (y * z) == (x * y) * z
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
            ensures
                x*(y + z) == x*y + x*z
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_ordering(x: int, y: int)
            requires
                0 < x,
                0 < y,
                0 <= x*y
            ensures
                x <= x*y && y <= x*y
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
            requires
                x < y,
                z > 0
            ensures
                x*z < y*z
        {
        }

        pub proof fn lemma_mul_by_zero_is_zero(x: int)
            ensures
                0*x == 0,
                x*0 == 0
        {
        }

        /*
          From Ironfleet's math library's mul.i.dfy
        */

        #[verifier(opaque)]
        pub open spec fn mul_pos(x: int, y: int) -> int
            recommends
                x >= 0
            decreases
                x
        {
            if x <= 0 {
                0
            }
            else {
                y + mul_pos(x - 1, y)
            }
        }

        pub open spec fn mul_recursive(x: int, y: int) -> int
        {
            if x >= 0 {
                mul_pos(x, y)
            }
            else {
                -1 * mul_pos(-1 * x, y)
            }
        }

        pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
            requires
                x >= 0
            ensures
                x * y == mul_pos(x, y)
            decreases
                x
        {
            reveal(mul_pos);
            if x > 0 {
                lemma_mul_is_mul_pos(x - 1, y);
                lemma_mul_is_distributive_add_other_way(y, x - 1, 1);
                assert (x * y == (x - 1) * y + y);
            }
        }

        pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
            ensures
                x * y == mul_recursive(x, y)
        {
            if (x >= 0) {
                lemma_mul_is_mul_pos(x, y);
            }
            else if (x <= 0) {
                lemma_mul_is_mul_pos(-x, y);
                lemma_mul_is_associative(-1, -x, y);
            }
        }

        pub proof fn lemma_mul_basics(x: int)
            ensures
                0 * x == 0,
                x * 0 == 0,
                1 * x == x,
                x * 1 == x
        {
        }

        pub proof fn lemma_mul_is_commutative(x: int, y: int)
            ensures
                x * y == y * x
        {
        }

        pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
            requires
                x <= y,
                z >= 0,
            ensures
                x * z <= y * z
            decreases
                z
        {
            if z > 0 {
                lemma_mul_inequality(x, y, z - 1);
                lemma_mul_is_distributive_add(x, z - 1, 1);
                lemma_mul_basics(x);
                assert (x * z == x * (z - 1) + x);
                lemma_mul_is_distributive_add(y, z - 1, 1);
                lemma_mul_basics(y);
                assert (y * z == y * (z - 1) + y);
            }
        }

        pub proof fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
            requires
                x <= x_bound,
                y <= y_bound,
                0 <= x,
                0 <= y
            ensures
                x * y <= x_bound * y_bound
        {
            lemma_mul_inequality(x, x_bound, y);
            lemma_mul_inequality(y, y_bound, x_bound);
        }

        /// This lemma is less precise than the non-strict version, since
        /// it uses two < facts to achieve only one < result. Thus, use it with
        /// caution -- it may be throwing away precision you'll require later.
        #[verifier(nonlinear)]
        pub proof fn lemma_mul_strict_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
            requires
                x < x_bound,
                y < y_bound,
                0 <= x,
                0 <= y
            ensures
                x * y < x_bound * y_bound
            decreases
                y
        {
            lemma_mul_upper_bound(x, x_bound - 1, y, y_bound - 1);
            assert ((x_bound - 1) * (y_bound - 1) == x_bound * y_bound - y_bound - x_bound + 1);
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
            requires
                x > 0
            ensures
                y <= z ==> x * y <= x * z,
                y < z ==> x * y < x * z
            decreases
                x
        {
            if x > 1 {
                lemma_mul_left_inequality(x - 1, y, z);
                assert (x * y == (x - 1) * y + y);
                assert (x * z == (x - 1) * z + z);
            }
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
            requires
                x*z <= y*z,
                z > 0
            ensures
                x <= y
            decreases
                z
        {
            if z > 1 {
                if (x * (z - 1) <= y * (z - 1)) {
                    lemma_mul_inequality_converse(x, y, z - 1);
                }
                else {
                    lemma_mul_inequality_converse(y, x, z - 1);
                    assert (false);
                }
            }
        }

        pub proof fn lemma_mul_equality_converse(x: int, y: int, z: int)
            requires
                x*z == y*z,
                0<z
            ensures
                x==y
        {
            lemma_mul_inequality_converse(x, y, z);
            lemma_mul_inequality_converse(y, x, z);
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
            ensures
                (y + z)*x == y*x + z*x
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
            ensures
                x*(y - z) == x*y - x*z
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_distributive_sub_other_way(x: int, y: int, z: int)
            ensures
                (y - z)*x == y*x - z*x
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
            ensures
                x*(y + z) == x*y + x*z,
                x*(y - z) == x*y - x*z,
                (y + z)*x == y*x + z*x,
                (y - z)*x == y*x - z*x,
                x*(y + z) == (y + z)*x,
                x*(y - z) == (y - z)*x,
                x*y == y*x,
                x*z == z*x
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_strictly_increases(x: int, y: int)
            requires
                1 < x,
                0 < y
            ensures
                y < x*y
        {
            assert (x * y == (x - 1) * y + y);
            lemma_mul_strictly_positive(x - 1, y);
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_increases(x: int, y: int)
            requires
                0<x,
                0<y
            ensures
                y <= x*y
            decreases
                x
        {
            if x > 1 {
                lemma_mul_increases(x - 1, y);
                assert (x * y == (x - 1) * y + y);
            }
        }

        pub proof fn lemma_mul_nonnegative(x: int, y: int)
            requires
                0 <= x,
                0 <= y
            ensures
                0 <= x*y
        {
            if x != 0 && y != 0 {
                lemma_mul_strictly_positive(x, y);
            }
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_unary_negation(x: int, y: int)
            ensures
                (-x)*y == -(x*y),
                -(x*y) == x*(-y)
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_one_to_one(m: int, x: int, y: int)
            requires
                m!=0,
                m*x == m*y
            ensures
                x == y
        {
            if m > 0 {
                if x < y {
                    lemma_mul_strict_inequality(x, y, m);
                }
                if x > y {
                    lemma_mul_strict_inequality(y, x, m);
                }
            }
            else {
                assert (x * m == -(x * -m));
                assert (y * m == -(y * -m));
                if x < y {
                    lemma_mul_strict_inequality(x, y, -m);
                }
                if x > y {
                    lemma_mul_strict_inequality(y, x, -m);
                }
            }
        }

        /*
          From Ironfleet's math library's div_nonlinear.i.dfy
        */

        pub proof fn lemma_div_of_0(d: int)
            requires
                d != 0
            ensures
                0int / d == 0
        {
        }

        pub proof fn lemma_div_by_self(d: int)
            requires
                  d != 0
            ensures
                d / d == 1
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_small_div(x: int, d: int)
            requires
                0 <= x < d,
                d > 0
            ensures
                x / d == 0
        {
        }

        pub proof fn lemma_mod_of_zero_is_zero(m: int)
            requires
                0 < m
            ensures
                0int % m == 0
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_fundamental_div_mod(x: int, d: int)
            requires
                d != 0
            ensures
                x == d * (x/d) + (x%d)
        {
        }

        #[verifier(nonlinear)]
        pub proof fn lemma_small_mod(x: int, m: int)
            requires
                0 <= x < m,
                0 < m
            ensures
                x % m == x
        {
        }

        pub proof fn lemma_mod_range(x: int, m: int)
            requires
                m > 0
            ensures
                0 <= x % m < m
        {
        }

        /*
          From Ironfleet's math library's mod_auto_proofs.i.dfy
        */

        pub proof fn lemma_mod_auto_basics(n: int, x: int)
            requires
                n > 0
            ensures
                (x + n) % n == x % n,
                (x - n) % n == x % n,
                (x + n) / n == x / n + 1,
                (x - n) / n == x / n - 1,
                0 <= x < n <==> x % n == x,
        {
            lemma_mod_range(x, n);
            lemma_fundamental_div_mod(x, n);
            lemma_fundamental_div_mod(x + n, n);
            lemma_fundamental_div_mod(x - n, n);
            lemma_mod_range(x, n);
            lemma_mod_range(x + n, n);
            lemma_mod_range(x - n, n);
            let zp = (x + n) / n - x / n - 1;
            let zm = (x - n) / n - x / n + 1;
            lemma_mul_is_distributive_sub(n, (x + n) / n, x / n + 1);
            lemma_mul_is_distributive_add(n, x / n, 1);
            assert (n * zp == n * ((x + n) / n) - n * (x / n) - n * 1);
            assert (0 == n * zp + ((x + n) % n) - (x % n));
            lemma_mul_is_distributive_sub(n, (x - n) / n, x / n - 1);
            lemma_mul_is_distributive_sub(n, x / n, 1);
            assert (n * zm == n * ((x - n) / n) - n * (x / n) + n * 1);
            assert (0 == n * zm + ((x - n) % n) - (x % n));
            if (zp > 0) { lemma_mul_inequality(1, zp, n); }
            if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
            if (zp == 0) { lemma_mul_by_zero_is_zero(n); }
            if (zm > 0) { lemma_mul_inequality(1, zm, n); }
            if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
            if 0 <= x < n {
                lemma_small_div(x, n);
            }
        }

        /*
          From Ironfleet's div.i.dfy
        */

        proof fn lemma_fundamental_div_mod_converse_helper_1(u: int, d: int, r: int)
            requires
                d != 0,
                0 <= r < d
            ensures
                u == (u * d + r) / d
            decreases
                if u >= 0 { u } else { -u }
        {
            if u < 0 {
                lemma_fundamental_div_mod_converse_helper_1(u + 1, d, r);
                lemma_mod_auto_basics(d, u * d + r);
                lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
                assert (u * d + r == (u + 1) * d + r - d);
                assert (u == (u * d + r) / d);
            }
            else if u == 0 {
                lemma_small_div(r, d);
                assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
                assert (u == (u * d + r) / d);
            }
            else {
                lemma_fundamental_div_mod_converse_helper_1(u - 1, d, r);
                lemma_mod_auto_basics(d, (u - 1) * d + r);
                lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
                assert (u * d + r == (u - 1) * d + r + d);
                assert (u == (u * d + r) / d);
            }
        }

        proof fn lemma_fundamental_div_mod_converse_helper_2(u: int, d: int, r: int)
            requires
                d != 0,
                0 <= r < d
            ensures
                r == (u * d + r) % d
            decreases
                if u >= 0 { u } else { -u }
        {
            if u < 0 {
                lemma_fundamental_div_mod_converse_helper_2(u + 1, d, r);
                lemma_mod_auto_basics(d, u * d + r);
                lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
                assert (u * d == (u + 1) * d + (-1) * d);
                assert (u * d + r == (u + 1) * d + r - d);
                assert (r == (u * d + r) % d);
            }
            else if u == 0 {
                assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
                if d > 0 {
                    lemma_small_mod(r, d);
                }
                else {
                    lemma_small_mod(r, -d);
                }
                assert (r == (u * d + r) % d);
            }
            else {
                lemma_fundamental_div_mod_converse_helper_2(u - 1, d, r);
                lemma_mod_auto_basics(d, (u - 1) * d + r);
                lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
                assert (u * d + r == (u - 1) * d + r + d);
                assert (r == (u * d + r) % d);
            }
        }

        pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
            requires
                d != 0,
                0 <= r < d,
                x == q * d + r
            ensures
                q == x / d,
                r == x % d
        {
            lemma_fundamental_div_mod_converse_helper_1(q, d, r);
            assert (q == (q * d + r) / d);
            lemma_fundamental_div_mod_converse_helper_2(q, d, r);
        }

        /*
          Lemmas we need for this project
        */

        pub proof fn lemma_div_relation_when_mods_have_same_order(d: int, x: int, y: int)
            requires
                d > 0,
                x < y,
                y - x <= d,
                x % d < y % d
            ensures
                y / d == x / d
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);

            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            lemma_mul_is_commutative(y / d, d);
            lemma_mul_is_commutative(x / d, d);

            if (y / d) > (x / d) {
                lemma_mul_inequality(1, (y / d) - (x / d), d);
                assert (((y / d) - (x / d)) * d >= 1 * d);
                assert ((y / d) * d - (x / d) * d >= d);
                assert (false);
            }
            if (y / d) < (x / d) {
                lemma_mul_inequality((y / d) - (x / d), -1, d);
                assert (((y / d) - (x / d)) * d <= (-1) * d);
                lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
                assert (false);
            }
        }

        pub proof fn lemma_div_relation_when_mods_have_same_order_alt(d: int, x: int, y: int)
            requires
                d > 0,
                x <= y,
                y - x < d,
                x % d <= y % d
            ensures
                y / d == x / d
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);

            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            lemma_mul_is_commutative(y / d, d);
            lemma_mul_is_commutative(x / d, d);

            if (y / d) > (x / d) {
                lemma_mul_inequality(1, (y / d) - (x / d), d);
                assert (((y / d) - (x / d)) * d >= 1 * d);
                assert (false);
            }
            if (y / d) < (x / d) {
                lemma_mul_inequality((y / d) - (x / d), -1, d);
                assert (((y / d) - (x / d)) * d <= (-1) * d);
                assert (false);
            }
        }

        pub proof fn lemma_div_relation_when_mods_have_different_order(d: int, x: int, y: int)
            requires
                d > 0,
                x < y,
                y - x <= d,
                y % d <= x % d
            ensures
                y / d == x / d + 1
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);

            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            lemma_mul_is_commutative(y / d, d);
            lemma_mul_is_commutative(x / d, d);

            if (y / d) > (x / d) + 1 {
                lemma_mul_inequality(2, (y / d) - (x / d), d);
                assert (((y / d) - (x / d)) * d >= 2 * d);
                assert (false);
            }
            if (y / d) <= (x / d) {
                lemma_mul_inequality(0, (x / d) - (y / d), d);
                assert (0 * d <= ((x / d) - (y / d)) * d);
                lemma_mul_is_commutative((x / d) - (y / d), d);
                lemma_mul_is_distributive_sub(d, x / d, y / d);
                assert (d * ((x / d) - (y / d)) == d * (x / d) - d * (y / d));
                assert (0 * d <= x - y - x % d + y % d);
                assert (false);
            }
        }

        pub proof fn lemma_div_relation_when_mods_have_different_order_alt(d: int, x: int, y: int)
            requires
                d > 0,
                x <= y,
                y - x < d,
                y % d < x % d
            ensures
                y / d == x / d + 1
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);

            lemma_mul_is_commutative(y / d, d);
            lemma_mul_is_commutative(x / d, d);

            if (y / d) > (x / d) + 1 {
                lemma_mul_inequality(2, (y / d) - (x / d), d);
                lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
                assert (((y / d) - (x / d)) * d >= 2 * d);
                assert (false);
            }
            if (y / d) <= (x / d) {
                lemma_mul_inequality(0, (x / d) - (y / d), d);
                assert (0 * d <= ((x / d) - (y / d)) * d);
                lemma_mul_is_commutative((x / d) - (y / d), d);
                lemma_mul_is_distributive_sub(d, x / d, y / d);
                assert (d * ((x / d) - (y / d)) == d * (x / d) - d * (y / d));
                assert (0 * d <= x - y - x % d + y % d);
                assert (false);
            }
        }

        pub proof fn lemma_mod_between(d: int, x: int, y: int, z: int)
            requires
                d > 0,
                x % d < y % d,
                y - x <= d,
                x <= z <= y
            ensures
                x % d <= z % d <= y % d
        {
            if y - x == d {
                lemma_mod_auto_basics(d, x);
                assert (y % d == x % d);
                assert (false);
            }
            else {
                lemma_fundamental_div_mod(x, d);
                lemma_fundamental_div_mod(y, d);
                lemma_fundamental_div_mod(z, d);
                lemma_mod_range(x, d);
                lemma_mod_range(y, d);
                lemma_mod_range(z, d);
                assert (d * (y / d) - d * (x / d) + y % d - x % d < d);
                assert (d * (y / d) - d * (x / d) < d);
                lemma_mul_is_distributive_sub(d, (y / d), (x / d));
                assert (d * ((y / d) - (x / d)) < d);

                lemma_div_relation_when_mods_have_same_order(d, x, y);

                let z_mod_d = x % d + (z - x);
                assert (z == (x / d) * d + z_mod_d) by {
                    assert (z == d * (x / d) + z_mod_d);
                    lemma_mul_is_commutative(d, (x / d));
                }
                lemma_fundamental_div_mod_converse(z, d, (x / d), z_mod_d);
            }
        }

        pub proof fn lemma_mod_not_between(d: int, x: int, y: int, z: int)
            requires
                d > 0,
                y % d < x % d,
                y - x <= d,
                x <= z <= y
            ensures
                z % d <= y % d || z % d >= x % d
        {
            if y - x == d {
                lemma_mod_auto_basics(d, x);
                assert (y % d == x % d);
                assert (false);
            }
            else {
                lemma_fundamental_div_mod(x, d);
                lemma_fundamental_div_mod(y, d);
                lemma_fundamental_div_mod(z, d);
                lemma_mod_range(x, d);
                lemma_mod_range(y, d);
                lemma_mod_range(z, d);
                assert (d * (y / d) - d * (x / d) + y % d - x % d >= 0);
                assert (d * (y / d) - d * (x / d) >= 0);
                lemma_mul_is_distributive_sub(d, (y / d), (x / d));
                assert (d * ((y / d) - (x / d)) >= 0);

                lemma_div_relation_when_mods_have_different_order(d, x, y);

                if y % d < z % d < x % d {
                    lemma_div_relation_when_mods_have_different_order(d, z, y);
                    lemma_div_relation_when_mods_have_same_order(d, z, x);
                    assert (false);
                }
            }
        }

        pub proof fn lemma_mod_addition_when_bounded(x: int, y: int, d: int)
            requires
                d > 0,
                y >= 0,
                (x % d) + y < d,
            ensures
                (x + y) % d == (x % d) + y
        {
            lemma_fundamental_div_mod(x, d);
            lemma_mul_is_commutative(x / d, d);
            lemma_fundamental_div_mod_converse(x + y, d, x / d, x % d + y);
        }

        pub proof fn lemma_mod_difference_equal(x: int, y: int, d: int)
            requires
                d > 0,
                x <= y,
                x % d <= y % d,
                y - x < d
            ensures
                y % d - x % d == y - x
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);

            assert (d * (y / d) - d * (x / d) + y % d - x % d == y - x);
            lemma_mul_is_distributive_sub(d, y / d, x / d);
            assert (d * (y / d - x / d) + y % d - x % d == y - x);
            assert (0 <= d * (y / d - x / d) + y % d - x % d < d);
            lemma_div_relation_when_mods_have_same_order_alt(d, x, y);
            assert (y / d == x / d);
        }

        pub proof fn lemma_mod_wrapped_len(x: int, y: int, d: int)
            requires
                d > 0,
                x <= y,
                x % d > y % d,
                y - x < d
            ensures
                d - (x % d) + (y % d) == y - x
        {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);
            assert (d * (y / d) - d * (x / d) + y % d - x % d == y - x);
            lemma_mul_is_distributive_sub(d, y / d, x / d);
            assert (d * (y / d - x / d) + y % d - x % d == y - x);
            assert (0 <= d * (y / d - x / d) + y % d - x % d < d);
            lemma_div_relation_when_mods_have_different_order_alt(d, x, y);
            assert (y / d == x / d + 1);
            assert (y / d - x / d == 1 ==> d * (y / d - x / d) == d) by (nonlinear_arith);
        }

        pub proof fn lemma_mod_equal(x: int, y: int, d: int)
            requires
                d > 0,
                x <= y,
                x % d == y % d,
                y - x < d
            ensures
                x == y
        {
            lemma_mod_difference_equal(x, y, d);
        }

        pub proof fn lemma_mod_equal_converse(x: int, y: int, d: int)
            requires
                d > 0,
                x == y,
            ensures
                x % d == y % d
        {}

        pub proof fn lemma_mod_not_equal(x: int, y: int, d: int)
            requires
                d > 0,
                y - x < d,
                y - x >= 0,
                x != y,
            ensures
                x % d != y % d
        {
            if x % d == y % d {
                if x < y {
                    lemma_mod_equal(x, y, d);
                    assert(false);
                } else {
                    assert(y - x < 0);
                    assert(false);
                }
            }

        }

        #[verifier(nonlinear)]
        pub proof fn lemma_mul_div_equal(x: int, q: int, d: int)
            requires
                q * d <= x < (q + 1) * d
            ensures
                (x / d) == q
        {}

        pub proof fn lemma_mod_subtract(x: int, y: int, d: int)
            requires
                d > 0,
                (x % d) + y >= d,
                0 <= y < d
            ensures
                (x % d) + y - d == (x + y) % d
        {
            assert(d <= (x % d) + y < 2 * d);
            assert((x / d) * d + d <= (x / d) * d + (x % d) + y < (x / d) * d + 2 * d);
            lemma_fundamental_div_mod(x, d);
            lemma_mul_is_commutative(x / d, d);
            lemma_mul_is_distributive_add_other_way(d, x / d, 1);
            lemma_mul_is_distributive_add_other_way(d, x / d, 2);
            assert((x / d + 1) * d <= x + y < (x / d + 2) * d);
            lemma_mul_div_equal(x + y, (x / d + 1), d);
            assert(x / d + 1 == (x + y) / d);
            lemma_fundamental_div_mod(x + y, d);
            assert(x + y == d * ((x + y) / d) + (x + y) % d);
        }
    }
}

pub mod pmemmock_t {
    use crate::pmemspec_t::*;
    use builtin::*;
    use builtin_macros::*;
    use std::convert::*;
    use vstd::prelude::*;

    verus! {

        pub struct VolatileMemoryMockingPersistentMemory
        {
            contents: Vec<u8>
        }

        impl VolatileMemoryMockingPersistentMemory {
            #[verifier::external_body]
            pub fn new(device_size: u64) -> (result: Result<Self, ()>)
                ensures
                    match result {
                        Ok(pm) => pm@.len() == device_size && pm.inv(),
                        Err(_) => true
                    }
            {
                Ok(Self {contents: vec![0; device_size as usize]})
            }
        }

        impl PersistentMemory for VolatileMemoryMockingPersistentMemory {
            closed spec fn view(self) -> Seq<u8>
            {
                self.contents@
            }

            closed spec fn inv(self) -> bool
            {
                self.contents.len() <= u64::MAX
            }

            closed spec fn constants(self) -> PersistentMemoryConstants
            {
                PersistentMemoryConstants { impervious_to_corruption: true }
            }

            #[verifier::external_body]
            fn read(&self, addr: u64, num_bytes: u64) -> Vec<u8>
            {
                let addr_usize: usize = addr.try_into().unwrap();
                let num_bytes_usize: usize = num_bytes.try_into().unwrap();
                self.contents[addr_usize..addr_usize+num_bytes_usize].to_vec()
            }

            #[verifier::external_body]
            fn write(&mut self, addr: u64, bytes: &[u8])
            {
                let addr_usize: usize = addr.try_into().unwrap();
                self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
            }
        }

    }
}

pub mod pmemspec_t {
    /*

      This file specifies, with the `PersistentMemory` type, the behavior
      of a persistent memory region. One of the things it models is what
      can happen to the persistent memory region if the system crashes in
      the middle of a write.

    */

    use crate::sccf::CheckPermission;
    use builtin::*;
    use builtin_macros::*;
    use vstd::bytes::*;
    use vstd::prelude::*;
    use vstd::set::*;
    use vstd::slice::*;

    #[cfg(not(verus_keep_ghost))]
    use crc64fast::Digest;

    verus! {

        pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
            forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
        }

        pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

        pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
            &&& bytes.len() == true_bytes.len() == addrs.len()
            &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
        }

        pub const crc_size: u64 = 8;

        pub closed spec fn spec_crc_bytes(header_bytes: Seq<u8>) -> Seq<u8>;

        #[verifier::external_body]
        pub exec fn bytes_crc(header_bytes: &Vec<u8>) -> (out: Vec<u8>)
            ensures
                spec_crc_bytes(header_bytes@) == out@,
                out@.len() == crc_size
        {
            #[cfg(not(verus_keep_ghost))]
            {
                let mut c = Digest::new();
                c.write(header_bytes.as_slice());
                u64_to_le_bytes(c.sum64())
            }
            #[cfg(verus_keep_ghost)]
            unimplemented!()
        }

        // We make two assumptions about how CRCs can be used to detect
        // corruption.

        // The first assumption, encapsulated in
        // `axiom_bytes_uncorrupted`, is that if we store byte sequences
        // `x` and `y` to persistent memory where `y` is the CRC of `x`,
        // then we can detect an absence of corruption by reading both of
        // them. Specifically, if we read from those locations and get
        // `x_c` and `y_c` (corruptions of `x` and `y` respectively), and
        // `y_c` is the CRC of `x_c`, then we can conclude that `x` wasn't
        // corrupted, i.e., that `x_c == x`.

        #[verifier(external_body)]
        pub proof fn axiom_bytes_uncorrupted(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                             y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
            requires
                maybe_corrupted(x_c, x, x_addrs),
                maybe_corrupted(y_c, y, y_addrs),
                y == spec_crc_bytes(x),
                y_c == spec_crc_bytes(x_c),
                all_elements_unique(x_addrs),
                all_elements_unique(y_addrs)
            ensures
                x == x_c
        {}

        // The second assumption, encapsulated in
        // `axiom_corruption_detecting_boolean`, is that the values
        // `cdb0_val` and `cdb1_val` are so randomly different from each
        // other that corruption can't make one appear to be the other.
        // That is, if we know we wrote either `cdb0_val` or `cdb1_val` to
        // a certain part of persistent memory, and when we read that same
        // part we get `cdb0_val` or `cdb1_val`, we can assume it matches
        // what we last wrote to it. To justify the assumption that
        // `cdb0_val` and `cdb1_val` are different from each other, we set
        // them to CRC(b"0") and CRC(b"1"), respectively.

        pub const cdb0_val: u64 = 0xa32842d19001605e; // CRC(b"0")
        pub const cdb1_val: u64 = 0xab21aa73069531b7; // CRC(b"1")

        #[verifier(external_body)]
        pub proof fn axiom_corruption_detecting_boolean(cdb_c: u64, cdb: u64, addrs: Seq<int>)
            requires
                maybe_corrupted(spec_u64_to_le_bytes(cdb_c), spec_u64_to_le_bytes(cdb), addrs),
                all_elements_unique(addrs),
                cdb == cdb0_val || cdb == cdb1_val,
                cdb_c == cdb0_val || cdb_c == cdb1_val,
            ensures
                cdb_c == cdb
        {}

        pub struct PersistentMemoryConstants {
            pub impervious_to_corruption: bool
        }

        // We mark this as `external_body` so that the verifier can't see
        // that there's nothing important in it and thereby shortcut some
        // checks.

        pub trait PersistentMemory : Sized {
            spec fn view(self) -> Seq<u8>;

            spec fn inv(self) -> bool;

            spec fn constants(self) -> PersistentMemoryConstants;

            /// This is the model of some routine that reads the
            /// `num_bytes` bytes at address `addr`.
            fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
                requires
                    self.inv(),
                    addr + num_bytes <= self@.len()
                ensures
                    ({
                        let true_bytes = self@.subrange(addr as int, addr + num_bytes);
                        let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr);
                        if self.constants().impervious_to_corruption {
                            bytes@ == true_bytes
                        }
                        else {
                            maybe_corrupted(bytes@, true_bytes, addrs)
                        }
                    });

            /// This is the model of some routine that writes `bytes`
            /// starting at address `addr`.
            fn write(&mut self, addr: u64, bytes: &[u8])
                requires
                    old(self).inv(),
                    addr + bytes@.len() <= (old(self))@.len(),
                    addr + bytes@.len() <= u64::MAX
                ensures
                    self.inv(),
                    self.constants() == old(self).constants(),
                    self@ == update_contents_to_reflect_write(old(self)@, addr as int, bytes@);
        }

        /// We model the persistent memory as getting flushed in chunks,
        /// where each chunk has `persistence_chunk_size` bytes. We refer
        /// to chunk number `id` as the set of addresses `addr` such that
        /// `addr / persistence_chunk_size == id`.
        pub spec const persistence_chunk_size: int = 8;

        /// Return the byte at address `addr` after writing
        /// `write_bytes` to address `write_addr`, if the byte at
        /// `addr` before the write was `prewrite_byte`.
        pub open spec fn update_byte_to_reflect_write(addr: int, prewrite_byte: u8, write_addr: int,
                                                      write_bytes: Seq<u8>) -> u8
        {
            if write_addr <= addr && addr < write_addr + write_bytes.len() {
                write_bytes[addr - write_addr]
            }
            else {
                prewrite_byte
            }
        }

        /// Return the contents of persistent memory after writing
        /// `write_bytes` to address `write_addr`, if the contents
        /// before the write was `prewrite_contents`.
        pub open spec(checked) fn update_contents_to_reflect_write(prewrite_contents: Seq<u8>, write_addr: int,
                                                                   write_bytes: Seq<u8>) -> Seq<u8>
            recommends
                0 <= write_addr,
                write_addr + write_bytes.len() <= prewrite_contents.len(),
        {
            Seq::<u8>::new(prewrite_contents.len(),
                           |addr| update_byte_to_reflect_write(addr, prewrite_contents[addr],
                                                               write_addr, write_bytes))
        }

        /// Return the byte at address `addr` after initiating (but
        /// not necessarily completing) a write of `write_bytes` to
        /// address `write_addr`, given that the byte at `addr` before
        /// the write was `prewrite_byte` and given that the set of
        /// chunk IDs that have been flushed since the initiation of
        /// the write is `chunks_flushed`.
        pub open spec fn update_byte_to_reflect_partially_flushed_write(addr: int, prewrite_byte: u8, write_addr: int,
                                                                        write_bytes: Seq<u8>,
                                                                        chunks_flushed: Set<int>) -> u8
        {
            if chunks_flushed.contains(addr / persistence_chunk_size) {
                update_byte_to_reflect_write(addr, prewrite_byte, write_addr, write_bytes)
            }
            else {
                prewrite_byte
            }
        }

        /// Return the contents of persistent memory after initiating
        /// (but not necessarily completing) a write of `write_bytes`
        /// to address `write_addr`, given that the contents before
        /// the write were `prewrite_contents` and given that the set of
        /// chunk IDs that have been flushed since the initiation of
        /// the write is `chunks_flushed`.
        pub open spec(checked) fn update_contents_to_reflect_partially_flushed_write(contents: Seq<u8>, write_addr: int,
                                                                                     write_bytes: Seq<u8>,
                                                                                     chunks_flushed: Set<int>) -> Seq<u8>
            recommends
                0 <= write_addr,
                write_addr + write_bytes.len() <= contents.len(),
        {
            Seq::<u8>::new(contents.len(),
                           |addr| update_byte_to_reflect_partially_flushed_write(addr, contents[addr], write_addr,
                                                                                 write_bytes, chunks_flushed))
        }

        /// A `WriteRestrictedPersistentMemory<P>` object wraps a
        /// `PersistentMemory` object to restrict how it's written.
        /// Untrusted code passed one of these can only write to the
        /// encapsulated persistent memory by providing a permission of
        /// type `P`. That permission must allow all possible states `s`
        /// such that crashing in the middle of the write might leave the
        /// persistent memory in state `s`.
        pub struct WriteRestrictedPersistentMemory<Perm, PM>
            where
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemory
        {
            pm: PM,
            ghost perm: Option<Perm> // unused, but Rust demands some reference to Perm
        }

        impl <Perm, PM> WriteRestrictedPersistentMemory<Perm, PM>
            where
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemory
        {
            pub closed spec fn view(self) -> Seq<u8> {
                self.pm@
            }

            pub closed spec fn inv(self) -> bool {
                self.pm.inv()
            }

            pub closed spec fn constants(self) -> PersistentMemoryConstants {
                self.pm.constants()
            }

            pub exec fn new(pm: PM) -> (wrpm: Self)
                requires
                    pm.inv()
                ensures
                    wrpm@ == pm@,
                    wrpm.inv(),
                    wrpm.constants() == pm.constants()
            {
                Self { pm: pm, perm: None }
            }

            pub exec fn get_pm_ref(&self) -> (pm: &PM)
                requires
                    self.inv()
                ensures
                    pm.inv(),
                    pm@ == self@,
                    pm.constants() == self.constants()
            {
                &self.pm
            }

            /// This `write` function can only be called if a crash in the
            /// middle of the requested write will leave the persistent
            /// memory in a state allowed by `perm`. The state must be
            /// allowed no matter what subset of the persistence chunks
            /// have been flushed.
            pub exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
                requires
                    old(self).inv(),
                    addr + bytes@.len() <= old(self)@.len(),
                    addr + bytes@.len() <= u64::MAX,
                    forall |chunks_flushed| {
                        let new_contents: Seq<u8> =
                            #[trigger] update_contents_to_reflect_partially_flushed_write(
                                old(self)@, addr as int, bytes@, chunks_flushed
                            );
                        perm@.check_permission(new_contents)
                    },
                ensures
                    self.inv(),
                    self.constants() == old(self).constants(),
                    self@ == update_contents_to_reflect_write(old(self)@, addr as int, bytes@),
            {
                self.pm.write(addr, bytes)
            }
        }

    }
}

pub mod sccf {
    /*
      Simple crash-consistency framework (open source)
    */

    use builtin::*;
    use builtin_macros::*;
    use vstd::prelude::*;

    verus! {

        pub open spec fn is_state_allowable<AbstractStorage, AbstractService>(
            pre_operation_state: AbstractStorage,
            crash_state: AbstractStorage,
            recovery_view: FnSpec(AbstractStorage) -> Option<AbstractService>,
            abstract_next: FnSpec(AbstractService, AbstractService) -> bool
            ) -> bool
        {
            let pre_operation_abstract_state = recovery_view(pre_operation_state);
            let crash_abstract_state = recovery_view(crash_state);
            ||| crash_abstract_state == pre_operation_abstract_state
            ||| {
                    &&& pre_operation_abstract_state.is_Some()
                    &&& crash_abstract_state.is_Some()
                    &&& abstract_next(pre_operation_abstract_state.unwrap(), crash_abstract_state.unwrap())
                }
        }

        pub trait CheckPermission<AbstractStorage>
        {
            spec fn check_permission(&self, state: AbstractStorage) -> bool;
        }

    }
}

use crate::main_t::*;
use crate::pmemmock_t::*;
use crate::pmemspec_t::*;

verus! {

    fn main() {
        let device_size: u64 = 4096;
        if let Ok(mut pm) = VolatileMemoryMockingPersistentMemory::new(device_size) {
            if let Ok(_) = InfiniteLogImpl::setup(&mut pm, device_size) {
                if let Ok(mut log) = InfiniteLogImpl::start(pm, device_size) {
                    let mut v: Vec<u8> = Vec::<u8>::new();
                    v.push(30); v.push(42); v.push(100);
                    if let Ok(pos) = log.append(&v) {
                        if let Ok((head, tail, capacity)) = log.get_head_and_tail() {
                            assert (head == 0);
                            assert (tail == 3);
                            // TODO: add an assertion using maybe_corrupted here
                            // if let Ok(bytes) = log.read(1, 2) {
                            //     assert (bytes@[0] == 42);
                            // }
                        }
                    }
                }
            }
        }
    }

}
