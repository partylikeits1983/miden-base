use alloc::string::ToString;

use miden_crypto::{
    hash::rpo::RpoDigest,
    merkle::{LeafIndex, MerkleError, MerklePath, SimpleSmt},
};

use crate::{
    note::{compute_note_hash, NoteId, NoteMetadata},
    utils::{ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable},
    BlockError, BLOCK_NOTE_TREE_DEPTH, MAX_BATCHES_PER_BLOCK, MAX_OUTPUT_NOTES_PER_BATCH,
    MAX_OUTPUT_NOTES_PER_BLOCK,
};

/// Wrapper over [SimpleSmt<BLOCK_NOTE_TREE_DEPTH>] for notes tree.
///
/// Each note is stored as two adjacent leaves: odd leaf for id, even leaf for metadata hash.
/// ID's leaf index is calculated as [(batch_idx * MAX_NOTES_PER_BATCH + note_idx_in_batch) * 2].
/// Metadata hash leaf is stored the next after id leaf: [id_index + 1].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockNoteTree(SimpleSmt<BLOCK_NOTE_TREE_DEPTH>);

impl BlockNoteTree {
    /// Returns a new [BlockNoteTree] instantiated with entries set as specified by the provided
    /// entries.
    ///
    /// Entry format: (note_index, note_id, note_metadata).
    ///
    /// Value of each leaf is computed as: `hash(note_id || note_metadata)`.
    /// All leaves omitted from the entries list are set to [crate::EMPTY_WORD].
    ///
    /// # Errors
    /// Returns an error if:
    /// - The number of entries exceeds the maximum notes tree capacity, that is 2^16.
    /// - The provided entries contain multiple values for the same key.
    pub fn with_entries(
        entries: impl IntoIterator<Item = (BlockNoteIndex, NoteId, NoteMetadata)>,
    ) -> Result<Self, MerkleError> {
        let leaves = entries.into_iter().map(|(index, note_id, metadata)| {
            (index.leaf_index_value() as u64, compute_note_hash(note_id, &metadata).into())
        });

        SimpleSmt::with_leaves(leaves).map(Self)
    }

    /// Returns the root of the tree
    pub fn root(&self) -> RpoDigest {
        self.0.root()
    }

    /// Returns merkle path for the note with specified batch/note indexes.
    pub fn get_note_path(&self, index: BlockNoteIndex) -> MerklePath {
        // get the path to the leaf containing the note (path len = 16)
        self.0.open(&index.leaf_index()).path
    }
}

impl Default for BlockNoteTree {
    fn default() -> Self {
        Self(SimpleSmt::new().expect("Unreachable"))
    }
}

/// Index of a block note.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockNoteIndex {
    batch_idx: usize,
    note_idx_in_batch: usize,
}

impl BlockNoteIndex {
    /// Creates a new [BlockNoteIndex].
    pub fn new(batch_idx: usize, note_idx_in_batch: usize) -> Result<Self, BlockError> {
        if note_idx_in_batch >= MAX_OUTPUT_NOTES_PER_BATCH {
            return Err(BlockError::TooManyNotesInBatch(note_idx_in_batch));
        }
        if batch_idx >= MAX_BATCHES_PER_BLOCK {
            return Err(BlockError::TooManyTransactionBatches(batch_idx));
        }

        Ok(Self { batch_idx, note_idx_in_batch })
    }

    /// Returns the batch index.
    pub fn batch_idx(&self) -> usize {
        self.batch_idx
    }

    /// Returns the note index in the batch.
    pub fn note_idx_in_batch(&self) -> usize {
        self.note_idx_in_batch
    }

    /// Returns the leaf index of the note in the note tree.
    pub fn leaf_index(&self) -> LeafIndex<BLOCK_NOTE_TREE_DEPTH> {
        LeafIndex::new(
            (self.batch_idx() * MAX_OUTPUT_NOTES_PER_BATCH + self.note_idx_in_batch()) as u64,
        )
        .expect("Unreachable: Input values must be valid at this point")
    }

    /// Returns the leaf index value of the note in the note tree.
    pub fn leaf_index_value(&self) -> u16 {
        const _: () = assert!(
            MAX_OUTPUT_NOTES_PER_BLOCK <= u16::MAX as usize + 1,
            "Any note index is expected to fit in `u16`"
        );

        self.leaf_index()
            .value()
            .try_into()
            .expect("Unreachable: Input values must be valid at this point")
    }
}

// SERIALIZATION
// ================================================================================================

impl Serializable for BlockNoteTree {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        target.write_u32(self.0.num_leaves() as u32);
        target.write_many(self.0.leaves());
    }
}

impl Deserializable for BlockNoteTree {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let count = source.read_u32()?;
        let leaves = source.read_many(count as usize)?;

        SimpleSmt::with_leaves(leaves)
            .map(Self)
            .map_err(|err| DeserializationError::InvalidValue(err.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use miden_crypto::{
        merkle::SimpleSmt,
        utils::{Deserializable, Serializable},
        Felt, ONE, ZERO,
    };

    use super::BlockNoteTree;

    #[test]
    fn test_serialization() {
        let data = core::iter::repeat(())
            .enumerate()
            .map(|(idx, ())| (idx as u64, [ONE, ZERO, ONE, Felt::new(idx as u64)]))
            .take(100);
        let initial_tree = BlockNoteTree(SimpleSmt::with_leaves(data).unwrap());

        let serialized = initial_tree.to_bytes();
        let deserialized_tree = BlockNoteTree::read_from_bytes(&serialized).unwrap();

        assert_eq!(deserialized_tree, initial_tree);
    }
}
