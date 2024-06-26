extern crate alloc;
pub use alloc::collections::BTreeMap;

use miden_lib::transaction::TransactionKernel;
use miden_objects::{
    accounts::{Account, AccountCode, AccountId, AccountStorage, SlotItem, StorageSlot},
    assembly::ModuleAst,
    assets::{Asset, AssetVault},
    notes::{Note, NoteId},
    transaction::{ChainMmr, InputNote, InputNotes, OutputNote, TransactionArgs},
    BlockHeader, Felt, Word,
};
use miden_tx::{DataStore, DataStoreError, TransactionInputs, TransactionProgress};
use mock::mock::{
    account::MockAccountType,
    notes::AssetPreservationStatus,
    transaction::{mock_inputs, mock_inputs_with_existing},
};
use serde::Serialize;
use serde_json::{from_str, to_string_pretty, Value};

use super::{read_to_string, write, Benchmark, Path};

// CONSTANTS
// ================================================================================================

pub const ACCOUNT_ID_FUNGIBLE_FAUCET_ON_CHAIN: u64 = 0x200000000000001F; // 2305843009213693983
pub const ACCOUNT_ID_SENDER: u64 = 0x800000000000001F; // 9223372036854775839
pub const ACCOUNT_ID_REGULAR_ACCOUNT_UPDATABLE_CODE_OFF_CHAIN: u64 = 0x900000000000003F; // 10376293541461622847

pub const DEFAULT_AUTH_SCRIPT: &str = "
    use.miden::contracts::auth::basic->auth_tx

    begin
        call.auth_tx::auth_tx_rpo_falcon512
    end
";

pub const DEFAULT_ACCOUNT_CODE: &str = "
    use.miden::contracts::wallets::basic->basic_wallet
    use.miden::contracts::auth::basic->basic_eoa

    export.basic_wallet::receive_asset
    export.basic_wallet::send_asset
    export.basic_eoa::auth_tx_rpo_falcon512
";

// MOCK DATA STORE
// ================================================================================================

#[derive(Clone)]
pub struct MockDataStore {
    pub account: Account,
    pub block_header: BlockHeader,
    pub block_chain: ChainMmr,
    pub notes: Vec<InputNote>,
    pub tx_args: TransactionArgs,
}

impl MockDataStore {
    pub fn new(asset_preservation: AssetPreservationStatus) -> Self {
        let (tx_inputs, tx_args) =
            mock_inputs(MockAccountType::StandardExisting, asset_preservation);
        let (account, _, block_header, block_chain, notes) = tx_inputs.into_parts();

        Self {
            account,
            block_header,
            block_chain,
            notes: notes.into_vec(),
            tx_args,
        }
    }

    pub fn with_existing(account: Option<Account>, input_notes: Option<Vec<Note>>) -> Self {
        let (
            account,
            block_header,
            block_chain,
            consumed_notes,
            _auxiliary_data_inputs,
            created_notes,
        ) = mock_inputs_with_existing(
            MockAccountType::StandardExisting,
            AssetPreservationStatus::Preserved,
            account,
            input_notes,
        );
        let output_notes = created_notes.into_iter().filter_map(|note| match note {
            OutputNote::Full(note) => Some(note),
            OutputNote::Header(_) => None,
        });
        let mut tx_args = TransactionArgs::default();
        tx_args.extend_expected_output_notes(output_notes);

        Self {
            account,
            block_header,
            block_chain,
            notes: consumed_notes,
            tx_args,
        }
    }

    pub fn tx_args(&self) -> &TransactionArgs {
        &self.tx_args
    }
}

impl Default for MockDataStore {
    fn default() -> Self {
        Self::new(AssetPreservationStatus::Preserved)
    }
}

impl DataStore for MockDataStore {
    fn get_transaction_inputs(
        &self,
        account_id: AccountId,
        block_num: u32,
        notes: &[NoteId],
    ) -> Result<TransactionInputs, DataStoreError> {
        assert_eq!(account_id, self.account.id());
        assert_eq!(block_num, self.block_header.block_num());
        assert_eq!(notes.len(), self.notes.len());

        let notes = self
            .notes
            .iter()
            .filter(|note| notes.contains(&note.id()))
            .cloned()
            .collect::<Vec<_>>();

        Ok(TransactionInputs::new(
            self.account.clone(),
            None,
            self.block_header,
            self.block_chain.clone(),
            InputNotes::new(notes).unwrap(),
        )
        .unwrap())
    }

    fn get_account_code(&self, account_id: AccountId) -> Result<ModuleAst, DataStoreError> {
        assert_eq!(account_id, self.account.id());
        Ok(self.account.code().module().clone())
    }
}

// TRANSACTION BENCHMARK
// ================================================================================================

#[derive(Serialize)]
pub struct TransactionBenchmark {
    prologue: Option<u32>,
    notes_processing: Option<u32>,
    note_execution: BTreeMap<String, Option<u32>>,
    tx_script_processing: Option<u32>,
    epilogue: Option<u32>,
}

impl From<TransactionProgress> for TransactionBenchmark {
    fn from(tx_progress: TransactionProgress) -> Self {
        let prologue = tx_progress.prologue().len();

        let notes_processing = tx_progress.notes_processing().len();

        let mut note_execution = BTreeMap::new();
        tx_progress.note_execution().iter().for_each(|(note_id, interval)| {
            note_execution.insert(note_id.to_hex(), interval.len());
        });

        let tx_script_processing = tx_progress.tx_script_processing().len();

        let epilogue = tx_progress.epilogue().len();

        Self {
            prologue,
            notes_processing,
            note_execution,
            tx_script_processing,
            epilogue,
        }
    }
}

// HELPER FUNCTIONS
// ================================================================================================

pub fn get_account_with_default_account_code(
    account_id: AccountId,
    public_key: Word,
    assets: Option<Asset>,
) -> Account {
    let account_code_src = DEFAULT_ACCOUNT_CODE;
    let account_code_ast = ModuleAst::parse(account_code_src).unwrap();
    let account_assembler = TransactionKernel::assembler();

    let account_code = AccountCode::new(account_code_ast.clone(), &account_assembler).unwrap();
    let account_storage = AccountStorage::new(
        vec![SlotItem {
            index: 0,
            slot: StorageSlot::new_value(public_key),
        }],
        vec![],
    )
    .unwrap();

    let account_vault = match assets {
        Some(asset) => AssetVault::new(&[asset]).unwrap(),
        None => AssetVault::new(&[]).unwrap(),
    };

    Account::new(account_id, account_vault, account_storage, account_code, Felt::new(1))
}

pub fn write_bench_results_to_json(
    path: &Path,
    tx_benchmarks: Vec<(Benchmark, TransactionProgress)>,
) -> Result<(), String> {
    // convert benchmark file internals to the JSON Value
    let benchmark_file = read_to_string(path).map_err(|e| e.to_string())?;
    let mut benchmark_json: Value = from_str(&benchmark_file).map_err(|e| e.to_string())?;

    // fill becnhmarks JSON with results of each benchmark
    for (bench_type, tx_progress) in tx_benchmarks {
        let tx_benchmark = TransactionBenchmark::from(tx_progress);
        let tx_benchmark_json = serde_json::to_value(tx_benchmark).map_err(|e| e.to_string())?;

        benchmark_json[bench_type.to_string()] = tx_benchmark_json;
    }

    // write the becnhmarks JSON to the results file
    write(
        path,
        to_string_pretty(&benchmark_json).expect("failed to convert json to String"),
    )
    .map_err(|e| e.to_string())?;

    Ok(())
}
