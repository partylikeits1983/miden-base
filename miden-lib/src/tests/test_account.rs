use miden_objects::{
    accounts::{
        account_id::testing::{
            ACCOUNT_ID_FUNGIBLE_FAUCET_ON_CHAIN, ACCOUNT_ID_INSUFFICIENT_ONES,
            ACCOUNT_ID_NON_FUNGIBLE_FAUCET_OFF_CHAIN,
            ACCOUNT_ID_REGULAR_ACCOUNT_IMMUTABLE_CODE_ON_CHAIN,
            ACCOUNT_ID_REGULAR_ACCOUNT_UPDATABLE_CODE_OFF_CHAIN,
        },
        AccountId, AccountType, StorageSlotType,
    },
    crypto::{hash::rpo::RpoDigest, merkle::LeafIndex},
};
use mock::{
    mock::{
        account::{
            storage_item_0, storage_item_1, storage_item_2, storage_map_2, MockAccountType,
            STORAGE_LEAVES_2,
        },
        host::MockHost,
        notes::AssetPreservationStatus,
        transaction::{mock_executed_tx, mock_inputs},
    },
    prepare_transaction,
    procedures::{output_notes_data_procedure, prepare_word},
    run_tx, run_within_host, run_within_tx_kernel,
};

use super::{
    super::transaction::ToTransactionKernelInputs, ContextId, Felt, MemAdviceProvider,
    ProcessState, StackInputs, Word, ONE, ZERO,
};
use crate::transaction::memory::{ACCT_CODE_ROOT_PTR, ACCT_NEW_CODE_ROOT_PTR};

// ACCOUNT CODE TESTS
// ================================================================================================

#[test]
pub fn test_set_code_is_not_immediate() {
    let (tx_inputs, tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

    let code = "
        use.miden::kernels::tx::prologue
        use.miden::account
        begin
            exec.prologue::prepare_transaction
            push.1.2.3.4
            exec.account::set_code
        end
        ";

    let transaction = prepare_transaction(tx_inputs, tx_args, code, None);
    let process = run_tx(&transaction).unwrap();

    // assert the code root is not changed
    assert_eq!(
        process.get_mem_value(ContextId::root(), ACCT_CODE_ROOT_PTR).unwrap(),
        transaction.account().code().root().as_elements()
    );

    // assert the new code root is cached
    assert_eq!(
        process.get_mem_value(ContextId::root(), ACCT_NEW_CODE_ROOT_PTR).unwrap(),
        [ONE, Felt::new(2), Felt::new(3), Felt::new(4)]
    );
}

#[test]
pub fn test_set_code_succeeds() {
    let executed_transaction = mock_executed_tx(AssetPreservationStatus::Preserved);

    let output_notes_data_procedure =
        output_notes_data_procedure(executed_transaction.output_notes());

    let code = format!(
        "
        use.miden::account
        use.miden::kernels::tx::prologue
        use.miden::kernels::tx::epilogue

        {output_notes_data_procedure}
        begin
            exec.prologue::prepare_transaction

            push.0.1.2.3
            exec.account::set_code

            exec.create_mock_notes

            push.1
            exec.account::incr_nonce

            exec.epilogue::finalize_transaction
        end
        "
    );

    let (stack_inputs, advice_inputs) = executed_transaction.get_kernel_inputs();
    let host = MockHost::new(executed_transaction.initial_account().into(), advice_inputs);
    let process = run_within_host("", &code, stack_inputs, host, None).unwrap();

    // assert the code root is changed after the epilogue
    assert_eq!(
        process.get_mem_value(ContextId::root(), ACCT_CODE_ROOT_PTR).unwrap(),
        [ZERO, ONE, Felt::new(2), Felt::new(3)]
    );
}

// ACCOUNT ID TESTS
// ================================================================================================

#[test]
pub fn test_account_type() {
    let procedures = vec![
        ("is_fungible_faucet", AccountType::FungibleFaucet),
        ("is_non_fungible_faucet", AccountType::NonFungibleFaucet),
        ("is_updatable_account", AccountType::RegularAccountUpdatableCode),
        ("is_immutable_account", AccountType::RegularAccountImmutableCode),
    ];

    let test_cases = [
        ACCOUNT_ID_REGULAR_ACCOUNT_IMMUTABLE_CODE_ON_CHAIN,
        ACCOUNT_ID_REGULAR_ACCOUNT_UPDATABLE_CODE_OFF_CHAIN,
        ACCOUNT_ID_FUNGIBLE_FAUCET_ON_CHAIN,
        ACCOUNT_ID_NON_FUNGIBLE_FAUCET_OFF_CHAIN,
    ];

    for (procedure, expected_type) in procedures {
        let mut has_type = false;

        for account_id in test_cases.iter() {
            let account_id = AccountId::try_from(*account_id).unwrap();

            let code = format!(
                "
                use.miden::kernels::tx::memory
                use.miden::kernels::tx::account

                begin
                    exec.account::{}
                end
                ",
                procedure
            );

            let process = run_within_tx_kernel(
                "",
                &code,
                StackInputs::new(vec![account_id.into()]).unwrap(),
                MemAdviceProvider::default(),
                None,
            )
            .unwrap();

            let expected_result = if account_id.account_type() == expected_type {
                has_type = true;
                ONE
            } else {
                ZERO
            };
            assert_eq!(
                process.stack.get(0),
                expected_result,
                "Rust and Masm check on account type diverge. proc: {} account_id: {} account_type: {:?} expected_type: {:?}",
                procedure,
                account_id,
                account_id.account_type(),
                expected_type,
            );
        }

        assert!(has_type, "missing test for type {:?}", expected_type);
    }
}

#[test]
fn test_validate_id_fails_on_insufficient_ones() {
    let code = format!(
        "
        use.miden::kernels::tx::account

        begin
            push.{ACCOUNT_ID_INSUFFICIENT_ONES}
            exec.account::validate_id
        end
        "
    );

    let result =
        run_within_tx_kernel("", &code, StackInputs::default(), MemAdviceProvider::default(), None);

    assert!(result.is_err());
}

#[test]
fn test_is_faucet_procedure() {
    let test_cases = [
        ACCOUNT_ID_REGULAR_ACCOUNT_IMMUTABLE_CODE_ON_CHAIN,
        ACCOUNT_ID_REGULAR_ACCOUNT_UPDATABLE_CODE_OFF_CHAIN,
        ACCOUNT_ID_FUNGIBLE_FAUCET_ON_CHAIN,
        ACCOUNT_ID_NON_FUNGIBLE_FAUCET_OFF_CHAIN,
    ];

    for account_id in test_cases.iter() {
        let account_id = AccountId::try_from(*account_id).unwrap();

        // assembly codes that checks if an account is a faucet
        let code = format!(
            "
        use.miden::kernels::tx::account

        begin
            # push the account id on to the stack
            push.{account_id}

            # execute is_faucet procedure
            exec.account::is_faucet
        end
    ",
            account_id = account_id,
        );

        let process = run_within_tx_kernel(
            "",
            &code,
            StackInputs::default(),
            MemAdviceProvider::default(),
            None,
        )
        .unwrap();
        let is_faucet = account_id.is_faucet();
        assert_eq!(
            process.stack.get(0),
            Felt::new(is_faucet as u64),
            "Rust and Masm is_faucet diverged. account_id: {}",
            account_id
        );
    }
}

// ACCOUNT STORAGE TESTS
// ================================================================================================

#[test]
fn test_get_item() {
    for storage_item in [storage_item_0(), storage_item_1()] {
        let (tx_inputs, tx_args) =
            mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

        let code = format!(
            "
        use.miden::account
        use.miden::kernels::tx::prologue


        begin
            # prepare the transaction
            exec.prologue::prepare_transaction

            # push the account storage item index
            push.{item_index}

            # get the item
            exec.account::get_item

            # assert the item value is correct
            push.{item_value} assert_eqw
        end
        ",
            item_index = storage_item.index,
            item_value = prepare_word(&storage_item.slot.value)
        );

        let transaction = prepare_transaction(tx_inputs, tx_args, &code, None);
        let _process = run_tx(&transaction).unwrap();
    }
}

#[test]
fn test_set_item() {
    let (tx_inputs, tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

    // copy the initial account slots (SMT)
    let mut account_smt = tx_inputs.account().storage().slots().clone();
    let init_root = account_smt.root();

    // insert a new leaf value
    let new_item_index = LeafIndex::new(12).unwrap();
    let new_item_value: Word = [Felt::new(91), Felt::new(92), Felt::new(93), Felt::new(94)];
    account_smt.insert(new_item_index, new_item_value);
    assert_ne!(account_smt.root(), init_root);

    let code = format!(
        "
    use.miden::account
    use.miden::kernels::tx::memory
    use.miden::kernels::tx::prologue

    begin
        # prepare the transaction
        exec.prologue::prepare_transaction

        # push the new storage item onto the stack
        push.{new_value}

        # push the account storage item index
        push.{new_item_index}

        # get the item
        exec.account::set_item

        # assert empty old value
        padw assert_eqw

        # get the new storage root
        exec.memory::get_acct_storage_root

        # assert the item value is correct
        push.{new_root} assert_eqw
    end
    ",
        new_value = prepare_word(&new_item_value),
        new_item_index = new_item_index.value(),
        new_root = prepare_word(&account_smt.root()),
    );

    let transaction = prepare_transaction(tx_inputs, tx_args, &code, None);
    let _process = run_tx(&transaction).unwrap();
}

// Test different account storage types
#[test]
fn test_get_storage_data_type() {
    for storage_item in [storage_item_0(), storage_item_1(), storage_item_2()] {
        let (tx_inputs, tx_args) =
            mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

        let code = format!(
            "
        use.miden::kernels::tx::account
        use.miden::kernels::tx::prologue

        begin
            # prepare the transaction
            exec.prologue::prepare_transaction

            # push the account storage item index
            push.{item_index}

            # get the data type of the respective storage slot
            exec.account::get_storage_slot_type_info

        end
        ",
            item_index = storage_item.index,
        );

        let transaction = prepare_transaction(tx_inputs, tx_args, &code, None);
        let process = run_tx(&transaction).unwrap();

        let storage_slot_data_type = match storage_item.slot.slot_type {
            StorageSlotType::Value { value_arity } => (value_arity, 0),
            StorageSlotType::Map { value_arity } => (value_arity, 1),
            StorageSlotType::Array { value_arity, depth } => (value_arity, depth),
        };

        assert_eq!(process.get_stack_item(0), Felt::from(storage_slot_data_type.0));
        assert_eq!(process.get_stack_item(1), Felt::from(storage_slot_data_type.1));

        // check that the rest of the stack is empty
        assert_eq!(process.get_stack_item(2), ZERO);
        assert_eq!(process.get_stack_item(3), ZERO);
        assert_eq!(Word::default(), process.get_stack_word(1));
        assert_eq!(Word::default(), process.get_stack_word(2));
        assert_eq!(Word::default(), process.get_stack_word(3));
    }
}

#[test]
fn test_get_map_item() {
    let (tx_inputs, tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

    let storage_item = storage_item_2();
    for (key, value) in STORAGE_LEAVES_2 {
        let code = format!(
            "
            use.miden::account
            use.miden::kernels::tx::prologue

            begin
                # prepare the transaction
                exec.prologue::prepare_transaction

                # push the item's KEY
                push.{map_key}

                # push the account storage item index
                push.{item_index}

                # get the map item
                exec.account::get_map_item

            end
            ",
            item_index = storage_item.index,
            map_key = prepare_word(&key),
        );

        let transaction =
            prepare_transaction(tx_inputs.clone(), tx_args.clone(), code.as_str(), None);
        let process = run_tx(&transaction).unwrap();
        assert_eq!(value, process.get_stack_word(0));

        // check that the rest of the stack is empty
        assert_eq!(Word::default(), process.get_stack_word(1));
        assert_eq!(Word::default(), process.get_stack_word(2));
        assert_eq!(Word::default(), process.get_stack_word(3));
    }
}

#[test]
fn test_set_map_item() {
    let (new_key, new_value) = (
        RpoDigest::new([Felt::new(109), Felt::new(110), Felt::new(111), Felt::new(112)]),
        [Felt::new(9_u64), Felt::new(10_u64), Felt::new(11_u64), Felt::new(12_u64)],
    );

    let (tx_inputs, tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

    let storage_item = storage_item_2();

    let code = format!(
        "
        use.miden::account
        use.miden::kernels::tx::prologue

        begin
            # prepare the transaction
            exec.prologue::prepare_transaction

            # push the new VALUE
            push.{new_value}

            # push the new KEY
            push.{new_key}

            # push the account storage item index
            push.{item_index}

            # set the map item
            exec.account::set_map_item

            # double check that on storage slot is indeed the new map
            push.{item_index}
            exec.account::get_item

        end
        ",
        item_index = storage_item.index,
        new_key = prepare_word(&new_key),
        new_value = prepare_word(&new_value),
    );

    let transaction = prepare_transaction(tx_inputs, tx_args, code.as_str(), None);
    let process = run_tx(&transaction).unwrap();

    let mut new_storage_map = storage_map_2();
    new_storage_map.insert(new_key, new_value);

    // check the new storage root in the process state is what we expect
    assert_eq!(new_storage_map.root(), RpoDigest::from(process.get_stack_word(0)));

    // check the old storage root in the process state is what we expect
    assert_eq!(storage_item.slot.value, process.get_stack_word(1));
}

// ACCOUNT VAULT TESTS
// ================================================================================================

#[test]
fn test_get_vault_commitment() {
    let (tx_inputs, tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

    let account = tx_inputs.account();
    let code = format!(
        "
    use.miden::account
    use.miden::kernels::tx::prologue

    begin
        # prepare the transaction
        exec.prologue::prepare_transaction

        # push the new storage item onto the stack
        exec.account::get_vault_commitment
        push.{expected_vault_commitment}
        assert_eqw
    end
    ",
        expected_vault_commitment = prepare_word(&account.vault().commitment()),
    );

    let transaction = prepare_transaction(tx_inputs, tx_args, &code, None);
    let _process = run_tx(&transaction).unwrap();
}

// PROCEDURE AUTHENTICATION TESTS
// ================================================================================================

#[test]
fn test_authenticate_procedure() {
    let (tx_inputs, _tx_args) =
        mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);
    let account = tx_inputs.account();

    let proc0_index = LeafIndex::new(0).unwrap();
    let proc1_index = LeafIndex::new(1).unwrap();

    let test_cases = vec![
        (account.code().procedure_tree().get_leaf(&proc0_index), true),
        (account.code().procedure_tree().get_leaf(&proc1_index), true),
        ([ONE, ZERO, ONE, ZERO], false),
    ];

    for (root, valid) in test_cases.into_iter() {
        let (tx_inputs, tx_args) =
            mock_inputs(MockAccountType::StandardExisting, AssetPreservationStatus::Preserved);

        let code = format!(
            "\
            use.miden::kernels::tx::account
            use.miden::kernels::tx::prologue

            begin
                # prepare the transaction
                exec.prologue::prepare_transaction

                # push test procedure root onto stack
                push.{root}

                # authenticate procedure
                exec.account::authenticate_procedure
            end
        ",
            root = prepare_word(&root)
        );

        let transaction = prepare_transaction(tx_inputs, tx_args, &code, None);
        let process = run_tx(&transaction);

        match valid {
            true => assert!(process.is_ok()),
            false => assert!(process.is_err()),
        }
    }
}
