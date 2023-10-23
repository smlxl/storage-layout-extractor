//! This module is an integration test that allows manual poking of the results
//! of the analysis at any point.
#![cfg(test)]

mod common;

#[test]
fn inspect_contract_data() -> anyhow::Result<()> {
    // Set to true if you are debugging
    let should_print = false;

    // Create the extractor
    let contract_path = "./asset/ReplaceMeForTesting.json";
    let extractor = common::new_extractor_from_path(contract_path)?;

    // Disassemble
    let disassembled = extractor.disassemble()?;

    // Prepare the VM
    let execution_ready = disassembled.prepare_vm()?;

    // Execute the VM and display the stored values
    let executed = execution_ready.execute()?;
    let results = &executed.state().execution_result;

    if should_print {
        for (i, state) in results.states.iter().enumerate() {
            if state.storage().keys().is_empty() {
                println!("Skipping empty state {i}");
                continue;
            }

            println!("=== State Number {i} ===");

            let storage_keys = state.storage().keys();

            for key in storage_keys {
                println!("  ===== Slot =====");
                println!("  KEY: {key}");

                let generations = state.storage().generations(key).unwrap();

                for gen in generations {
                    println!("  VALUE: {gen}");
                }
            }

            println!();
        }
    }

    // Prepare the unifier
    let unifier_read = executed.prepare_unifier();

    // Perform unification
    let unification_complete = unifier_read.infer()?;

    // Get the final storage layout for the input contract and print it for
    // debugging
    let layout = unification_complete.layout();
    if should_print {
        dbg!(layout);
    }

    Ok(())
}
