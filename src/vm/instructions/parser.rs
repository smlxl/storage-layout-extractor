//! This module contains the parser definition for turning a stream of bytes
//! into an [`super::InstructionStream`].
//!
//! # Implementation Note
//!
//! While it might make sense in the future to build a more robust parser based
//! on parser combinators from a library like [`nom`](https://docs.rs/nom), for
//! now it makes sense to stick to a simple system.

use std::rc::Rc;

use crate::{
    constant::{
        DUP_OPCODE_BASE_VALUE,
        LOG_OPCODE_BASE_VALUE,
        PUSH_OPCODE_BASE_VALUE,
        PUSH_OPCODE_MAX_BYTES,
        SWAP_OPCODE_BASE_VALUE,
    },
    error::ParseError,
    opcode::{
        arithmetic as arith,
        control,
        environment as env,
        logic,
        memory as mem,
        DynOpcode,
        Opcode,
    },
};

/// Parse the input `bytes` into a vector of [`Opcode`]s, returning a reasonable
/// parser error if parsing fails.
///
/// This is a disassembly process.
///
/// # Errors
///
/// When one of the `bytes` cannot be parsed as a valid opcode, or when `bytes`
/// is empty.
pub fn parse(bytes: &[u8]) -> anyhow::Result<Vec<DynOpcode>> {
    if bytes.is_empty() {
        return Err(ParseError::EmptyBytecode.into());
    }

    let mut opcodes: Vec<DynOpcode> = Vec::with_capacity(bytes.len());
    let ops = &mut opcodes;
    let mut push_size: u8 = 0;
    let mut push_size_bytes: u8 = push_size;
    let mut push_bytes: Vec<u8> = Vec::with_capacity(PUSH_OPCODE_MAX_BYTES as usize);

    // Iterate over the bytes, parsing into Opcodes as necessary.
    for byte in bytes.iter() {
        if push_size_bytes != 0 {
            // While we have bytes remaining as part of the push opcode we want to consume
            // them.
            push_bytes.push(*byte);
            push_size_bytes -= 1;

            if push_size_bytes == 0 && !push_bytes.is_empty() {
                // If the push bytes buffer has data in it and there are no more bytes to read
                // we want to construct the opcode.
                let opcode = mem::PushN::new(push_size, push_bytes.clone())?;
                add_op(ops, opcode);

                // To maintain correct byte offsets in the instruction stream (a correspondence
                // of bytes to instructions), we need to add a number of no-ops equal to the
                // size of the push's data.
                for _ in 0..push_size {
                    add_op(ops, control::Nop);
                }

                // Now we can zero out our state variables.
                push_bytes.clear();
                push_size = 0;
            }
        } else {
            // Now we can match the next byte and process the opcode.
            match byte {
                0x00 => add_op(ops, control::Stop),
                0x01 => add_op(ops, arith::Add),
                0x02 => add_op(ops, arith::Mul),
                0x03 => add_op(ops, arith::Sub),
                0x04 => add_op(ops, arith::Div),
                0x05 => add_op(ops, arith::SDiv),
                0x06 => add_op(ops, arith::Mod),
                0x07 => add_op(ops, arith::SMod),
                0x08 => add_op(ops, arith::AddMod),
                0x09 => add_op(ops, arith::MulMod),
                0x0a => add_op(ops, arith::Exp),
                0x0b => add_op(ops, arith::SignExtend),
                0x10 => add_op(ops, logic::Lt),
                0x11 => add_op(ops, logic::Gt),
                0x12 => add_op(ops, logic::SLt),
                0x13 => add_op(ops, logic::SGt),
                0x14 => add_op(ops, logic::Eq),
                0x15 => add_op(ops, logic::IsZero),
                0x16 => add_op(ops, logic::And),
                0x17 => add_op(ops, logic::Or),
                0x18 => add_op(ops, logic::Xor),
                0x19 => add_op(ops, logic::Not),
                0x1a => add_op(ops, logic::Byte),
                0x1b => add_op(ops, logic::Shl),
                0x1c => add_op(ops, logic::Shr),
                0x1d => add_op(ops, logic::Sar),
                0x20 => add_op(ops, env::Sha3),
                0x30 => add_op(ops, env::Address),
                0x31 => add_op(ops, env::Balance),
                0x32 => add_op(ops, env::Origin),
                0x33 => add_op(ops, env::Caller),
                0x34 => add_op(ops, env::CallValue),
                0x35 => add_op(ops, mem::CallDataLoad),
                0x36 => add_op(ops, mem::CallDataSize),
                0x37 => add_op(ops, mem::CallDataCopy),
                0x38 => add_op(ops, mem::CodeSize),
                0x39 => add_op(ops, mem::CodeCopy),
                0x3a => add_op(ops, env::GasPrice),
                0x3b => add_op(ops, mem::ExtCodeSize),
                0x3c => add_op(ops, mem::ExtCodeCopy),
                0x3d => add_op(ops, mem::ReturnDataSize),
                0x3e => add_op(ops, mem::ReturnDataCopy),
                0x3f => add_op(ops, env::ExtCodeHash),
                0x40 => add_op(ops, env::BlockHash),
                0x41 => add_op(ops, env::CoinBase),
                0x42 => add_op(ops, env::Timestamp),
                0x43 => add_op(ops, env::Number),
                0x44 => add_op(ops, env::Prevrandao),
                0x45 => add_op(ops, env::GasLimit),
                0x46 => add_op(ops, env::ChainId),
                0x47 => add_op(ops, env::SelfBalance),
                0x48 => add_op(ops, env::BaseFee),
                0x50 => add_op(ops, mem::Pop),
                0x51 => add_op(ops, mem::MLoad),
                0x52 => add_op(ops, mem::MStore),
                0x53 => add_op(ops, mem::MStore8),
                0x54 => add_op(ops, mem::SLoad),
                0x55 => add_op(ops, mem::SStore),
                0x56 => add_op(ops, control::Jump),
                0x57 => add_op(ops, control::JumpI),
                0x58 => add_op(ops, control::PC),
                0x59 => add_op(ops, mem::MSize),
                0x5a => add_op(ops, env::Gas),
                0x5f => add_op(ops, mem::Push0),
                0x60..=0x7f => {
                    push_size = byte - PUSH_OPCODE_BASE_VALUE;
                    push_size_bytes = push_size;
                }
                0x80..=0x8f => {
                    let item_to_duplicate = byte - DUP_OPCODE_BASE_VALUE;
                    let opcode = mem::DupN::new(item_to_duplicate)?;
                    add_op(ops, opcode);
                }
                0x90..=0x9f => {
                    let item_to_swap_with = byte - SWAP_OPCODE_BASE_VALUE;
                    let opcode = mem::SwapN::new(item_to_swap_with)?;
                    add_op(ops, opcode);
                }
                0xa0..=0xa4 => {
                    let topic_count = byte - LOG_OPCODE_BASE_VALUE;
                    let opcode = env::LogN::new(topic_count)?;
                    add_op(ops, opcode)
                }
                0xf0 => add_op(ops, env::Create),
                0xf1 => add_op(ops, control::Call),
                0xf2 => add_op(ops, control::CallCode),
                0xf3 => add_op(ops, control::Return),
                0xf4 => add_op(ops, control::DelegateCall),
                0xf5 => add_op(ops, env::Create2),
                0xfa => add_op(ops, control::StaticCall),
                0xfd => add_op(ops, control::Revert),
                0xfe => add_op(ops, control::Invalid),
                0xff => add_op(ops, env::SelfDestruct),
                _ => return Err(ParseError::InvalidOpcode(*byte).into()),
            }
        }
    }

    Ok(opcodes)
}

/// Adds an operation `elem` to the array of opcodes `ops`.
fn add_op<T: Opcode>(ops: &mut Vec<DynOpcode>, elem: T) {
    ops.push(Rc::new(elem))
}
