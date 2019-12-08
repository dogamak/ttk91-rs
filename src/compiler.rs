use crate::symbolic::{self, program::RelocationKind};
use crate::bytecode::{Segment, Program};
use crate::instruction::Instruction;

use std::collections::HashMap;
use std::convert::TryInto;

pub fn compile(symprog: symbolic::Program) -> Program {
    let mut relocation_table = Vec::new();

    for (label, ins) in &symprog.instructions {
        if let Some(entry) = ins.relocation_symbol() {
            relocation_table.push(entry);
        }
    }

    let mut symbol_table = HashMap::new();
    let mut data = Vec::new();

    symbol_table.insert("CRT".to_string(), 0);
    symbol_table.insert("HALT".to_string(), 11);

    for (symbol, ins) in &symprog.init_table {
        let addr = data.len();

        for _ in 0..ins.size {
            data.push(ins.value as u32);
        }

        if let Some(symbol) = symbol {
            symbol_table.insert(symbol.clone(), addr as u16);
        }
    }

    let mut instructions = symprog.instructions
        .iter()
        .map(|(_label, ins)| ins)
        .cloned()
        .map(Into::into)
        .collect::<Vec<Instruction>>();

    for (i, (label, ins)) in symprog.instructions.iter().enumerate() {
        if let Some(label) = label {
            symbol_table.insert(label.to_string(), i as u16);
        }

        match ins.relocation_symbol() {
            None => {},
            Some(entry) => {
                let addr = *symbol_table.get(&entry.symbol).unwrap();

                let imm = match entry.kind {
                    RelocationKind::Address => addr,
                    RelocationKind::Value => data[addr as usize] as u16,
                };

                instructions[i].immediate = imm;
            },
        }
    }

    let bytecode = instructions.into_iter().map(Into::into).collect(); 

    Program {
        symbol_table,
        code: Segment {
            start: data.len(),
            content: bytecode,
        },
        data: Segment {
            start: 0,
            content: data,
        },
    }
}

#[test]
fn test_compile() {
    use crate::symbolic::parser::parse_symbolic_file;

    let source = r#"
X 	DC 	13
Y 	DC 	15

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; hello.k91 - print 28
;
MAIN 	LOAD 	R1, X
        ADD 	R1, Y
	    OUT 	R1, =CRT
	    SVC 	SP, =HALT
    "#;

    let program = crate::symbolic::Program::parse(source).unwrap();
    println!("{:?}", program.instructions);

    let prog = compile(program);

    use std::convert::TryFrom;

    let ins = prog.code.content.iter()
        .map(|word| Instruction::try_from(*word).unwrap())
        .collect::<Vec<_>>();

    println!("{:?}", ins);

    println!("{:?}", prog);
}
