//! Compilation from assembly source to bytecode.

use crate::symbol_table::{SymbolId, SymbolTable, Value, Property};
use crate::symbolic;
use crate::symbolic::program::{
    PseudoInstruction,
    RealInstruction,
    Instruction as SymbolicInstruction,
};

use crate::bytecode::{Program, Segment};
use crate::instruction::Instruction as BytecodeInstruction;

/// Trait for producing compilation artifacts from a series of instructions.
pub trait CompilerBackend {
    /// Type of the artifact created by this backend.
    type Artifact;

    /// Error type which is used by methods of this trait. 
    type Error;

    /// Get a mutable reference to the symbol table.
    fn symbol_table_mut(&mut self) -> &mut SymbolTable;

    /// Handle a pseudo instruction.
    fn pseudo_instruction(&mut self, instruction: PseudoInstruction) -> Result<(), Self::Error>;

    /// Handle a label.
    fn insert_label(&mut self, symbol: SymbolId) -> Result<(), Self::Error>;

    /// Emit an instruction.
    fn insert_instruction(&mut self, instruction: RealInstruction) -> Result<(), Self::Error>;

    /// Finalize the compilation and return the artifact.
    fn finish(&mut self) -> Result<Self::Artifact, Self::Error>;
} 

/// Backend that produces the internal representation of the program.
#[derive(Debug, Clone, Default)]
pub struct IrBackend {
    symbol_table: SymbolTable,
    relocation_table: Vec<(usize, SymbolId)>,
    labels: Vec<SymbolId>,
    data: Vec<i32>,
    code: Vec<u32>,
}

/// A TTK91 program has generally two memory segments: the code segment at the beginning of the
/// memory and the following data segment.
#[derive(Clone, Debug)]
enum BytecodeSegment {
    Code,
    Data,
}

/// Representation of a location in a bytecode artifact. By expressing the location relative to the
/// beginning of the memory segment, the representation remains valid even if new instructions are
/// inserted.
type BytecodeLocation = (BytecodeSegment, usize);

impl Property for BytecodeLocation {
    const NAME: &'static str = "BytecodeLocation";
    type Value = Option<Self>;

    fn default_value() -> Option<Self> {
        None
    }
}

impl CompilerBackend for IrBackend {
    type Artifact = Program;
    type Error = ();

    fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        &mut self.symbol_table
    }

    fn pseudo_instruction(&mut self, instruction: PseudoInstruction) -> Result<(), ()> {
        println!("Pseudo: {:?}", instruction);
        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some((BytecodeSegment::Data, self.data.len())));
        }

        let words = std::iter::repeat(instruction.value).take(instruction.size as usize);
        self.data.extend(words);
        Ok(())
    }

    fn insert_label(&mut self, symbol: SymbolId) -> Result<(), ()> {
        self.labels.push(symbol);
        Ok(())
    }

    fn insert_instruction(&mut self, instruction: RealInstruction) -> Result<(), ()> {
        println!("Real: {:?}", instruction);
        if let symbolic::ast::Value::Symbol(sym) = instruction.operand2.value {
            self.relocation_table.push((self.code.len(), sym));
        }

        let ins: BytecodeInstruction = instruction.into();

        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some((BytecodeSegment::Code, self.code.len())));
        }

        self.code.push(ins.into());

        Ok(())
    }

    fn finish(&mut self) -> Result<Self::Artifact, ()> {
        for symbol in self.symbol_table.iter_mut() {
            if let Some(loc) = symbol.get::<BytecodeLocation>().into_owned() {
                let addr = match loc {
                    (BytecodeSegment::Code, off) => off as i32,
                    (BytecodeSegment::Data, off) => (self.code.len() + off) as i32,
                };
                symbol.set::<Value>(Some(addr));
            }
        }

        for (offset, symbol) in &self.relocation_table {
            let addr = self.symbol_table.symbol(*symbol)
                .get::<Value>()
                .unwrap();

            self.code[*offset] = self.code[*offset] & 0xFFFF0000 | (addr as u32);
        }

        let symbol_table = std::mem::take(&mut self.symbol_table);
        let data = std::mem::take(&mut self.data);
        let code = std::mem::take(&mut self.code);

        Ok(Program {
            symbol_table,
            data: Segment {
                start: code.len(),
                content: data,
            },
            code: Segment {
                start: 0,
                content: code.into_iter().map(|word| word as i32).collect(),
            },
        })
    }
}

/// A backend for producing byte vectors.
#[derive(Default, Clone, Debug)]
pub struct BytecodeBackend {
    symbol_table: SymbolTable,
    relocation_table: Vec<(usize, SymbolId)>,
    labels: Vec<SymbolId>,
    data: Vec<u8>,
    code: Vec<u8>,
}

impl CompilerBackend for BytecodeBackend {
    type Artifact = Vec<u8>;
    type Error = ();

    fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        &mut self.symbol_table
    }

    fn pseudo_instruction(&mut self, instruction: PseudoInstruction) -> Result<(), ()> {
        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some((BytecodeSegment::Data, self.data.len())));
        }

        for _ in 0..instruction.size {
            self.data.extend(&instruction.value.to_le_bytes());
        }

        Ok(())
    }

    fn insert_instruction(&mut self, instruction: RealInstruction) -> Result<(), ()> {
        if let symbolic::ast::Value::Symbol(sym) = instruction.operand2.value {
            self.relocation_table.push((self.code.len() + 2, sym));
        }

        let ins: BytecodeInstruction = instruction.into();

        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some((BytecodeSegment::Code, self.code.len())));
        }

        let word: u32 = ins.into();
        self.code.extend(&word.to_le_bytes());

        Ok(())
    }

    fn insert_label(&mut self, label: SymbolId) -> Result<(), ()> {
        self.labels.push(label);
        Ok(())
    }

    fn finish(&mut self) -> Result<Vec<u8>, ()> {
        for symbol in self.symbol_table.iter_mut() {
            if let Some(loc) = symbol.get::<BytecodeLocation>().into_owned() {
                let addr = match loc {
                    (BytecodeSegment::Code, off) => off as i32,
                    (BytecodeSegment::Data, off) => (self.code.len() + off) as i32,
                };
                symbol.set::<Value>(Some(addr));
            }
        }

        for (offset, symbol) in &self.relocation_table {
            let addr = self.symbol_table.symbol(*symbol)
                .get::<Value>()
                .unwrap();

            let [low, high] = (addr as u16).to_le_bytes();

            self.code[*offset] = low;
            self.code[offset + 1] = high;
        }

        let mut artifact = Vec::with_capacity(self.data.len() + self.code.len());
        artifact.extend(&self.code);
        artifact.extend(&self.data);

        Ok(artifact)
    }
}

/// Compile the program using a given backend.
pub fn compile<B>(mut backend: B, program: symbolic::program::Program)
    -> Result<B::Artifact, B::Error>
where
    B: CompilerBackend,
{
    let symbol_table = backend.symbol_table_mut();
    *symbol_table = program.symbol_table;

    symbol_table.get_or_create("HALT".into())
        .set::<Value>(Some(11));

    symbol_table.get_or_create("CRT".into())
        .set::<Value>(Some(0));

    for entry in program.instructions {
        for label in &entry.labels {
            backend.insert_label(*label)?;
        }

        match entry.instruction {
            SymbolicInstruction::Real(sym_ins) =>
                backend.insert_instruction(sym_ins)?,
            SymbolicInstruction::Pseudo(ins) =>
                backend.pseudo_instruction(ins)?,
        }
    }

    backend.finish()
}

#[test]
fn test_compile() {
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

    let backend: IrBackend = Default::default();
    let prog: Program = compile(backend, program).unwrap();

    use std::convert::TryFrom;

    for word in &prog.code.content {
        println!("W> {:b}", word);
    }

    let ins = prog
        .code
        .content
        .iter()
        .map(|word| BytecodeInstruction::try_from(*word as u32).unwrap())
        .collect::<Vec<_>>();

    println!("{:?}", ins);

    println!("{:?}", prog);
}
