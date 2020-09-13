//! Compilation from assembly source to bytecode.

use std::collections::HashMap;

use crate::symbol_table::{SymbolId, SymbolTable, Value, Property};
use crate::symbolic;
use crate::parsing::Span;
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
    fn pseudo_instruction(&mut self, instruction: PseudoInstruction, span: Option<Span>) -> Result<(), Self::Error>;

    /// Handle a label.
    fn insert_label(&mut self, symbol: SymbolId) -> Result<(), Self::Error>;

    /// Emit an instruction.
    fn insert_instruction(&mut self, instruction: RealInstruction, span: Option<Span>) -> Result<(), Self::Error>;

    /// Finalize the compilation and return the artifact.
    fn finish(&mut self) -> Result<Self::Artifact, Self::Error>;
} 

/// Backend that produces the internal representation of the program.
#[derive(Debug, Clone, Default)]
pub struct IrBackend {
    code: Vec<u32>,
    data: Vec<i32>,
    labels: Vec<SymbolId>,
    relocation_table: Vec<(usize, SymbolId)>,
    source_map: HashMap<BytecodeLocation, Span>,
    symbol_table: SymbolTable,
}

/// A TTK91 program has generally two memory segments: the code segment at the beginning of the
/// memory and the following data segment.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

    fn pseudo_instruction(&mut self, instruction: PseudoInstruction, span: Option<Span>) -> Result<(), ()> {
        println!("Pseudo: {:?}", instruction);
        let location = (BytecodeSegment::Data, self.data.len());

        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some(location.clone()));
        }

        if let Some(span) = span {
            self.source_map.insert(location, span);
        }

        let words = std::iter::repeat(instruction.value).take(instruction.size as usize);
        self.data.extend(words);
        Ok(())
    }

    fn insert_label(&mut self, symbol: SymbolId) -> Result<(), ()> {
        self.labels.push(symbol);
        Ok(())
    }

    fn insert_instruction(&mut self, instruction: RealInstruction, span: Option<Span>) -> Result<(), ()> {
        println!("Real: {:?}", instruction);
        if let symbolic::ast::Value::Symbol(sym) = instruction.operand2.value {
            self.relocation_table.push((self.code.len(), sym));
        }

        let ins: BytecodeInstruction = instruction.into();
        let location = (BytecodeSegment::Code, self.code.len());

        for label in self.labels.drain(..) {
            self.symbol_table.symbol_mut(label)
                .set::<BytecodeLocation>(Some(location.clone()));
        }

        self.code.push(ins.into());

        if let Some(span) = span {
            self.source_map.insert(location, span);
        }

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

        let source_map = self.source_map.iter()
            .map(|(loc, span)| {
                let addr = match loc {
                    (BytecodeSegment::Code, off) => *off,
                    (BytecodeSegment::Data, off) => self.code.len() + *off,
                };

                (addr, span.clone())
            })
            .collect();

        let symbol_table = std::mem::take(&mut self.symbol_table);
        let data = std::mem::take(&mut self.data);
        let code = std::mem::take(&mut self.code);

        Ok(Program {
            symbol_table,
            source_map,
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
                backend.insert_instruction(sym_ins, entry.span)?,
            SymbolicInstruction::Pseudo(ins) =>
                backend.pseudo_instruction(ins, entry.span)?,
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
