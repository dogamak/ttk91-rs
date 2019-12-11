//! Compilation from assembly source to bytecode.

use crate::symbolic::{
    self,
    program::{
        RelocationKind,
        SymbolicInstruction,
    },
};
use crate::bytecode::{Segment, Program};
use crate::instruction::Instruction;

use std::collections::HashMap;
use std::convert::TryInto;

/// Represents the type of a memory segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SegmentType {
    /// Segment that contains program instructions.
    /// Pushed words are guaranteed to be in consecutive addresses.
    Text,

    /// Segment that contains data.
    /// Pushed words have no guarantee about their location.
    Data,
}

/// Defines an interface for a data structure into which bytecode can be compiled.
pub trait CompileTarget: Sized {
    /// Represents a position in the data structure.
    /// This should not change even if new instructions or data is pushed to the data structure.
    /// The actual address of this location in the produced memory dump can change.
    type Location: Clone;

    /// Create an empty instance of itself.
    fn create() -> Self;

    /// Create an empty instance of itself with reserved capacity for `size` words of data.
    /// This is just a request or a hint, so this doesn't need to be actually implemented if
    /// the data structure doesn't support this.
    ///
    /// The provided default implementation is a call to [CompileTarget::create].
    fn with_capacity(_size: u16) -> Self {
        Self::create()
    }

    /// Finalize the compilation.
    /// The compiler will not modify the data structure after this.
    fn finish(self) -> Self {
        self
    }

    /// Sets the word in the location `addr` to value `word`.
    fn set_word(&mut self, addr: &Self::Location, word: i32);

    /// Pushes a new word to the data structure.
    /// The only requirement for the location of the word is that words pushed with segment type
    /// [SegmentType::Text] need to be in consecutive addresses.
    ///
    /// # Parameters
    /// - `source_line`: The line number of the instruction in the symbolic assembly source.
    /// - `word`: Value for the word.
    /// - `segment`: Type of the data. Affects the words location in the memory dump.
    fn push_word(&mut self, source_line: Option<usize>, word: i32, segment: SegmentType) -> Self::Location;

    /// Declares a new symbol with label `label` in location `address`.
    fn new_symbol(&mut self, label: String, address: &Self::Location);

    /// Translates the location `loc` into a word offset in the memory dump.
    /// The location can change after calls to [push_word](CompileTarget::push_word).
    fn to_address(&self, loc: &Self::Location) -> u16;
}

impl Program {
    fn move_symbols_after(&mut self, addr: u16) {
        for (_key, value) in self.symbol_table.iter_mut() {
            if *value >= addr {
                *value += 1;
            }
        }
    }
}

impl CompileTarget for Program {
    type Location = (SegmentType, usize);

    fn create() -> Program {
        Program {
            code: Segment {
                content: Vec::new(),
                start: 0,
            },
            data: Segment {
                content: Vec::new(),
                start: 0,
            },
            symbol_table: HashMap::new(),
        }
    }

    fn push_word(
        &mut self,
        _source_line: Option<usize>,
        word: i32,
        segment: SegmentType,
    ) -> Self::Location {
        let (abs_addr, rel_addr) = match segment {
            SegmentType::Text => {
                self.code.content.push(word as u32);
                self.data.start += 1;
                (self.code.content.len() - 1, self.code.content.len() - 1)
            },
            SegmentType::Data => {
                self.data.content.push(word as u32);
                (self.code.content.len() + self.data.content.len() - 1, self.data.content.len() - 1)
            },
        };

        self.move_symbols_after(abs_addr as u16);

        (segment, rel_addr)
    }

    fn set_word(&mut self, (segment, addr): &Self::Location, value: i32) {
        match segment {
            SegmentType::Text => self.code.content[*addr] = value as u32,
            SegmentType::Data => self.data.content[*addr] = value as u32,
        }
    }

    fn new_symbol(&mut self, label: String, (segment, mut addr): &Self::Location) {
        if *segment == SegmentType::Data {
            addr += self.code.content.len();
        }

        println!("Add label '{}': {}", label, addr);

        self.symbol_table.insert(label, addr as u16);
    }

    fn to_address(&self, loc: &Self::Location) -> u16 {
        match loc {
            (SegmentType::Text, addr) => *addr as u16,
            (SegmentType::Data, addr) => (addr + self.data.start) as u16,
        }
    }
}

/// Captures line number information produced during the compilation process
/// and produces a mapping from memory locations into source assembly line numbers.
///
/// Line numbers for both instructions and symbols are included.
pub struct SourceMap<T: CompileTarget> {
    /// The actual artifact of the compilation.
    pub compiled: T,

    tmp: HashMap<T::Location, usize>,

    /// Map from memory locations into source assembly line numbers.
    pub source_map: HashMap<u16, usize>,
}

impl<T> CompileTarget for SourceMap<T>
    where T: CompileTarget,
          T::Location: std::hash::Hash + std::cmp::Eq + Clone,
{
    type Location = T::Location;

    fn create() -> Self {
        SourceMap {
            compiled: T::create(),
            tmp: HashMap::new(),
            source_map: HashMap::new(),
        }
    }

    fn set_word(&mut self, loc: &Self::Location, word: i32) {
        self.compiled.set_word(loc, word);
    }

    fn push_word(&mut self, source_line: Option<usize>, word: i32, segment: SegmentType) -> Self::Location {
        let loc = self.compiled.push_word(source_line, word, segment);

        if let Some(line) = source_line {
            self.tmp.insert(loc.clone(), line);
        }

        loc
    }

    fn new_symbol(&mut self, label: String, loc: &Self::Location) {
        self.compiled.new_symbol(label, loc);
    }

    fn to_address(&self, loc: &Self::Location) -> u16 {
        self.compiled.to_address(loc)
    }

    fn finish(mut self) -> Self {
        let mut map = HashMap::new();

        for (loc, source) in self.tmp.drain() {
            let addr = self.compiled.to_address(&loc);
            map.insert(addr, source);
        }

        self.source_map = map;

        self
    }
}

/// Compiles the given assembly program into bytecode.
/// Supports compilation into multiple data structures, but most often the compilation target is
/// [crate::bytecode::Program] possibly in combination with [SourceMap].
pub fn compile<T: CompileTarget>(symprog: symbolic::Program) -> T {
    let mut target = T::create();

    let mut relocation_table = HashMap::<String, Vec<(T::Location, Instruction)>>::new();
    let mut symbol_table = HashMap::new();

    for entry in symprog.instructions {
        match entry.instruction {
            SymbolicInstruction::Concrete(sym_ins) => {
                let ins: Instruction = sym_ins.clone().into();
                let word: u32 = ins.clone().into();

                let loc = target.push_word(
                    Some(entry.source_line),
                    word as i32,
                    SegmentType::Text,
                );

                if let Some(reloc) = sym_ins.relocation_symbol() {
                    relocation_table
                        .entry(reloc.symbol)
                        .or_default()
                        .push((loc.clone(), ins));
                }

                if let Some(label) = entry.label {
                    target.new_symbol(label.clone(), &loc);
                    symbol_table.insert(label, loc);
                }
            },
            SymbolicInstruction::Pseudo(ins) => {
                let loc = target.push_word(
                    Some(entry.source_line),
                    ins.value,
                    SegmentType::Data,
                );

                if let Some(label) = entry.label {
                    target.new_symbol(label.clone(), &loc);
                    symbol_table.insert(label, loc);
                }

                for _ in 0..ins.size-1 {
                    target.push_word(
                        Some(entry.source_line),
                        ins.value,
                        SegmentType::Data,
                    );
                }
            },
        }
    }

    for (label, locs) in relocation_table {
        let addr = match label.as_str() {
            "CRT" => 0,
            "KBD" => 0,
            "HALT" => 11,
            _ => {
                let sym_loc = symbol_table.get(&label).unwrap();
                target.to_address(sym_loc)
            },
        };

        for (ins_loc, mut ins) in locs {
            ins.immediate = addr;
            let word: u32 = ins.into();

            target.set_word(
                &ins_loc,
                word as i32,
            );
        }
    }
    
    target.finish()
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

    let prog: crate::bytecode::Program = compile(program);

    use std::convert::TryFrom;

    for word in &prog.code.content {
        println!("W> {:b}", word);
    }

    let ins = prog.code.content.iter()
        .map(|word| Instruction::try_from(*word).unwrap())
        .collect::<Vec<_>>();

    println!("{:?}", ins);

    println!("{:?}", prog);
}

#[test]
fn test_compile_sourcemap() {
    use crate::{symbolic, bytecode};

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

    let program = symbolic::Program::parse(source).unwrap();
    let prog: SourceMap<bytecode::Program> = compile(program);

    assert_eq!(prog.source_map.get(&0), Some(&8));
    assert_eq!(prog.source_map.get(&1), Some(&9));
    assert_eq!(prog.source_map.get(&2), Some(&10));
    assert_eq!(prog.source_map.get(&3), Some(&11));
    assert_eq!(prog.source_map.get(&4), Some(&2));
    assert_eq!(prog.source_map.get(&5), Some(&3));

    println!("{:?}", prog.compiled);
}
