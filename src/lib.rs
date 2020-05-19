//! A create for doing anything related to the imaginary TTK91 instruction architecture used in
//! teaching at University of Helsinki.
//!
//! Currently this crate provides the functionality to:
//! - Read and write `.b91` files containing TTK91 bytecode.
//! - Read and write `.k91` files containing TTK91 symbolic assembly.
//! - Compile bytecode from symbolic TTK91 assembly.
//! - Execute bytecode.
//!
//! # Future plans
//!
//! - `ttk91run` and `ttk91compile` executables
//! - WebAssembly interface for GUI
//! - Translating TTK91 bytecode into x86 instructions
//!   - Writing them to a `.o` file for linking
//! - Go above and beyond the original TTK91
//!   - String variables
//!   - Interruptions
//!   - Assembler macros
//! - Multiple crates? (`ttk91`, `ttk91-emulator`, `ttk91-wasm`)
//!
//! # Unimplemented stuff
//! - Stack and related instructions (`PUSH`, `POP`, `CALL`, `EXIT`, `PUSHR`, `POPR`)
//! - Labels for instructions in `ttk91repl`
//!
//! # Example
//! ```
//! use ttk91::{
//!     symbolic::Program,
//!     emulator::{Emulator, StdIo, Memory},
//! };
//!
//! fn main() {
//!     // Simple TTK91 program that adds 13 and 15 together and outputs the answer.
//!     let symbolic_source = r#"
//!         ;; DATA
//!         X       DC      13
//!         Y       DC      15
//!
//!         ;; CODE
//!         MAIN 	LOAD 	R1, X
//!                 ADD 	R1, Y
//!                 OUT 	R1, =CRT
//!                 SVC 	SP, =HALT
//!     "#;
//!
//!     // Parse the symbolic assembly into symbolic IR.
//!     let symbolic = Program::parse(symbolic_source).unwrap();
//!
//!     // Translate the symbolic IR into bytecode IR.
//!     let compiled = symbolic.compile();
//!
//!     // Convert the bytecode IR to bytecode.
//!     let memory = compiled.to_words();
//!
//!     // Load the bytecode into an emulator which uses the standard output.
//!     let mut emulator = Emulator::new(memory, StdIo)
//!         .expect("could not initialize emulator");
//!
//!     // Execute the bytecode.
//!     emulator.run()
//!         .expect("an error occured while emulating the program");
//! }
//! ```
//!
//! # Executables
//!
//! ## `ttk91repl`
//!
//! The `ttk91repl` provides a Read-Execute-Print-Loop environment for the TTK91 symbolic assembly
//! language. It supports alternating between writing and executing code and provides multiple
//! commands suitable for debugging.
//!
//! ```text
//! 0x8000> LOAD  R1, =5
//! 0x8001> OUT   R1, =CRT
//! 5
//! 0x0002> .register r1
//! Register R1 = 5
//! 0x8002> SUB   R1, =1
//! 0x8003> JNZER R1, 0x8001
//! 4
//! 3
//! 2
//! 1
//! 0x8004> 
//! ```
//!
//! ## `ttk91run`
//! ## `ttk91compile`
pub mod parsing;
pub mod symbol_table;
pub mod emulator;
pub mod instruction;
pub mod bytecode;
pub mod symbolic;
pub mod compiler;
pub mod error;
pub mod event;

//pub use emulator::{Memory, Emulator};
//pub use program::Program;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
