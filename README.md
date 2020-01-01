<p align="center"><img src="assets/ttk91rs-logo.svg" /></p>
<p align="center">
  <a href="https://travis-ci.com/dogamak/ttk91-rs">
    <img src="https://travis-ci.com/dogamak/ttk91-rs.svg?branch=master" />
  </a>
  <img src="https://docs.rs/ttk91/badge.svg" />
  <img src="https://img.shields.io/crates/v/ttk91.svg" />
</p>

## Overview

The `ttk91` crate provides a library for dealing with TTK91 bytecode and symbolic assembly files,
compiling assembly to bytecode and executing bytecode. The crate also includes tools
for doing these tasks from the command-line. The [`ttk91-wasm`](https://github.com/dogamak/ttk91-wasm) crate provides a (limited) WebAssembly interface for this crate, via which [`ttk91-web`](https://github.com/dogamak/ttk91-web) uses this crate.

## Features

- Parse files containing TTK91 bytecode and assembly
- Compile symbolic assembly into bytecode
- Generate source map for the bytecode
- Execute bytecode
- Extensible IO and Memory interfaces
- [Command-line utilities](#command-line-utilities)

## Example
```rust
use ttk91::{
    symbolic::Program,
    emulator::{Emulator, StdIo, Memory},
};

fn main() {
    // Simple TTK91 program that adds 13 and 15 together and outputs the answer.
    let symbolic_source = r#"
        ;; DATA
        X       DC      13
        Y       DC      15

        ;; CODE
        MAIN 	LOAD 	R1, X
                ADD 	R1, Y
                OUT 	R1, =CRT
                SVC 	SP, =HALT
    "#;

    // Parse the symbolic assembly into symbolic IR.
    let symbolic = Program::parse(symbolic_source).unwrap();

    // Translate the symbolic IR into bytecode IR.
    let compiled = symbolic.compile();

    // Convert the bytecode IR to bytecode.
    let memory = compiled.to_words();

    // Load the bytecode into an emulator which uses the standard output.
    let mut emulator = Emulator::new(memory, StdIo);

    // Execute the bytecode.
    emulator.run()
        .expect("an error occured while emulating the program");
}
```


## Command-line utilities

### `ttk91repl`
The `ttk91repl` provides a Read-Execute-Print-Loop environment for the TTK91 symbolic assembly
language. It supports alternating between writing and executing code and provides multiple
commands suitable for debugging both TTK91 programs and the emulator itself.

```text
0x8000> LOAD  R1, =5
0x8001> OUT   R1, =CRT
5
0x0002> .register r1
Register R1 = 5
0x8002> SUB   R1, =1
0x8003> JNZER R1, 0x8001
4
3
2
1
0x8004> 
```

### `ttk91run`
Runs TTK91 programs with input and output piped to standard streams.
If the supplied file contains assembly, compiles it to bytecode before executing it.

```shell
$ ttk91run tests/hello.b91
28
```

