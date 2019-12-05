# TTK91 Rust Toolkit

The `ttk91` crate provides a library for dealing with TTK91 bytecode nad symbolic assembly files
compiling assembly to bytecode and executing bytecode. The crate also includes command-line tools
for doing these tasks from the terminal.

## Using the library
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


## Executables

### `ttk91repl`
The `ttk91repl` provides a Read-Execute-Print-Loop environment for the TTK91 symbolic assembly
language. It supports alternating between writing and executing code and provides multiple
commands suitable for debugging.

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
$ ttk91run tests/hello.k91
28
```

