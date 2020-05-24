use ttk91::{bytecode::Program, emulator::Emulator, symbolic};

fn read_program() -> Program {
    let bytecode_file = include_str!("hello.b91");

    Program::parse(bytecode_file).unwrap()
}

#[test]
fn test_hello_read_program() {
    let p = read_program();

    assert_eq!(p.code.start, 0);
    assert_eq!(
        p.code.content,
        vec![36175876, 287834117, 69206016, 1891631115,]
    );

    assert_eq!(p.data.start, 4);
    assert_eq!(p.data.content, vec![13, 15]);

    use ttk91::symbol_table::Value;

    assert_eq!(
        p.symbol_table
            .symbol_by_label("halt")
            .unwrap()
            .get::<Value>()
            .as_ref(),
        &Some(11i32)
    );
    assert_eq!(
        p.symbol_table
            .symbol_by_label("crt")
            .unwrap()
            .get::<Value>()
            .as_ref(),
        &Some(0i32)
    );
    assert_eq!(
        p.symbol_table
            .symbol_by_label("x")
            .unwrap()
            .get::<Value>()
            .as_ref(),
        &Some(4i32)
    );
    assert_eq!(
        p.symbol_table
            .symbol_by_label("y")
            .unwrap()
            .get::<Value>()
            .as_ref(),
        &Some(5i32)
    );
    assert_eq!(
        p.symbol_table
            .symbol_by_label("main")
            .unwrap()
            .get::<Value>()
            .as_ref(),
        &Some(0i32)
    );
}

fn compile_program() -> Program {
    let symbolic_source = include_str!("hello.k91");

    let sprog = symbolic::Program::parse(symbolic_source).expect("could not parse hello.k91");

    println!("{:?}", sprog);

    sprog.compile()
}

#[test]
fn test_hello_emulate_symbolic_program() {
    let p = compile_program();

    for word in &p.clone().to_words() {
        println!("W> {:b}", word);
    }

    let mut io = TestIo::new();

    let mut e = Emulator::new(p.to_words(), &mut io).unwrap();

    while !e.halted {
        println!("{:?}", e.get_current_instruction());
        e.step().unwrap();
        println!("{:?}", e.context);
        println!("{:?}", p.symbol_table);
        /*for (symbol, addr) in &p.symbol_table {
            match e.memory.get_data(*addr as u16) {
                Err(()) => println!("  {} = {}", symbol, addr),
                Ok(value) => println!("  {}[{}] = {}", symbol, addr, value),
            }
        }*/
    }

    assert_eq!(io.into_output(), [28]);
}

use ttk91::emulator::TestIo;

#[test]
fn test_hello_emulate_program() {
    let p = read_program();

    let mut io = TestIo::new(); //with_input(input);

    let mut e = Emulator::new(p.to_words(), &mut io).unwrap();

    while !e.halted {
        println!("{:?}", e.get_current_instruction());
        e.step().unwrap();
        println!("{:?}", e.context);
        println!("{:?}", p.symbol_table);
        println!("{:?}", p.symbol_table);
        /*for (symbol, addr) in &p.symbol_table {
            match e.memory.get_data(*addr as u16) {
                Err(()) => println!("  {} = {}", symbol, addr),
                Ok(value) => println!("  {}[{}] = {}", symbol, addr, value),
            }
        }*/
    }

    assert_eq!(io.into_output(), [28]);
}
