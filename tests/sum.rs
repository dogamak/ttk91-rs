use ttk91::{
    bytecode::Program,
    emulator::{Emulator, TestIo},
};

fn read_program() -> Program {
    let bytecode_file = include_str!("sum.b91");

    Program::parse(bytecode_file).unwrap()
}

#[test]
fn test_sum_read_program() {
    let p = read_program();

    assert_eq!(p.code.start, 0);
    assert_eq!(p.code.content, vec![
        52428801,
        18874378,
        572522503,
        36175883,
        287834122,
        18874379,
        536870912,
        36175883,
        69206016,
        1891631115,
    ]);

    assert_eq!(p.data.start, 10);
    assert_eq!(p.data.content, vec![ 0, 0 ]);

    use ttk91::symbol_table::Address;

    assert_eq!(p.symbol_table.get_symbol_by_label("kbd").unwrap().get::<Address>().as_ref(), &Some(1u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("crt").unwrap().get::<Address>().as_ref(), &Some(0u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("summa").unwrap().get::<Address>().as_ref(), &Some(11u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("done").unwrap().get::<Address>().as_ref(), &Some(7u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("sum").unwrap().get::<Address>().as_ref(), &Some(0u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("luku").unwrap().get::<Address>().as_ref(), &Some(10u16));
    assert_eq!(p.symbol_table.get_symbol_by_label("halt").unwrap().get::<Address>().as_ref(), &Some(11u16));
}

#[test]
fn test_sum_emulate_program() {
    let p = read_program();
    let m = p.to_words();

    let cases = vec![
        (vec![1,2,3,4,0], vec![1+2+3+4]),
        (vec![0], vec![0]),
        (vec![1,10,100,1000,10000,0], vec![11111]),
    ];

    for (input, output) in cases {
        let mut io = TestIo::with_input(input);

        let mut e = Emulator::new(m.clone(), &mut io).unwrap();

        while !e.halted {
            println!("{:?}", e.get_current_instruction());
            e.step().unwrap();
            println!("{:?}", e.context);
            println!("{:?}", p.symbol_table);
            // for (symbol, addr) in &p.symbol_table {
            //     println!("  {}[{}] = {}", symbol, addr, e.memory.get_data(*addr as u16).unwrap());
            // }
        }

        assert_eq!(io.into_output(), output);
    }
}
