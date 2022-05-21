use std::prelude::v1::*;
use std::rc::Rc;
use std::iter;

use netsblox_ast as ast;

use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;

fn get_running_proc(xml: &str, locals: SymbolTable, ref_pool: &mut RefPool) -> (Process, SymbolTable, SymbolTable, usize) {
    let parser = ast::ParserBuilder::default().build().unwrap();
    let ast = parser.parse(xml).unwrap();
    let (code, locs) = ByteCode::compile(&ast.roles[0]);
    let mut proc = Process::new(Rc::new(code), 1024);
    assert!(!proc.is_running());

    let main = locs.funcs.iter().find(|x| x.0.trans_name.trim() == "main").expect("no main function at global scope");
    proc.initialize(main.1, locals);
    assert!(proc.is_running());

    let globals = SymbolTable::from_globals(&ast.roles[0], ref_pool);
    let fields = SymbolTable::from_fields(&ast.roles[0].sprites[0], ref_pool);

    (proc, globals, fields, main.1)
}

fn run_till_term(proc: &mut Process, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<Option<Value>, ExecError> {
    assert!(proc.is_running());
    let ret = loop {
        match proc.step(ref_pool, globals, fields) {
            StepResult::Idle => panic!(),
            StepResult::Normal | StepResult::Yield => (),
            StepResult::Terminate(e) => break e,
        }
    };
    assert!(!proc.is_running());
    ret
}

//<variable name="field"><l>0</l></variable>

#[test]
fn test_proc_ret() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_ret.xml"),
        methods = "",
    ), SymbolTable::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap().flatten(&ref_pool).unwrap() {
        FlatValue::String(x) => assert_eq!(x, ""),
        x => panic!("{:?}", x),
    }
}

#[test]
fn test_proc_sum_123n() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, main) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_sum_123n.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    for (n, expect) in [(0.0, 0.0), (1.0, 1.0), (2.0, 3.0), (3.0, 6.0), (4.0, 10.0), (5.0, 15.0), (6.0, 21.0)] {
        let mut locals = SymbolTable::default();
        locals.set_or_define("n", n.into());
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
            Value::CopyValue(CopyValue::Number(ret)) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, main) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_recursive_factorial.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    for (n, expect) in [(0.0, 1.0), (1.0, 1.0), (2.0, 2.0), (3.0, 6.0), (4.0, 24.0), (5.0, 120.0), (6.0, 720.0), (7.0, 5040.0)] {
        let mut locals = SymbolTable::default();
        locals.set_or_define("n", n.into());
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
            Value::CopyValue(CopyValue::Number(ret)) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}

// #[test]
fn test_proc_loops_lists_basic() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_loops_lists_basic.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap().flatten(&ref_pool).unwrap() {
        FlatValue::List(x) => {
            let expected = [
                vec![1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0],
                vec![1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0],
                vec![1.0,2.0,3.0,4.0,5.0,6.0,7.0],
                vec![2.0,3.0,4.0,5.0,6.0,7.0],
                vec![3.0,4.0,5.0,6.0,7.0],
                vec![4.0,5.0,6.0,7.0],
                vec![5.0,6.0,7.0],
                vec![6.0,7.0],
                vec![7.0],
                vec![8.0],
                vec![9.0,8.0],
                vec![10.0,9.0,8.0],
                vec![6.5,7.5,8.5,9.5],
                vec![6.5,7.5,8.5],
                vec![6.5,7.5],
                vec![6.5],
                vec![6.5],
                vec![6.5,5.5],
                vec![6.5,5.5,4.5],
                vec![6.5,5.5,4.5,3.5],
                vec![6.5,5.5,4.5,3.5,2.5],
                vec![6.5,5.5,4.5,3.5,2.5,1.5],
            ];
            assert_eq!(x.len(), expected.len());
            for (i, (got, expected)) in iter::zip(x, expected).enumerate() {
                match got.flatten(&ref_pool).unwrap() {
                    FlatValue::List(x) => {
                        assert_eq!(x.len(), expected.len());
                        for (j, (got, expected)) in iter::zip(x, expected).enumerate() {
                            match got {
                                Value::CopyValue(CopyValue::Number(x)) => if *x != expected {
                                    panic!("res[{}][{}] = {}, expected {}", i, j, x, expected);
                                }
                                x => panic!("{:?}", x),
                            }
                        }
                    }
                    x => panic!("{:?}", x),
                }
            }
        }
        x => panic!("{:?}", x),
    }
}