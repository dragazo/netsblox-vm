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
    let fields = SymbolTable::from_fields(&ast.roles[0].entities[0], ref_pool);

    (proc, globals, fields, main.1)
}

fn run_till_term(proc: &mut Process, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<Option<Value>, ExecError> {
    assert!(proc.is_running());
    let ret = loop {
        match proc.step(ref_pool, globals, fields)? {
            StepType::Idle => panic!(),
            StepType::Normal | StepType::Yield => (),
            StepType::Terminate(e) => break e,
        }
    };
    assert!(!proc.is_running());
    Ok(ret)
}

fn assert_values_eq(got: &Value, expected: &Value, epsilon: f64, path: &str) {
    if got.get_type() != expected.get_type() {
        panic!("{} - type error - got {:?} expected {:?} - {:?}", path, got.get_type(), expected.get_type(), got);
    }
    match (got, expected) {
        (Value::Bool(got), Value::Bool(expected)) => {
            if got != expected { panic!("{} - bool error - got {} expected {}", path, got, expected) }
        }
        (Value::Number(got), Value::Number(expected)) => {
            let good = if got.is_finite() && expected.is_finite() { (got - expected).abs() <= epsilon } else { got == expected };
            if !good { panic!("{} - number error - got {} expected {}", path, got, expected) }
        }
        (Value::String(got), Value::String(expected)) => {
            if got != expected { panic!("{} - string error - got {} expected {}", path, got, expected) }
        }
        (Value::List(got), Value::List(expected)) => {
            let got = got.upgrade().unwrap();
            let got = got.borrow();

            let expected = expected.upgrade().unwrap();
            let expected = expected.borrow();

            if got.len() != expected.len() { panic!("{} - list len error - got {} expected {}\ngot:      {:?}\nexpected: {:?}", path, got.len(), expected.len(), got, expected) }

            for (i, (got, expected)) in iter::zip(got.iter(), expected.iter()).enumerate() {
                assert_values_eq(got, expected, epsilon, &format!("{}[{}]", path, i));
            }
        }
        (x, y) => unimplemented!("types: {:?} {:?}", x.get_type(), y.get_type()),
    }
}

//<variable name="field"><l>0</l></variable>

#[test]
fn test_proc_ret() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_ret.xml"),
        methods = "",
    ), SymbolTable::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
        Value::String(x) => assert_eq!(&*x, ""),
        x => panic!("{:?}", x),
    }
}

#[test]
fn test_proc_sum_123n() {
    let mut ref_pool = RefPool::default();
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
            Value::Number(ret) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let mut ref_pool = RefPool::default();
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
            Value::Number(ret) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}

#[test]
fn test_proc_loops_lists_basic() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_loops_lists_basic.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let got = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap();
    let expected = Value::from_vec(vec![
        Value::from_vec([1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([1.0,2.0,3.0,4.0,5.0,6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([2.0,3.0,4.0,5.0,6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([3.0,4.0,5.0,6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([4.0,5.0,6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([5.0,6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.0,7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([7.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([8.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([9.0,8.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([10.0,9.0,8.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,7.5,8.5,9.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,7.5,8.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,7.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,5.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,5.5,4.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,5.5,4.5,3.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,5.5,4.5,3.5,2.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([6.5,5.5,4.5,3.5,2.5,1.5].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
        Value::from_vec([56.0,44.0,176.0].into_iter().map(|v| v.into()).collect(), &mut ref_pool),
    ], &mut ref_pool);
    assert_values_eq(&got, &expected, 1e-10, "");
}

#[test]
fn test_proc_recursively_self_containing_lists() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_recursively_self_containing_lists.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
        Value::List(res) => {
            let res = res.upgrade().unwrap();
            let res = res.borrow();
            assert_eq!(res.len(), 4);

            fn check(name: &str, got: &Value, expected_basic: &Value, ref_pool: &mut RefPool) {
                let orig_got = got;
                match got {
                    Value::List(got) => {
                        let top_weak = got;
                        let got = got.upgrade().unwrap();
                        let got = got.borrow();
                        if got.len() != 11 { panic!("{} - len error - got {} expected 11", name, got.len()) }
                        let basic = Value::from_vec(got[..10].iter().cloned().collect(), ref_pool);
                        assert_values_eq(&basic, expected_basic, 1e-10, name);
                        match &got[10] {
                            Value::List(nested) => if !top_weak.ptr_eq(nested) {
                                panic!("{} - self-containment not ref-eq - got {:?}", name, nested.upgrade().unwrap().borrow());
                            }
                            x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                        }
                        assert_eq!(orig_got.alloc_ptr(), got[10].alloc_ptr());
                    }
                    x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                }
            }

            check("left mode", &res[0], &Value::from_vec([1.0,4.0,9.0,16.0,25.0,36.0,49.0,64.0,81.0,100.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool), &mut ref_pool);
            check("right mode", &res[1], &Value::from_vec([2.0,4.0,8.0,16.0,32.0,64.0,128.0,256.0,512.0,1024.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool), &mut ref_pool);
            check("both mode", &res[2], &Value::from_vec([1.0,4.0,27.0,256.0,3125.0,46656.0,823543.0,16777216.0,387420489.0,10000000000.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool), &mut ref_pool);
            check("unary mode", &res[3], &Value::from_vec([-1.0,-2.0,-3.0,-4.0,-5.0,-6.0,-7.0,-8.0,-9.0,-10.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool), &mut ref_pool);
        }
        x => panic!("{:?}", x),
    }
}

#[test]
fn test_proc_sieve_of_eratosthenes() {
    let mut ref_pool = RefPool::default();
    let mut locals = SymbolTable::default();
    locals.set_or_define("n", 100.0.into());
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_sieve_of_eratosthenes.xml"),
        methods = "",
    ), locals, &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap();
    let expect = Value::from_vec([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97].into_iter().map(|x| (x as f64).into()).collect(), &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-100, "primes");
}

#[test]
fn test_proc_early_return() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_early_return.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap();
    let expect = Value::from_vec([1,3].into_iter().map(|x| (x as f64).into()).collect(), &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-100, "res");
}

#[test]
fn test_proc_short_circuit() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_short_circuit.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap();
    let expect = Value::from_vec(vec![
        Value::from_vec(vec![Value::Bool(true), Value::String(Rc::new("xed".into()))], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(false), Value::String(Rc::new("sergb".into()))], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(true), Value::Bool(true)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(true), Value::Bool(false)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(false)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(false)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(true)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(true)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(false), Value::Bool(true)], &mut ref_pool),
        Value::from_vec(vec![Value::Bool(false), Value::Bool(false)], &mut ref_pool),
        Value::from_vec(vec![
            Value::String(Rc::new("xed".into())), Value::String(Rc::new("sergb".into())),
            Value::Bool(true), Value::Bool(false), Value::Bool(false), Value::Bool(false),
            Value::Bool(true), Value::Bool(true), Value::Bool(true), Value::Bool(false),
        ], &mut ref_pool),
    ], &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-100, "short circuit test");
}