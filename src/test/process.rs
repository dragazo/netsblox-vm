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

fn run_till_term(proc: &mut Process, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<(Option<Value>, usize), ExecError> {
    assert!(proc.is_running());
    let mut yields = 0;
    let ret = loop {
        match proc.step(ref_pool, globals, fields)? {
            StepType::Idle => panic!(),
            StepType::Normal => (),
            StepType::Yield => yields += 1,
            StepType::Terminate(e) => break e,
        }
    };
    assert!(!proc.is_running());
    Ok((ret, yields))
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

#[test]
fn test_proc_ret() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_ret.xml"),
        methods = "",
    ), SymbolTable::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap() {
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
        locals.redefine_or_define("n", Shared::Unique(n.into()));
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap() {
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
        locals.redefine_or_define("n", Shared::Unique(n.into()));
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap() {
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

    let got = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
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

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap() {
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
    locals.redefine_or_define("n", Shared::Unique(100.0.into()));
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_sieve_of_eratosthenes.xml"),
        methods = "",
    ), locals, &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
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

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
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

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
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

#[test]
fn test_proc_all_arithmetic() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_all_arithmetic.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
    let inf = std::f64::INFINITY;
    let expect = Value::from_vec(vec![
        Value::from_vec([8.5, 2.9, -2.9, -8.5].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([2.9, 8.5, -8.5, -2.9].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([15.96, -15.96, -15.96, 15.96].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([2.035714285714286, -2.035714285714286, -2.035714285714286, 2.035714285714286].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([inf, -inf, -inf, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([130.75237792066878, 0.007648044463151016].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.1, -2.7, 2.7, -0.1, 5.8, -1.3, 1.3, -5.8].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([7.0, 8.0, -7.0, -8.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([56.8, 6.3, inf, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([-56.8, 6.3, -inf, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([8.0, 8.0, -7.0, -7.0, inf, -inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([7.0, 7.0, -8.0, -8.0, inf, -inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([2.701851217221259, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.12706460860135046, 0.7071067811865475].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.9918944425900297, 0.7071067811865476].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.12810295445305653, 1.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.0, 30.0, -30.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([90.0, 60.0, 120.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.0, 26.56505117707799, -26.56505117707799, 88.72696997994328, -89.91635658567779].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([-0.6931471805599453, 0.0, 2.186051276738094, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([-0.3010299956639812, 0.0, 0.9493900066449128, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([-1.0, 0.0, 3.1538053360790355, inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([1.0, 3.3201169227365472, 0.0001363889264820114, inf, 0.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([1.0, 15.848931924611133, 1.2589254117941663e-9, inf, 0.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([1.0, 2.2973967099940698, 0.002093307544016197, inf, 0.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
        Value::from_vec([0.0, 1.2, -8.9, inf, -inf].into_iter().map(|x| x.into()).collect(), &mut ref_pool),
    ], &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-7, "short circuit test");
}

#[test]
fn test_proc_lambda_local_shadow_capture() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_lambda_local_shadow_capture.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
    let expect = Value::from_vec([1.0, 0.0, 1.0].into_iter().map(|x| x.into()).collect(), &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-20, "local shadow capture");
}

#[test]
fn test_proc_generators_nested() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_generators_nested.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
    let expect = Value::from_vec([1, 25, 169, 625, 1681, 3721, 7225, 12769, 21025, 32761].into_iter().map(|x| (x as f64).into()).collect(), &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-20, "nested generators");
}

#[test]
fn test_proc_call_in_closure() {
    let mut ref_pool = RefPool::default();
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/proc_call_in_closure.xml"),
        methods = "",
    ), Default::default(), &mut ref_pool);

    let res = run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().0.unwrap();
    let expect = Value::from_vec(vec![
        Value::from_vec([2, 4, 6, 8, 10].into_iter().map(|x| (x as f64).into()).collect(), &mut ref_pool),
        Value::from_vec([1, 3, 5, 7, 9].into_iter().map(|x| (x as f64).into()).collect(), &mut ref_pool),
    ], &mut ref_pool);
    assert_values_eq(&res, &expect, 1e-20, "call in closure");
}
