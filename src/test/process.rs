use alloc::rc::Rc;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::boxed::Box;

use core::cell::RefCell;
use core::fmt::Write;

use crate::*;
use crate::gc::*;
use crate::json::*;
use crate::real_time::*;
use crate::bytecode::*;
use crate::runtime::*;
use crate::std_system::*;
use crate::compact_str::{CompactString, format_compact, ToCompactString};

use super::*;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proc: Gc<'gc, RefLock<Process<'gc, C, StdSystem<C>>>>,
    glob: Gc<'gc, RefLock<GlobalContext<'gc, C, StdSystem<C>>>>,
}
type EnvArena = Arena<Rootable![Env<'_>]>;

fn get_running_proc<'a, F>(parser: ast::Parser, xml: &'a str, settings: Settings, system: Rc<StdSystem<C>>, locals: F) -> (EnvArena, Locations) where F: for<'gc> FnOnce(&Mutation<'gc>) -> SymbolTable<'gc, C, StdSystem<C>>{
    let ast = parser.parse(xml).unwrap();
    assert_eq!(ast.roles.len(), 1);

    let (code, init_info, ins_locs, locs) = ByteCode::compile(&ast.roles[0]).unwrap();
    let main = locs.funcs.iter().chain(locs.entities[0].1.funcs.iter()).find(|x| x.0.trans_name.trim() == "main").expect("no main function/method");

    (EnvArena::new(|mc| {
        let glob = GlobalContext::from_init(mc, &init_info, Rc::new(code), settings, system);
        let entity = *glob.entities.iter().next().unwrap().1;
        let glob = Gc::new(mc, RefLock::new(glob));
        let state = ProcessState::from(ProcessKind { entity, dispatcher: None });

        let proc = Process::new(ProcContext { global_context: glob, state, entity, start_pos: main.1, locals: locals(mc), barrier: None, reply_key: None, local_message: None });
        assert!(proc.is_running());

        Env { glob, proc: Gc::new(mc, RefLock::new(proc)) }
    }), ins_locs)
}

fn run_till_term<F>(env: &mut EnvArena, and_then: F) where F: for<'gc> FnOnce(&Mutation<'gc>, &Env, Result<(Value<'gc, C, StdSystem<C>>, usize), ExecError<C, StdSystem<C>>>) {
    env.mutate(|mc, env| {
        let mut proc = env.proc.borrow_mut(mc);
        assert!(proc.is_running());

        fn assert_done<'gc>(mc: &Mutation<'gc>, proc: &mut Process<'gc, C, StdSystem<C>>) {
            assert!(!proc.is_running());
            assert_ne!(proc.get_call_stack().len(), 0);
            for _ in 0..16 {
                match proc.step(mc) {
                    Ok(ProcessStep::Idle) => (),
                    x => panic!("{x:?}"),
                }
                assert!(!proc.is_running());
                assert_ne!(proc.get_call_stack().len(), 0);
            }
        }

        let mut yields = 0;
        let ret = loop {
            match proc.step(mc) {
                Ok(ProcessStep::Idle) => panic!(),
                Ok(ProcessStep::Normal) => (),
                Ok(ProcessStep::Yield) => yields += 1,
                Ok(ProcessStep::Terminate { result }) => break result,
                Ok(ProcessStep::CreatedClone { .. }) => panic!("proc tests should not clone"),
                Ok(ProcessStep::DeletedClone { .. }) => panic!("proc tests should not clone"),
                Ok(ProcessStep::Broadcast { .. }) => panic!("proc tests should not broadcast"),
                Ok(ProcessStep::Watcher { .. }) => panic!("proc tests should not use watchers"),
                Ok(ProcessStep::Abort { .. }) => panic!("proc tests should not abort"),
                Ok(ProcessStep::Fork { .. }) => panic!("proc tests should not fork"),
                Ok(ProcessStep::Pause) => panic!("proc tests should not pause"),
                Err(e) => {
                    assert_done(mc, &mut *proc);
                    drop(proc); // so handler can borrow the proc if needed
                    return and_then(mc, env, Err(e));
                }
            }
        };

        assert_done(mc, &mut *proc);
        drop(proc); // so handler can borrow the proc if needed
        and_then(mc, env, Ok((ret, yields)));
    });
}

#[test]
fn test_proc_ret() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/ret.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| match res.unwrap().0 {
        Value::Text(x) => assert_eq!(x, ""),
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sum_123n() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));

    for (n, expect) in [(0, json!("0")), (1, json!(1)), (2, json!(3)), (3, json!(6)), (4, json!(10)), (5, json!(15)), (6, json!(21))] {
        let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
            globals = "",
            fields = "",
            funcs = include_str!("blocks/sum-123n.xml"),
            methods = "",
        ), Settings::default(), system.clone(), |_| {
            let mut locals = SymbolTable::default();
            locals.define_or_redefine("n", Shared::Unique(Number::new(n as f64).unwrap().into()));
            locals
        });
        run_till_term(&mut env, |mc, _, res| {
            let expect = Value::from_simple(mc, SimpleValue::from_json(expect).unwrap());
            assert_values_eq(&res.unwrap().0, &expect, 1e-20, "sum 123n");
        });
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));

    for (n, expect) in [(0, json!("1")), (1, json!("1")), (2, json!(2)), (3, json!(6)), (4, json!(24)), (5, json!(120)), (6, json!(720)), (7, json!(5040))] {
        let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
            globals = "",
            fields = "",
            funcs = include_str!("blocks/recursive-factorial.xml"),
            methods = "",
        ), Settings::default(), system.clone(), |_| {
            let mut locals = SymbolTable::default();
            locals.define_or_redefine("n", Shared::Unique(Number::new(n as f64).unwrap().into()));
            locals
        });
        run_till_term(&mut env, |mc, _, res| {
            let expect = Value::from_simple(mc, SimpleValue::from_json(expect).unwrap());
            assert_values_eq(&res.unwrap().0, &expect, 1e-20, "recursive factorial");
        });
    }
}

#[test]
fn test_proc_loops_lists_basic() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/loops-lists-basic.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5,6,7,8,9,10],
            [1,2,3,4,5,6,7,8,9,10],
            [1,2,3,4,5,6,7],
            [2,3,4,5,6,7],
            [3,4,5,6,7],
            [4,5,6,7],
            [5,6,7],
            [6,7],
            [7],
            [8],
            [9,8],
            [10,9,8],
            [6.5,7.5,8.5,9.5],
            [6.5,7.5,8.5],
            [6.5,7.5],
            [6.5],
            [6.5],
            [6.5,5.5],
            [6.5,5.5,4.5],
            [6.5,5.5,4.5,3.5],
            [6.5,5.5,4.5,3.5,2.5],
            [6.5,5.5,4.5,3.5,2.5,1.5],
            ["56","44","176"],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expected, 1e-10, "loops lists");
    });
}

#[test]
fn test_proc_recursively_self_containing_lists() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/recursively-self-containing-lists.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| match res.unwrap().0 {
        Value::List(res) => {
            let res = res.borrow();
            assert_eq!(res.len(), 4);

            fn check<'gc>(name: &str, mc: &Mutation<'gc>, got: &Value<'gc, C, StdSystem<C>>, expected_basic: &Value<'gc, C, StdSystem<C>>) {
                let orig_got = got;
                match got {
                    Value::List(got) => {
                        let top_weak = got;
                        let got = got.borrow();
                        if got.len() != 11 { panic!("{} - len error - got {} expected 11", name, got.len()) }
                        let basic = Value::List(Gc::new(mc, RefLock::new(got.iter().take(10).cloned().collect())));
                        assert_values_eq(&basic, expected_basic, 1e-10, name);
                        match &got[10] {
                            Value::List(nested) => if top_weak.as_ptr() != nested.as_ptr() {
                                panic!("{} - self-containment not ref-eq - got {:?}", name, nested.borrow());
                            }
                            x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                        }
                        assert_eq!(orig_got.identity(), got[10].identity());
                    }
                    x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                }
            }

            check("left mode", mc, &res[0], &Value::from_simple(mc, SimpleValue::from_json(json!([1,4,9,16,25,36,49,64,81,100])).unwrap()));
            check("right mode", mc, &res[1], &Value::from_simple(mc, SimpleValue::from_json(json!([2,4,8,16,32,64,128,256,512,1024])).unwrap()));
            check("both mode", mc, &res[2], &Value::from_simple(mc, SimpleValue::from_json(json!([1,4,27,256,3125,46656,823543,16777216,387420489,10000000000.0])).unwrap()));
            check("unary mode", mc, &res[3], &Value::from_simple(mc, SimpleValue::from_json(json!([-1,-2,-3,-4,-5,-6,-7,-8,-9,-10])).unwrap()));
        }
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sieve_of_eratosthenes() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));

    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/sieve-of-eratosthenes.xml"),
        methods = "",
    ), Settings::default(), system, |_| {
        let mut locals = SymbolTable::default();
        locals.define_or_redefine("n", Shared::Unique(Number::new(100.0).unwrap().into()));
        locals
    });

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-100, "primes");
    });
}

#[test]
fn test_proc_early_return() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/early-return.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([1,3])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-100, "res");
    });
}

#[test]
fn test_proc_short_circuit() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/short-circuit.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [true, "xed"],
            [false, "sergb"],
            [true, true],
            [true, false],
            [false],
            [false],
            [true],
            [true],
            [false, true],
            [false, false],
            ["xed", "sergb", true, false, false, false, true, true, true, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-100, "short circuit test");
    });
}

#[test]
fn test_proc_all_arithmetic() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/all-arithmetic.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [8.5, 2.9, -2.9, -8.5],
            [2.9, 8.5, -8.5, -2.9],
            [15.96, -15.96, -15.96, 15.96],
            [2.035714285714286, -2.035714285714286, -2.035714285714286, 2.035714285714286],
            [130.75237792066878, 0.007648044463151016],
            [0.1, -2.7, 2.7, -0.1, 5.8, -1.3, 1.3, -5.8],
            [7.0, 8.0, -7.0, -8.0],
            [56.8, 6.3],
            [-56.8, 6.3],
            [8.0, 8.0, -7.0, -7.0],
            [7.0, 7.0, -8.0, -8.0],
            [2.701851217221259],
            [0.12706460860135046, 0.7071067811865475],
            [0.9918944425900297, 0.7071067811865476],
            [0.12810295445305653, 1.0],
            [0.0, 30.0, -30.0],
            [90.0, 60.0, 120.0],
            [0.0, 26.56505117707799, -26.56505117707799, 88.72696997994328, -89.91635658567779],
            [-0.6931471805599453, 0.0, 2.186051276738094],
            [-0.3010299956639812, 0.0, 0.9493900066449128],
            [-1.0, 0.0, 3.1538053360790355],
            [1.0, 3.3201169227365472, 0.0001363889264820114],
            [1.0, 15.848931924611133, 1.2589254117941663e-9],
            [1.0, 2.2973967099940698, 0.002093307544016197],
            ["0", "1.2", "-8.9"],
            "NumberError { error: Nan }",
            "NumberError { error: Infinity }",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-7, "arith tests");
    });
}

#[test]
fn test_proc_lambda_local_shadow_capture() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/lambda-local-shadow-capture.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!(["1", 0, "1"])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "local shadow capture");
    });
}

#[test]
fn test_proc_custom_script_vars() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/custom-script-vars.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0, 0, 0],
            [0, 0],
            ["56", 0],
            ["56", "-12"],
            [0, "-12"],
            [0, 0],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "custom script vars");
    });
}

#[test]
fn test_proc_upvars() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/upvars.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0.6427876096865393,0],
            [0.984807753012208,0],
            [0.8660254037844387,0],
            [0.3420201433256689,0],
            [-0.34202014332566866,0],
            [-0.8660254037844384,0],
            [-0.9848077530122081,0],
            [-0.6427876096865396,0],
            "---",
            [-0.6427876096865396,0],
            "---",
            [0.6427876096865393,0.766044443118978],
            [0.984807753012208,0.17364817766693041],
            [0.8660254037844387,-0.4999999999999998],
            [0.3420201433256689,-0.9396926207859083],
            [-0.34202014332566866,-0.9396926207859084],
            [-0.8660254037844384,-0.5000000000000004],
            [-0.9848077530122081,0.17364817766692997],
            [-0.6427876096865396,0.7660444431189778],
            "---",
            [-0.6427876096865396,0.7660444431189778],
            "---",
            [0.6427876096865393,0],
            [0.984807753012208,0],
            [0.8660254037844387,0],
            [0.3420201433256689,0],
            [-0.34202014332566866,0],
            [-0.8660254037844384,0],
            [-0.9848077530122081,0],
            [-0.6427876096865396,0],
            "---",
            [-0.6427876096865396,0],
            "---",
            [0.6427876096865393,0.766044443118978],
            [0.984807753012208,0.17364817766693041],
            [0.8660254037844387,-0.4999999999999998],
            [0.3420201433256689,-0.9396926207859083],
            [-0.34202014332566866,-0.9396926207859084],
            [-0.8660254037844384,-0.5000000000000004],
            [-0.9848077530122081,0.17364817766692997],
            [-0.6427876096865396,0.7660444431189778],
            "---",
            [-0.6427876096865396,0.7660444431189778],
            "---",
            "---",
            [0,0],
            "---",
            [0.3420201433256687,0],
            [0.6427876096865393,0],
            [0.8660254037844386,0],
            [0.984807753012208,0],
            "---",
            [0.984807753012208,0],
            "---",
            [0.3420201433256687,0.9396926207859084],
            [0.6427876096865393,0.766044443118978],
            [0.8660254037844386,0.5000000000000001],
            [0.984807753012208,0.17364817766693041],
            "---",
            [0.984807753012208,0.17364817766693041],
            "---",
            [0.3420201433256687,0],
            [0.6427876096865393,0],
            [0.8660254037844386,0],
            [0.984807753012208,0],
            "---",
            [0.984807753012208,0],
            "---",
            [0.3420201433256687,0.9396926207859084],
            [0.6427876096865393,0.766044443118978],
            [0.8660254037844386,0.5000000000000001],
            [0.984807753012208,0.17364817766693041],
            "---",
            [0.984807753012208,0.17364817766693041],
            "---",
            "---",
            [0,0],
            "---",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-10, "upvars");
    });
}

#[test]
fn test_proc_generators_nested() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/generators-nested.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([1, 25, 169, 625, 1681, 3721, 7225, 12769, 21025, 32761])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "nested generators");
    });
}

#[test]
fn test_proc_call_in_closure() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/call-in-closure.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [2, 4, 6, 8, 10],
            [1, 3, 5, 7, 9],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "call in closure");
    });
}

#[test]
fn test_proc_warp_yields() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));

    for (mode, (expected_counter, expected_yields)) in [(12, 12), (13, 13), (17, 0), (18, 0), (16, 0), (17, 2), (14, 0), (27, 3), (30, 7), (131, 109), (68, 23), (51, 0), (63, 14)].into_iter().enumerate() {
        let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
            globals = r#"<variable name="counter"><l>0</l></variable>"#,
            fields = "",
            funcs = include_str!("blocks/warp-yields.xml"),
            methods = "",
        ), Settings::default(), system.clone(), |_| {
            let mut locals = SymbolTable::default();
            locals.define_or_redefine("mode", Shared::Unique(Number::new(mode as f64).unwrap().into()));
            locals
        });

        run_till_term(&mut env, |mc, env, res| {
            let (res, yields) = res.unwrap();
            assert_values_eq(&res, &Value::from_simple(mc, SimpleValue::from_json(json!("x")).unwrap()), 1e-20, &format!("yield test (mode {mode}) res"));
            let counter = env.glob.borrow().globals.lookup("counter").unwrap().get().clone();
            assert_values_eq(&counter, &Number::new(expected_counter as f64).unwrap().into(), 1e-20, &format!("yield test (mode {mode}) value"));
            if yields != expected_yields { panic!("yield test (mode {}) yields - got {} expected {}", mode, yields, expected_yields) }
        });
    }
}

#[test]
fn test_proc_string_ops() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/string-ops.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "hello 5 world",
            [ "these", "are", "some", "words" ],
            [
                [ "hello", "world" ],
                [ "he", "", "o wor", "d" ]
            ],
            [ "", "", "these", "", "", "", "are", "some", "words", "", "" ],
            [ " ", " ", "t", "h", "e", "s", "e", " ", " ", " ", " ", "a", "r", "e", " ", "s", "o", "m", "e", " ", "w", "o", "r", "d", "s", " ", " " ],
            [ "these", "are", "some", "words" ],
            [ "hello", "world", "", "lines" ],
            [ "hello", "", "world", "test" ],
            [ "hello", "world", "", "cr land" ],
            [
                [ "test", "", "23", "21", "a", "b", "", "" ]
            ],
            [
                [ "test", "", "23", "21", "a", "b", "", "" ],
                [ "perp", "", "3", "", "44", "3", "2" ],
            ],
            { "a": [ 1, "a", [ 7, [] ], { "g": "4", "h": [] }], "b": 3, "c": "hello world" },
            [
                [ "a", "b" ],
                [ "c", "d" ],
                [ "g" ],
            ],
            [
                "L",
                [ "M", "A", "f" ],
                "f",
            ],
            [
                97,
                [97, 98, 99],
                [
                    [104, 101, 108, 108, 111],
                    [104, 105],
                    106,
                ],
            ],
            6,
            5,
            [5, 2, 1],
            [ "hello", "world" ],
            { "a": 1, "b": 2, "c": 3, "d": 4, "e": 5, "f": 6, "g": 7, "h": 8, "i": 9, "j": 10 },
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "string ops");
    });
}

#[test]
fn test_proc_str_cmp_case_insensitive() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/str-cmp-case-insensitive.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            false, true, true, true, true,
            [
                false, true,
                [false, true, true, false],
            ],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "str cmp case insensitive");
    });
}

#[test]
fn test_proc_rpc_call_basic() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));

    for (lat, long, city) in [(36.1627, -86.7816, "Nashville"), (40.8136, -96.7026, "Lincoln"), (40.7608, -111.8910, "Salt Lake City")] {
        let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
            globals = "",
            fields = "",
            funcs = include_str!("blocks/rpc-call-basic.xml"),
            methods = "",
        ), Settings::default(), system.clone(), |_| {
            let mut locals = SymbolTable::default();
            locals.define_or_redefine("lat", Shared::Unique(Number::new(lat).unwrap().into()));
            locals.define_or_redefine("long", Shared::Unique(Number::new(long).unwrap().into()));
            locals
        });
        run_till_term(&mut env, |_, _, res| match res.unwrap().0 {
            Value::Text(ret) => assert_eq!(ret, city),
            x => panic!("{:?}", x),
        });
    }
}

#[test]
fn test_proc_list_index_blocks() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-index-blocks.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
            [2, 3, 4, 5, 6, 7, 8, 9, 10],
            [2, 3, 4, 5, 6, 7, 8, 9],
            [2, 3, 4, 5, 7, 8, 9],
            ["17", 2, 3, 4, 5, 7, 8, 9],
            ["17", 2, 3, 4, 5, 7, 8, 9, "18"],
            ["17", 2, "19", 3, 4, 5, 7, 8, 9, "18"],
            ["17", 2, "19", 3, 4, 5, 7, 8, 9, "18", "20"],
            ["30", 2, "19", 3, 4, 5, 7, 8, 9, "18", "20"],
            ["30", 2, "19", 3, 4, 5, 7, 8, 9, "18", "32"],
            ["30", 2, "19", 3, 4, 5, "33", 8, 9, "18", "32"],
            ["30", "32", 4],
            [],
            ["50"],
            [],
            ["51"],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "index ops");
    });
}

#[test]
fn test_proc_literal_types() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/literal-types.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ "50e4", "50e4s" ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-20, "literal types check");
    });
}

#[test]
fn test_proc_say() {
    let output = Rc::new(RefCell::new(CompactString::default()));
    let output_cpy = output.clone();
    let config = Config::<C, StdSystem<C>> {
        request: None,
        command: Some(Rc::new(move |_, key, command, _| match command {
            Command::Print { style: _, value } => {
                if let Some(value) = value { writeln!(*output_cpy.borrow_mut(), "{value:?}").unwrap() }
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            _ => CommandStatus::UseDefault { key, command },
        })),
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/say.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, _| ());
    assert_eq!(output.borrow().as_str(), "\"Greetings, human.\"\n\"I will destroy him.\"\n");
}

#[test]
fn test_proc_syscall() {
    let buffer = Rc::new(RefCell::new(CompactString::default()));
    let buffer_cpy = buffer.clone();
    let config = Config::<C, StdSystem<C>> {
        request: Some(Rc::new(move |_, key, request, _| match &request {
            Request::Syscall { name, args } => match name.as_str() {
                "bar" => match args.is_empty() {
                    false => {
                        let mut buffer = buffer_cpy.borrow_mut();
                        for value in args {
                            buffer.push_str(value.as_text().unwrap().as_ref());
                        }
                        key.complete(Ok(SimpleValue::Number(Number::new(buffer.len() as f64).unwrap()).into()));
                        RequestStatus::Handled
                    }
                    true => {
                        key.complete(Err(CompactString::new("beep beep - called with empty args")));
                        RequestStatus::Handled
                    }
                }
                "foo" => {
                    let content = buffer_cpy.borrow().clone();
                    key.complete(Ok(SimpleValue::Text(content).into()));
                    RequestStatus::Handled
                }
                _ => RequestStatus::UseDefault { key, request },
            }
            _ => RequestStatus::UseDefault { key, request },
        })),
        ..Default::default()
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/syscall.xml"),
        methods = "",
    ), Settings { syscall_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["", ""],
            "",
            ["5test9", ""],
            "beep beep - called with empty args",
            ["5test9", ""],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "syscall checks");
    });
}

#[test]
fn test_proc_timer_wait() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/timer-wait.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    let start = std::time::Instant::now();
    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([0.0, 0.05, 0.15, 0.3, 0.5, 0.75, 1.05, 1.4, 1.8, 2.25, 2.75])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 0.01, "timer checks");
    });
    let duration = start.elapsed().as_millis();
    assert!(duration >= 2750);
}

#[test]
fn test_proc_cons_cdr() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/cons-cdr.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1],
            [2,1],
            [3,2,1],
            [4,3,2,1],
            [5,4,3,2,1],
            [4,3,2,1],
            [3,2,1],
            [2,1],
            [1],
            []
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "cons cdr checks");
    });
}

#[test]
fn test_proc_list_find_contains() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-find-contains.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 0, false],
            ["2", 2, true],
            ["3", 0, false],
            ["5", 1, true],
            ["world", 0, false],
            ["hello", 3, true],
            ["2", 2, true],
            [["1","2","3"], 4, true],
            [["1","2","3","4"], 0, false],
            [["1","2"], 0, false],
            [[], 5, true],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "cons cdr checks");
    });
}

#[test]
fn test_proc_append() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/append.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,"test"],
            [],
            [1,2,3,4],
            [1,2,3,4,1,2,3,4],
            [1,2,3,4,2,3,"4"],
            [1,2,3,4,2,3,"4"],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "append result");
    });
}

#[test]
fn test_proc_foreach_mutate() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/foreach-mutate.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11],
            [2,4,6,8,10,12,14,16,18,20],
            [2, 1.5, 1.3333333, 3, 2, 1.6666666, 4, 2.5, 2, 3, 2.5, 2.33333, 4, 3, 2.666666, 5, 3.5, 3, 4, 3.5, 3.333333, 5, 4, 3.666666, 6, 4.5, 4],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "map result");
    });
}

#[test]
fn test_proc_map() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/map.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5,6,7,8,9,10,2,4,6,8,10,12,14,16,18,20],
            [1,4,9,16,25,36,49,64,81,100],
            [1.0, 1.4142135623730951, 1.7320508075688772, 2.0, 2.23606797749979, 2.449489742783178, 2.6457513110645907, 2.8284271247461903, 3.0, 3.1622776601683795, 1.4142135623730951, 2.0, 2.449489742783178, 2.8284271247461903, 3.1622776601683795, 3.4641016151377544, 3.7416573867739413, 4.0, 4.242640687119285, 4.47213595499958],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "map result");
    });
}

#[test]
fn test_proc_keep_find() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/keep-find.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5,6,7,8,9,10,4,5,6,7,8,9,10,11,12,13],
            [3,6,9],
            [10,11,12,13,14,15,16,17,18,19,20,17,18,19,20,21],
            14,
            "",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "keep/find results");
    });
}

#[test]
fn test_proc_numeric_bases() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/numeric-bases.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["34", 34, 68, 1156],
            ["025", 25, 50, 625],
            ["0x43", 67, 134, 4489],
            ["0o34", 28, 56, 784],
            ["0b101101", 45, 90, 2025],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "numeric bases results");
    });
}

#[test]
fn test_proc_combine() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/combine.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5,6,7,8,9,10,[1,2],[2,3],[6,4],[24,5],[120,6],[720,7],[5040,8],[40320,9],[362880,10]],
            3628800,
            ["7"],
            "7",
            [],
            0,
            55,
            "1, 2, 3, 4, 5, 6, 7, 8, 9, 10",
            0,
            0,
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "keep/find results");
    });
}

#[test]
fn test_proc_autofill_closure_params() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/autofill-closure-params.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [3,6,9,12,15,18,21,24,27,30],
            [3,4,5,6,7,8,9,10,11,12],
            [1,3,5,7,9],
            55,
            3628800,
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "autofill closure params");
    });
}

#[test]
fn test_proc_pick_random() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/pick-random.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let results = {
            let mut out = vec![];
            for row in res.unwrap().0.as_list().unwrap().borrow().iter() {
                let mut vals = vec![];
                for val in row.as_list().unwrap().borrow().iter() {
                    vals.push(match val {
                        Value::Number(x) => *x,
                        _ => panic!("{val:?}"),
                    });
                }
                out.push(vals);
            }
            out
        };
        assert_eq!(results.len(), 4);
        for row in results.iter() {
            if row.len() != 1024 { panic!("len error {}\n{row:?}", row.len()); }
        }

        for val in results[0].iter().map(|x| x.get()) {
            if !(1.0..=10.0).contains(&val) || (val != val as i64 as f64) {
                panic!("res[0] error: {val}");
            }
        }
        for val in results[1].iter().map(|x| x.get()) {
            if !(-6.0..=5.0).contains(&val) || (val != val as i64 as f64) {
                panic!("res[1] error: {val}");
            }
        }

        let mut int_count = 0;
        for val in results[2].iter().map(|x| x.get()) {
            if !(-6.0..=5.1).contains(&val) {
                panic!("res[2] error: {val}");
            }
            if val == val as i64 as f64 { int_count += 1; }
        }
        assert!(int_count <= 5); // hard to test rng, but this is almost certainly true

        int_count = 0;
        for val in results[3].iter().map(|x| x.get()) {
            if !(0.0..=0.9999).contains(&val) {
                panic!("res[3] error: {val}");
            }
            if val == val as i64 as f64 { int_count += 1; }
        }
        assert!(int_count <= 5); // hard to test rng, but this is almost certainly true
    });
}

#[test]
fn test_proc_tensor_list_idx() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/tensor-list-idx.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let results = res.unwrap().0.as_list().unwrap();
        let results = &*results.borrow();

        assert_eq!(results.len(), 6);
        assert_values_eq(&results[0], &Value::from_simple(mc, SimpleValue::from_json(json!(["11", 2, "help", ["4", "3", "5"], "tr", "34", -7])).unwrap()), 1e-5, "tensor list idx 0");
        match &results[1] {
            Value::List(x) => {
                let x = &*x.borrow();
                assert_eq!(x.len(), 5);
                match &x[0] {
                    Value::Text(x) => assert_eq!(x.as_str(), "help"),
                    x => panic!("{x:?}"),
                }
                match &x[1] {
                    Value::Text(x) => assert_eq!(x.as_str(), "11"),
                    x => panic!("{x:?}"),
                }
                match &x[2] {
                    Value::List(x) => {
                        let x = &*x.borrow();
                        assert_eq!(x.len(), 3);
                        match &x[0] {
                            Value::Number(x) => assert!(x.get() == 2.0),
                            x => panic!("{x:?}"),
                        }
                        match &x[1] {
                            Value::Text(x) => assert_eq!(x.as_str(), "11"),
                            x => panic!("{x:?}"),
                        }
                        match &x[2] {
                            Value::Text(x) => assert_eq!(x.as_str(), "help"),
                            x => panic!("{x:?}"),
                        }
                    }
                    x => panic!("{x:?}"),
                }
                match &x[3] {
                    Value::Number(x) => assert!(x.get() == -7.0),
                    x => panic!("{x:?}"),
                }
                assert_eq!(results[1].identity(), x[4].identity());
            }
            x => panic!("{x:?}"),
        }
        assert_values_eq(&results[2], &Value::from_simple(mc, SimpleValue::from_json(json!(["11", 2, "help", ["4", "3", "5"], "tr", "34", -7])).unwrap()), 1e-5, "tensor list idx 2");
        assert_values_eq(&results[3], &Value::from_simple(mc, SimpleValue::from_json(json!([["1", "2"], ["1", "2"], ["1", "2"], ["4", "3", "5"], "tr", "34", ["1", "2"]])).unwrap()), 1e-5, "tensor list idx 3");
        assert_values_eq(&results[4], &Value::from_simple(mc, SimpleValue::from_json(json!([["7", "5"], ["1", "2"], ["7", "5"], ["1", "2"], ["7", "5"], ["1", "2"], ["4", "3", "5"], "tr", "34", ["7", "5"], ["1", "2"]])).unwrap()), 1e-5, "tensor list idx 4");
        assert_values_eq(&results[5], &Value::from_simple(mc, SimpleValue::from_json(json!([["1", "2"], ["7", "5"], ["1", "2"], "tr", "34", ["7", "5"], ["1", "2"]])).unwrap()), 1e-5, "tensor list idx 5");
    });
}

#[test]
fn test_proc_rand_list_ops() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rand-list-ops.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let (results, last) = {
            fn extract_value(val: &Value<'_, C, StdSystem<C>>) -> Text {
                match val {
                    Value::Number(x) => SimpleValue::stringify_number(*x),
                    Value::Text(x) if matches!(x.as_str(), "hello" | "goodbye") => x.clone(),
                    x => panic!("{x:?}"),
                }
            }

            let mut out = vec![];
            let res = res.unwrap().0.as_list().unwrap();
            let res = res.borrow();
            let mut res = res.iter();
            let last = loop {
                match res.next().unwrap() {
                    Value::List(row) => {
                        let mut vals = vec![];
                        for val in row.borrow().iter() {
                            vals.push(extract_value(val));
                        }
                        out.push(vals);
                    }
                    x => break extract_value(x),
                }
            };
            assert!(res.next().is_none());
            (out, last)
        };

        assert_eq!(results.len(), 3);
        assert_eq!(results[0].len(), 6);
        assert_eq!(results[1].len(), 7);
        assert_eq!(results[2].len(), 7);

        assert_eq!(results[0], &["5", "6", "7", "8", "9", "10"]);
        assert!(results[1].iter().any(|x| *x == "hello"));
        assert!(!results[1].iter().any(|x| *x == "goodbye"));
        assert!(results[2].iter().any(|x| *x == "goodbye"));

        assert!(results[2].contains(&last));
    });
}

#[test]
fn test_proc_variadic_sum_product() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-sum-product.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            15,
            21,
            [17, 16, 18],
            [20, 28, 13],
            0,
            120,
            840,
            [150, 180, 180],
            [240, 320, 20],
            1,
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "variadic sum product");
    });
}

#[test]
fn test_proc_preserve_tensor_topology() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/preserve-tensor-topology.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [[["5", "3", "4"], ["5", "3", "4"], ["5", "3", "4"]], true, false, false],
            [[[6, 4, 5], [6, 4, 5], [6, 4, 5]], true, false, false],
            [[[10, 6, 8], [10, 6, 8], [10, 6, 8]], true, false, false],
            [[[-5, -3, -4], [-5, -3, -4], [-5, -3, -4]], true, false, false],
            [[[32, 8, 16], [32, 8, 16], [32, 8, 16]], true, false, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "preserve tensor topology");
    });
}

#[test]
fn test_proc_variadic_min_max() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-min-max.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ "1", "2", "9", "17" ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "variadic min/max");
    });
}

#[test]
fn test_proc_atan2_new_cmp() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/atan2-new-cmp.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [18.43494882, 116.5650511, -32.0053832, -158.198590],
            [14.03624346, 53.13010235, -18.4349488],
            [false, true, true],
            [true, true, false],
            [true, false, true],
            true,
            false,
            [false, true],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "atan2 and new cmp");
    });
}

#[test]
fn test_proc_list_columns() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-columns.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [
                ["1", "4", "6"],
                ["2", "5", ""],
                ["3", "", ""],
            ],
            [[1,2,3,4,5,6,7,8,9,10]],
            [
                ["1", "2", "3", "6", "7"],
                ["1", "2", "4", "6", "7"],
                ["1", "2", "5", "6", "7"],
            ],
            [
                ["1", "2", "3", "6", "8", "9"],
                ["1", "2", "4", "7", "", "9"],
                ["1", "2", "5", "", "", "9"],
            ],
            [
                ["1", "2", "7", "9"],
                ["1", ["3", "4"], "8", "9"],
                ["1", "5", "", "9"],
                ["1", ["6"], "", "9"],
            ],
            [["6"]],
            [],
            [[[]]],
            [],
            false,
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "columns");
    });
}

#[test]
fn test_proc_transpose_consistency() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/transpose-consistency.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0],
            [1, 0],
            [2, 0],
            [],
            [],
            [],
            [0],
            [0],
            [0],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "transpose consistency");
    });
}

#[test]
fn test_proc_compare_str() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/compare-str.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [false, true, true, false, false, true],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, true, true, false, false, true],

            [false, true, true, false, false, true],
            [false, true, true, false, false, true],
            [false, true, true, false, false, true],
            [false, true, true, false, false, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, false, false, true, true, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, false, false, true, true, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, false, false, true, true, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, false, false, true, true, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, false, false, true, true, true],

            [false, true, true, false, false, true],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],
            [false, true, true, false, false, true],

            [false, true, true, false, false, true],
            [false, true, true, false, false, true],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],

            [false, true, true, false, false, true],
            [true, true, false, true, false, false],
            [false, false, false, true, true, true],

            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
            [true, true, false, true, false, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "compare str");
    });
}

#[test]
fn test_proc_new_min_max() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/new-min-max.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["12", "12", "23", "23"],
            ["12", "12", "023", "023"],
            ["12", "12", 23, 23],
            [12, 12, "23", "23"],
            [12, 12, "023", "023"],
            [12, 12, 23, 23],
            ["hello", "hello", "world", "world"],
            ["abc", "ABC", "abc", "ABC"],
            [[], [], ["4"], ["4"]],
            [["4"], ["4"], ["7"], ["7"]],
            [["4"], ["4"], ["4", "1", "2"], ["4", "1", "2"]],
            [["4", "1", "2"], ["4", "1", "2"], ["4", "2"], ["4", "2"]],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "new min max");
    });
}

#[test]
fn test_proc_flatten() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/flatten.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["3", "6", "7", "10", "12", "16", "20"],
            ["6", "1", "3", "6", "1", "3", "6", "1", "3"],
            ["hello world"],
            [""],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "flatten");
    });
}

#[test]
fn test_proc_list_len_rank_dims() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-len-rank-dims.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0, 1, [0]],
            [3, 1, [3]],
            [3, 2, [3, 0]],
            [3, 2, [3, 1]],
            [5, 3, [5, 3, 1]],
            [6, 5, [6, 3, 1, 3, 1]],
            [2, 2, [2, 10]],
            [2, 2, [2, 10]],
            [0, []],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list len, rank, dims");
    });
}

#[test]
fn test_proc_string_index() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/string-index.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["안", "요", "세"],
            ["h", "w", ["t", "i"], "d"],
            ["o", "d", ["s", "s"], "g"],
            ["셋", "하", ["섯", "둘"], "다"],
            ["요", "d", "수", "r", "일"],
            [3, 2],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "string index");
    });
}

#[test]
fn test_proc_type_query() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/type-query.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [false, true, false, false, false, false, false],
            [false, true, false, false, false, false, false],
            [false, true, false, false, false, false, false],
            [false, true, false, false, false, false, false],
            [true, false, false, false, false, false, false],
            [true, false, false, false, false, false, false],
            [false, true, false, false, false, false, false],
            [false, false, true, false, false, false, false],
            [false, false, false, true, false, false, false],
            [false, false, false, true, false, false, false],
            [false, false, false, true, false, false, false],
            [false, false, false, false, true, false, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "type query");
    });
}

#[test]
fn test_proc_variadic_strcat() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-strcat.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "hello world test13",
            "this is a test15",
            "",
            "",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "variadic strcat");
    });
}

#[test]
fn test_proc_list_lines() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-lines.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "",
            "hello",
            "hello\nworld",
            "hello\nworld\n69",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list lines");
    });
}

#[test]
fn test_proc_whitespace_in_numbers() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/whitespace-in-numbers.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [12, 32, 14],
            [18, 50, 20],
            [10, 26, 12],
            [9, 11, 27],
            [false, true, true, false, true, false, false],
            [true, true, false, true, false, false, false],
            [true, true, false, true, false, false, false],
            [true, true, false, true, false, false, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "ws in nums");
    });
}

#[test]
fn test_proc_binary_make_range() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/binary-make-range.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [1,2,3,4,5],
            [
                [1,2,3,4,5],
                [2,3,4,5],
                [8,7,6,5],
                [5],
            ],
            [
                [3,2,1],
                [3,2],
                [3,4,5,6,7,8],
                [3,4,5],
            ],
            [
                [4,3,2,1],
                [8,7,6,5,4,3,2],
                [5,6,7,8],
            ],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "binary make range");
    });
}

#[test]
fn test_proc_identical_to() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/identical-to.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [true, false, false, true],
            [true, true, true, true],
            [false, false, true, true, true],
            [false, false, false, true],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "identical to");
    });
}

#[test]
fn test_proc_variadic_list_ctors() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-list-ctors.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [],
            ["1","2","3"],
            ["1","5","3","8"],
            [],
            ["1","2","3","5","4","2","1","8"],
            ["2","1","9","5","4","6","5","1"],
            [false, false, false, false],
            [true, true, true, true],
            [true, false],
            [true, false],
            [true, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "variadic list ctors");
    });
}

#[test]
fn test_proc_list_rev() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-rev.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["2", "4", "1"],
            ["2", ["6", "4", "3"], "8", "1"],
            [["6", ["6", "4", "3"], "3"], ["6", "4", "3"], "8", "1"],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list rev");
    });
}

#[test]
fn test_proc_list_reshape() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-reshape.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["3", "1", "h", "e", "l", "l", "1", "h", "e", "l"],
            [["3", "1", "h", "e", "l"], ["l", "1", "h", "e", "l"]],
            [
                [["3", "1", "h"], ["e", "l", "l"], ["1", "h", "e"], ["l", "l", "gh"], ["3", "1", "h"]],
                [["e", "l", "l"], ["1", "h", "e"], ["l", "l", "gh"], ["3", "1", "h"], ["e", "l", "l"]],
            ],
            [
                [["3", "1", "h", "e", "l"]],
                [["l", "1", "h", "e", "l"]],
                [["l", "gh", "3", "1", "h"]],
                [["e", "l", "l", "1", "h"]],
                [["e", "l", "l", "gh", "3"]],
            ],
            [[], [], [], []],
            "3",
            "3",
            [[6, 6, 6], [6, 6, 6]],
            "EmptyList",
            "EmptyList",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list reshape");
    });
}

#[test]
fn test_proc_list_json() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-json.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            r#"[]"#,
            r#"["test"]"#,
            r#"["test",25.0,"12"]"#,
            r#"[["1",["2"],[],[["2"]]],"\"another\"",["1",["2"],[],[["2"]]],"[{}]"]"#,
            r#"14.0"#,
            r#""hello world \"again\"""#,
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list json");
    });
}

#[test]
fn test_proc_explicit_to_string_cvt() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/explicit-to-string-cvt.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "hello world 1",
            "hello 67 2",
            "hello 69 3",
            "hello true 4",
            "hello false 5",
            "hello [] 6",
            "hello [test] 7",
            "hello [test,more] 8",
            "hello [1,2,3,4] 9",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "explicit tostr");
    });
}

#[test]
fn test_proc_empty_variadic_no_auto_insert() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/empty-variadic-no-auto-insert.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [[], [], [], []],
            [[], [], [], []],
            [[], [], [], []],
            [[], [], [], []],
            [[], [], [], []],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "no auto insert");
    });
}

#[test]
fn test_proc_c_ring_no_auto_insert() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/c-ring-no-auto-insert.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [[""], ["", 1, ""], "", [], "", ["", "", 1, ""], "", 1],
            [[""], ["", 2, ""], "", [], "", ["", "", 2, ""], "", 2],
            [[""], ["", 3, ""], "", [], "", ["", "", 3, ""], "", 3],
            [[""], ["", 4, ""], "", [], "", ["", "", 4, ""], "", 4],
            [[""], ["", 5, ""], "", [], "", ["", "", 5, ""], "", 5],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "no auto insert");
    });
}

#[test]
fn test_proc_signed_zero() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/signed-zero.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0.0, 0.0, 0.0],
            ["0", "0", "0"],
            [false, true, true, false, true, false, true],
            [false, true, true, false, true, false, true],
            [false, true, true, false, true, false, true],
            [false, true, true, false, true, false, true],
            [false, true, true, false, true, false, true],
            [false, true, true, false, true, false, true],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 0.0, "signed zero");
    });
}

#[test]
fn test_proc_singleton_sum_product() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/singleton-sum-product.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            9, 9, [6, [4, 2], 1], [6, [4, 2], 1],
            9, 9, [6, [4, 2], 1], [6, [4, 2], 1],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "singleton sum product");
    });
}

#[test]
fn test_proc_list_combinations() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-combinations.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [],
            [[1], [2], [3], [4], [5], [6], [7], [8], [9], [10]],
            [
                [1, "red"], [1, "green"], [1, "blue"],
                [2, "red"], [2, "green"], [2, "blue"],
                [3, "red"], [3, "green"], [3, "blue"],
            ],
            [
                [1, "red", "yes"], [1, "red", "no"],
                [1, "green", "yes"], [1, "green", "no"],
                [1, "blue", "yes"], [1, "blue", "no"],

                [2, "red", "yes"], [2, "red", "no"],
                [2, "green", "yes"], [2, "green", "no"],
                [2, "blue", "yes"], [2, "blue", "no"],
            ],
            [
                ["hello", "darkness", "friend", "!"], ["hello", "darkness", "friend", "."],
                ["hello", "my", "friend", "!"], ["hello", "my", "friend", "."],
                ["hello", "old", "friend", "!"], ["hello", "old", "friend", "."],

                ["goodbye", "darkness", "friend", "!"], ["goodbye", "darkness", "friend", "."],
                ["goodbye", "my", "friend", "!"], ["goodbye", "my", "friend", "."],
                ["goodbye", "old", "friend", "!"], ["goodbye", "old", "friend", "."],
            ],
            [],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "list combinations");
    });
}


#[test]
fn test_proc_unevaluated_inputs() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/unevaluated-inputs.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "before", "waiting... 1", "waiting... 2", "waiting... 3", "waiting... 4", "waiting... 5", "waiting... 6", "after",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "unevaluated inputs");
    });
}

#[test]
fn test_proc_index_over_bounds() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, ins_locs) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/index-over-bounds.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let res = res.unwrap_err();
        match &res.cause {
            ErrorCause::IndexOutOfBounds { index, len } => {
                assert_eq!(*index, 11);
                assert_eq!(*len, 10);
            }
            x => panic!("{x:?}"),
        }
        assert_eq!(ins_locs.lookup(res.pos).as_deref().unwrap(), "item_18_4");
    });
}

#[test]
fn test_proc_neg_collab_ids() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, ins_locs) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/neg-collab-ids.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let res = res.unwrap_err();
        match &res.cause {
            ErrorCause::IndexOutOfBounds { index, len } => {
                assert_eq!(*index, 11);
                assert_eq!(*len, 10);
            }
            x => panic!("{x:?}"),
        }
        assert_eq!(ins_locs.lookup(res.pos).as_deref().unwrap(), "item_-18_4");
    });
}

#[test]
fn test_proc_basic_motion() {
    #[derive(PartialEq, Eq, Debug)]
    enum Action {
        Forward(i32),
        Turn(i32),
        Position,
        Heading,
    }
    fn to_i32(x: Number) -> i32 {
        let x = x.get();
        let y = x as i32;
        if x != y as f64 { panic!() }
        y
    }

    let sequence = Rc::new(RefCell::new(Vec::with_capacity(16)));
    let config = Config::<C, StdSystem<C>> {
        command: {
            let sequence = sequence.clone();
            Some(Rc::new(move |_, key, command, _| {
                match command {
                    Command::Forward { distance } => sequence.borrow_mut().push(Action::Forward(to_i32(distance))),
                    Command::ChangeProperty { prop: Property::Heading, delta } => sequence.borrow_mut().push(Action::Turn(to_i32(delta.as_number().unwrap()))),
                    _ => return CommandStatus::UseDefault { key, command },
                }
                key.complete(Ok(()));
                CommandStatus::Handled
            }))
        },
        request: {
            let sequence = sequence.clone();
            Some(Rc::new(move |_, key, request, _| {
                match request {
                    Request::Property { prop: Property::XPos } => {
                        sequence.borrow_mut().push(Action::Position);
                        key.complete(Ok(SimpleValue::Number(Number::new(13.0).unwrap()).into()));
                    }
                    Request::Property { prop: Property::YPos } => {
                        sequence.borrow_mut().push(Action::Position);
                        key.complete(Ok(SimpleValue::Number(Number::new(54.0).unwrap()).into()));
                    }
                    Request::Property { prop: Property::Heading } => {
                        sequence.borrow_mut().push(Action::Heading);
                        key.complete(Ok(SimpleValue::Number(Number::new(39.0).unwrap()).into()));
                    }
                    _ => return RequestStatus::UseDefault { key, request },
                }
                RequestStatus::Handled
            }))
        },
    };

    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/basic-motion.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([ 13, 54, 39 ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expected, 1e-4, "basic motion test")
    });

    let expected = [
        Action::Forward(44),
        Action::Forward(-42),
        Action::Turn(91),
        Action::Turn(-49),
        Action::Turn(-51),
        Action::Turn(57),
        Action::Position,
        Action::Position,
        Action::Heading,
    ];
    assert_eq!(*sequence.borrow(), expected);
}

#[test]
fn test_proc_string_cmp() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/string-cmp.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [true, false, false, true, false, false, false],
            [true, false, false, true, true, true, true],
            [false, true, true, false, false, false, false],
            [false, true, true, false, true, true, true],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "string cmp");
    });
}

#[test]
fn test_proc_stack_overflow() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, locs) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="g"><l>0</l></variable>"#,
        fields = r#"<variable name="f"><l>0</l></variable>"#,
        funcs = "",
        methods = include_str!("blocks/stack-overflow.xml"),
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, env, res| {
        let err = res.unwrap_err();
        let summary = ErrorSummary::extract(&err, &*env.proc.borrow(), &locs);
        fn check(s: &ErrorSummary) {
            assert!(s.cause.contains("CallDepthLimit"));
            assert!(format!("{s:?}").starts_with("ErrorSummary"));

            assert_eq!(s.globals.len(), 1);
            assert_eq!(s.globals[0].name, "g");
            assert_eq!(s.globals[0].value, "\"hello\"");

            assert_eq!(s.fields.len(), 1);
            assert_eq!(s.fields[0].name, "f");
            assert_eq!(s.fields[0].value, "\"world\"");

            assert!(s.trace.len() >= 64);
            assert_eq!(s.trace[0].locals.len(), 0);
            for (i, entry) in s.trace[1..].iter().enumerate() {
                assert_eq!(entry.locals.len(), 1);
                let v = &entry.locals[0];
                assert_eq!(v.name, "v");
                assert_eq!(v.value, format!("{}", i + 1));
            }
        }
        check(&summary);
        check(&summary.clone());
    });
}

#[test]
fn test_proc_variadic_params() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-params.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [],
            ["5"],
            ["5", "g"],
            ["5", "g", "q"],
            [1, 2, 3, 4, 5, 6, 7, 8],
            [[], []],
            [["6"], []],
            [[], ["9"]],
            [["34"], ["gf"]],
            [["34", "1h"], ["gf"]],
            [[], ["re", "ds", "w"]],
            [["3", "1"], ["re", "ds", "w"]],
            [["3", "1"], [1, 2, 3, 4]],
            [["gf", "fd", "", "d"], [1, 2, 3, 4]],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "variadic params");
    });
}

#[test]
fn test_proc_rand_str_char_cache() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rand-str-char-cache.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let res = res.unwrap().0.as_text().unwrap();
        assert_eq!(res.len(), 8192);
        let mut counts: BTreeMap<char, usize> = BTreeMap::new();
        for ch in res.chars() {
            assert!(('0'..='9').contains(&ch));
            *counts.entry(ch).or_default() += 1;
        }
        for ch in "0123456789".chars() {
            let count = *counts.entry(ch).or_default();
            if !(600..1000).contains(&count) {
                panic!("char count {ch:?} way out of expected range {count}");
            }
        }
    });
}

#[test]
fn test_proc_noop_upvars() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/noop-upvars.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ 0, 0, 1, 0 ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "noop upvars");
    });
}

#[test]
fn test_proc_try_catch_throw() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/try-catch-throw.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ "starting", "start code", "got error", "test error", "done" ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "try catch throw");
    });
}

#[test]
fn test_proc_exception_unregister() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/exception-unregister.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ "top start", "before test", "before inner", "inner error", "IndexOutOfBounds { index: 332534, len: 3 }", "after test", "top error", "IndexOutOfBounds { index: 332534, len: 6 }", "top done"])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "exception res");
    });
}

#[test]
fn test_proc_exception_rethrow() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/exception-rethrow.xml"),
        methods = "",
    ), Settings::default(), system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([ "IndexOutOfBounds { index: 543548, len: 0 }", "test error here" ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "exception res");
    });
}

#[test]
fn test_proc_rpc_error() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rpc-error.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["Nashville", ""],
            ["latitude is required.", "latitude is required."],
            ["Nashville", ""],
            ["latitude is required.", "latitude is required."],
            ["Nashville", ""],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "rpc error");
    });
}

#[test]
fn test_proc_c_rings() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/c-rings.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "foo 1", "foo 1", "foo 1", "foo 1", "foo 1", "foo 1", "foo 1", "foo 1", "foo 1", "---",
            "foo 2", "foo 2", "foo 2", "foo 2", "---",
            "bar 1", "bar 1", "bar 1", "bar 1", "bar 1", "bar 1", "bar 1", "bar 1", "---",
            "bar 1", "---",
            "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "bar 2", "---",
            "bar 2", "---",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "c-rings");
    });
}

#[test]
fn test_proc_wall_time() {
    let utc_offset = UtcOffset::from_hms(5, 14, 20).unwrap();
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(utc_offset, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/wall-time.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |_, _, res| {
        let t = OffsetDateTime::now_utc().to_offset(utc_offset);
        let res = res.unwrap().0.as_list().unwrap();
        let res = res.borrow();
        assert_eq!(res.len(), 8);

        assert!((res[0].as_number().unwrap().get() - (t.unix_timestamp_nanos() / 1000000) as f64).abs() < 10.0);
        assert_eq!(res[1].as_number().unwrap().get(), t.year() as f64);
        assert_eq!(res[2].as_number().unwrap().get(), t.month() as u8 as f64);
        assert_eq!(res[3].as_number().unwrap().get(), t.day() as f64);
        assert_eq!(res[4].as_number().unwrap().get(), t.date().weekday().number_from_sunday() as f64);
        assert_eq!(res[5].as_number().unwrap().get(), t.hour() as f64);
        assert_eq!(res[6].as_number().unwrap().get(), t.minute() as f64);
        assert_eq!(res[7].as_number().unwrap().get(), t.second() as f64);
    });
}

#[test]
fn test_proc_to_csv() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/to-csv.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "",
            "test,,again",
            "a,d,c,ef,8",
            " a , d,c ,e f,8",
            " a b c ,ain't,'aint,aint','ain't', x y z ,'",
            " a b c ,\"ain\"\"t\",\"\"\"aint\",\"aint\"\"\",\"\"\"ain\"\"t\"\"\", x y z ,\"\"\"\"",
            " a b c ,\"ain,t\",\",aint\",\"aint,\",\",ain,t,\", x y z ,\",\"",
            "hello,\"one\ntwo\nthree\",world",
            "hello,\"one\ntwo\nthree\"\nworld,test,\"one\ntwo\n\"\nagain,\"\ntwo\",\"\ntwo\n\"",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "to-csv");
    });
}

#[test]
fn test_proc_from_csv() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/from-csv.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [],
            [["test", "", "again"]],
            [["a", "d", "c", "ef", "8"]],
            [[" a ", " d", "c ", "e f", "8"]],
            [[" a b c ", "ain't", "'aint", "aint'", "'ain't'", " x y z ", "'"]],
            [[" a b c ", "ain\"t", "\"aint", "aint\"", "\"ain\"t\"", " x y z ", "\""]],
            [[" a b c ", "ain,t", ",aint", "aint,", ",ain,t,", " x y z ", ","]],
            [["hello", "one\ntwo\nthree", "world"]],
            [
                ["hello", "one\ntwo\nthree"],
                ["world", "test", "one\ntwo\n"],
                ["again", "\ntwo", "\ntwo\n"],
            ],
            [["abcxyz"]],
            "NotCsv { value: \"abc\\\"xyz\\\"\" }",
            "NotCsv { value: \"\\\"abc\\\"xyz\" }",
            "NotCsv { value: \"\\\"abcxyz\" }",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "from-csv");
    });
}

#[test]
fn test_proc_extra_cmp_tests() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/extra-cmp-tests.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [[1, 2, 3, 4, 5], [6, 7, 8, 9, 10]],
            [[3, 1], [3, 2], [4, 1], [4, 2]],
            [false, true, false],
            [false, true, false],
            [true, false, true],
            [false, true, false],
            [false, true, false],
            [true, false, true],
            [true, false, true],
            [false, true, false],
            [false, true, false],
            [false, true, false],
            [false, true, false],
            [false, true, false],
            [false, true, false],
            [true, false, true],
            [false, true, false],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "extra-cmp-tests");
    });
}

#[test]
fn test_proc_stop_fn() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/stop-fn.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["1", 2],
            ["1", 3],
            ["1", 4],
            "",
            ["2", 1],
            ["2", 2],
            "",
            ["3", 1],
            ["3", 2],
            ["3", 3],
            ["3", 4],
            ["3", 5],
            "",
            ["4", 1],
            ["4", 2],
            ["4", 3],
            "",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "stop fn");
    });
}

#[test]
fn test_proc_unicode_strings() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/unicode-strings.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            [
                "x",
                ["x"],
                ["x"],
                1,
                ["x"],
                ["x"],
                ["x"],
                120,
                "x",
            ],
            [
                "hello world!",
                ["h", "e", "l", "l", "o", " ", "w", "o", "r", "l", "d", "!"],
                ["hello", "world"],
                12,
                ["h", "e", "l", "l", "o", " ", "w", "o", "r", "l", "d", "!"],
                ["h", "e", "l", "l", "o", " ", "w", "o", "r", "l", "d", "!"],
                ["h", "e", "l", "l", "o", " ", "w", "o", "r", "l", "d", "!"],
                [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33],
                ["h", "e", "l", "l", "o", " ", "w", "o", "r", "l", "d", "!"],
                "hello world!",
            ],
            [
                "abc😊🥲😎👀a̐éö̲물彩虹xyz",
                ["a", "b", "c", "😊", "🥲", "😎", "👀", "a̐", "é", "ö̲", "물", "彩", "虹", "x", "y", "z"],
                ["abc", "a̐éö̲물", "彩", "虹", "xyz"],
                16,
                ["a", "b", "c", "😊", "🥲", "😎", "👀", "a̐", "é", "ö̲", "물", "彩", "虹", "x", "y", "z"],
                ["a", "b", "c", "😊", "🥲", "😎", "👀", "a̐", "é", "ö̲", "물", "彩", "虹", "x", "y", "z"],
                ["a", "b", "c", "😊", "🥲", "😎", "👀", "a̐", "é", "ö̲", "물", "彩", "虹", "x", "y", "z"],
                [97, 98, 99, 128522, 129394, 128526, 128064, 97, 784, 101, 769, 111, 776, 818, 47932, 24425, 34425, 120, 121, 122],
                ["a", "b", "c", "😊", "🥲", "😎", "👀", "a", "\u{310}", "e", "\u{301}", "o", "\u{308}", "\u{332}", "물", "彩", "虹", "x", "y", "z"],
                "abc😊🥲😎👀a̐éö̲물彩虹xyz",
            ],
            [
                "The quick (\"brown\") fox can't jump 32.3 feet, right?",
                ["T", "h", "e", " ", "q", "u", "i", "c", "k", " ", "(", "\"", "b", "r", "o", "w", "n", "\"", ")", " ", "f", "o", "x", " ", "c", "a", "n", "'", "t", " ", "j", "u", "m", "p", " ", "3", "2", ".", "3", " ", "f", "e", "e", "t", ",", " ", "r", "i", "g", "h", "t", "?"],
                ["The", "quick", "brown", "fox", "can't", "jump", "32.3", "feet", "right"],
                52,
                ["T", "h", "e", " ", "q", "u", "i", "c", "k", " ", "(", "\"", "b", "r", "o", "w", "n", "\"", ")", " ", "f", "o", "x", " ", "c", "a", "n", "'", "t", " ", "j", "u", "m", "p", " ", "3", "2", ".", "3", " ", "f", "e", "e", "t", ",", " ", "r", "i", "g", "h", "t", "?"],
                ["T", "h", "e", " ", "q", "u", "i", "c", "k", " ", "(", "\"", "b", "r", "o", "w", "n", "\"", ")", " ", "f", "o", "x", " ", "c", "a", "n", "'", "t", " ", "j", "u", "m", "p", " ", "3", "2", ".", "3", " ", "f", "e", "e", "t", ",", " ", "r", "i", "g", "h", "t", "?"],
                ["T", "h", "e", " ", "q", "u", "i", "c", "k", " ", "(", "\"", "b", "r", "o", "w", "n", "\"", ")", " ", "f", "o", "x", " ", "c", "a", "n", "'", "t", " ", "j", "u", "m", "p", " ", "3", "2", ".", "3", " ", "f", "e", "e", "t", ",", " ", "r", "i", "g", "h", "t", "?"],
                [84, 104, 101, 32, 113, 117, 105, 99, 107, 32, 40, 34, 98, 114, 111, 119, 110, 34, 41, 32, 102, 111, 120, 32, 99, 97, 110, 39, 116, 32, 106, 117, 109, 112, 32, 51, 50, 46, 51, 32, 102, 101, 101, 116, 44, 32, 114, 105, 103, 104, 116, 63],
                ["T", "h", "e", " ", "q", "u", "i", "c", "k", " ", "(", "\"", "b", "r", "o", "w", "n", "\"", ")", " ", "f", "o", "x", " ", "c", "a", "n", "'", "t", " ", "j", "u", "m", "p", " ", "3", "2", ".", "3", " ", "f", "e", "e", "t", ",", " ", "r", "i", "g", "h", "t", "?"],
                "The quick (\"brown\") fox can't jump 32.3 feet, right?",
            ],
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "unicode strings");
    });
}

#[test]
fn test_proc_ext_raii() {
    let config = Config::<C, StdSystem<C>> {
        request: Some(Rc::new(move |_, key, request, proc| match &request {
            Request::UnknownBlock { name, args } => {
                match name.as_str() {
                    "scopeBlock::enter" => {
                        assert_eq!(args.len(), 1);
                        proc.state.tokens.push(args[0].as_text().unwrap());
                        key.complete(Ok(SimpleValue::Number(Number::new(0.0).unwrap())));
                        return RequestStatus::Handled;
                    }
                    "scopeBlock::exit" => {
                        assert_eq!(args.len(), 0);
                        proc.state.tokens.pop().unwrap();
                        key.complete(Ok(SimpleValue::Number(Number::new(0.0).unwrap())));
                        return RequestStatus::Handled;
                    }
                    "getSomething" => {
                        assert_eq!(args.len(), 0);
                        key.complete(Ok(proc.state.tokens.join_compact(",").into()));
                        return RequestStatus::Handled;
                    }
                    _ => return RequestStatus::UseDefault { key, request },
                }
            }
            _ => RequestStatus::UseDefault { key, request },
        })),
        command: None,
    };
    let parser = ast::Parser {
        stmt_replacements: vec![
            ("scopeBlock".into(), Box::new(|mut args, info, _| {
                assert_eq!(args.len(), 2);
                let f = Box::new(args.pop().unwrap());
                let v = args.pop().unwrap();
                Ok(vec![
                    ast::Stmt { kind: ast::StmtKind::UnknownBlock { name: "scopeBlock::enter".into(), args: vec![v] }, info },
                    ast::Stmt { kind: ast::StmtKind::CallClosure { closure: f, args: vec![], new_entity: None }, info: ast::BlockInfo::none() },
                    ast::Stmt { kind: ast::StmtKind::UnknownBlock { name: "scopeBlock::exit".into(), args: vec![] }, info: ast::BlockInfo::none() },
                ])
            })),
        ],
        ..Default::default()
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(parser, &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/ext-raii.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!([
            "",
            "",
            "end",
            "end,my",
            "end,my,suffering",
            "end,my",
            "end",
            "",
            "",

            "help",
            "help",
            "help,end",
            "help,end,my",
            "help,end,my,suffering",
            "help,end,my",
            "help,end",
            "help",
            "help",

            "help,me",
            "help,me",
            "help,me,end",
            "help,me,end,my",
            "help,me,end,my,suffering",
            "help,me,end,my",
            "help,me,end",
            "help,me",
            "help,me",

            "help,me,please",
            "help,me,please",
            "help,me,please,end",
            "help,me,please,end,my",
            "help,me,please,end,my,suffering",
            "help,me,please,end,my",
            "help,me,please,end",
            "help,me,please",
            "help,me,please",

            "help,me",
            "help",
            "",

            "halp",
            "halp,mi",
            "halp,mi",
            "halp,mi,end",
            "halp,mi,end,my",
            "catch 1",
            "",
            "",

            "hlp,m,pl",
            "hlp,m,pl",
            "hlp,m,pl,end",
            "hlp,m,pl,end,my",
            "catch 2",
            "hlp,m",
            "",

            "hl",
            "hl,mee",
            "hl,mee,plz",
            "catch 3",
            "hl,mee",
            "hl,mee",
            "hl",
            "",

            "heelp,miii,plox",
            "heelp,miii,plox",
            "heelp,miii,plox,end",
            "heelp,miii,plox,end,my",
            "heelp,miii,plox,end",
            "heelp,miii,plox",
            "heelp,miii,plox",
            "",
        ])).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "call frame state");
    });
}

#[test]
fn test_proc_extra_blocks() {
    let actions: Rc<RefCell<Vec<Vec<Text>>>> = Rc::new(RefCell::new(vec![]));
    let actions_clone = actions.clone();
    let config = Config::<C, StdSystem<C>> {
        request: Some(Rc::new(move |_, key, request, _| match &request {
            Request::UnknownBlock { name, args } => {
                match name.as_str() {
                    "tuneScopeSetInstrument" => {
                        assert_eq!(args.len(), 1);
                        let ins = args[0].as_text().unwrap();
                        actions_clone.borrow_mut().push(vec!["set ins".into(), ins]);
                        key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                    }
                    "tuneScopeSetVolume" => {
                        assert_eq!(args.len(), 1);
                        let vol = args[0].as_number().unwrap();
                        actions_clone.borrow_mut().push(vec!["set vol".into(), SimpleValue::stringify_number(vol)]);
                        key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                    }
                    "tuneScopePlayChordForDuration" => {
                        assert_eq!(args.len(), 2);
                        let notes = args[0].to_simple().unwrap().into_json::<C, StdSystem<C>>().unwrap();
                        let duration = args[1].as_text().unwrap();
                        actions_clone.borrow_mut().push(vec!["play chord".into(), format_text!("{notes}"), duration]);
                        key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                    }
                    "tuneScopePlayTracks" => {
                        assert_eq!(args.len(), 2);
                        let time = args[0].as_text().unwrap();
                        let tracks = args[1].to_simple().unwrap().into_json::<C, StdSystem<C>>().unwrap();
                        actions_clone.borrow_mut().push(vec!["play tracks".into(), time, format_text!("{tracks}")]);
                        key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                    }
                    "tuneScopeNote" => {
                        assert_eq!(args.len(), 1);
                        let note = args[0].as_text().unwrap();
                        actions_clone.borrow_mut().push(vec!["get note".into(), note.clone()]);
                        key.complete(Ok(SimpleValue::Text(format_compact!("nte {note}")).into()));
                    }
                    "tuneScopeDuration" => {
                        assert_eq!(args.len(), 1);
                        let duration = args[0].as_text().unwrap();
                        actions_clone.borrow_mut().push(vec!["get duration".into(), duration.clone()]);
                        key.complete(Ok(SimpleValue::Text(format_compact!("drt {duration}")).into()));
                    }
                    "tuneScopeSection" => {
                        assert_eq!(args.len(), 1);
                        let items = args[0].to_simple().unwrap().into_json::<C, StdSystem<C>>().unwrap();
                        actions_clone.borrow_mut().push(vec!["make section".into(), format_text!("{items}")]);
                        key.complete(Ok(SimpleValue::from_json(items).unwrap().into()));
                    }
                    _ => return RequestStatus::UseDefault { key, request },
                }
                RequestStatus::Handled
            }
            _ => RequestStatus::UseDefault { key, request },
        })),
        command: None,
    };

    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/extra-blocks.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!("cool")).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "extra blocks");
    });

    let expected = vec![
        vec![CompactString::new("set ins"), CompactString::new("Clarinet")],
        vec![CompactString::new("set vol"), CompactString::new("1337")],
        vec![CompactString::new("get note"), CompactString::new("A3")],
        vec![CompactString::new("get note"), CompactString::new("Fb3")],
        vec![CompactString::new("play chord"), json!(["nte A3", "nte Fb3"]).to_compact_string(), CompactString::new("Quarter")],
        vec![CompactString::new("play tracks"), CompactString::new("4/4"), json!([true, false, 3.0]).to_compact_string()],
        vec![CompactString::new("get note"), CompactString::new("C4")],
        vec![CompactString::new("get duration"), CompactString::new("Half")],
        vec![CompactString::new("make section"), json!(["nte C4", "drt Half"]).to_compact_string()],
        vec![CompactString::new("play tracks"), CompactString::new("6/8"), json!(["nte C4", "drt Half"]).to_compact_string()],
    ];
    assert_eq!(&*actions.borrow(), &expected);
}

#[test]
fn test_proc_play_notes() {
    let sound_events = Rc::new(RefCell::new(vec![]));
    let sound_events_clone = sound_events.clone();
    let config = Config::<C, StdSystem<C>> {
        request: None,
        command: Some(Rc::new(move |_, key, command, _| match command {
            Command::PlayNotes { notes, beats, blocking } => {
                sound_events_clone.borrow_mut().push((notes, beats, blocking));
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            _ => CommandStatus::UseDefault { key, command },
        })),
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let (mut env, _) = get_running_proc(Default::default(), &format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/play-notes.xml"),
        methods = "",
    ), Settings { rpc_error_scheme: ErrorScheme::Soft, ..Default::default() }, system, |_| SymbolTable::default());

    run_till_term(&mut env, |mc, _, res| {
        let expect = Value::from_simple(mc, SimpleValue::from_json(json!("done!")).unwrap());
        assert_values_eq(&res.unwrap().0, &expect, 1e-5, "play notes");
    });

    let sound_events = &*sound_events.borrow();
    assert_eq!(sound_events.len(), 13);

    assert!(sound_events[0].0 == [Note::from_midi(60, false).unwrap()] && (sound_events[0].1.get() - 0.5).abs() < 1e-10 && sound_events[0].2);
    assert!(sound_events[1].0 == [Note::from_midi(51, false).unwrap()] && (sound_events[1].1.get() - 1.0).abs() < 1e-10 && sound_events[1].2);
    assert!(sound_events[2].0 == [Note::from_midi(82, false).unwrap()] && (sound_events[2].1.get() - 2.333).abs() < 1e-10 && sound_events[2].2);
    assert!(sound_events[3].0 == [Note::from_midi(86, true).unwrap()] && (sound_events[3].1.get() - 0.5).abs() < 1e-10 && sound_events[3].2);
    assert!(sound_events[4].0 == [Note::from_midi(58, true).unwrap()] && (sound_events[4].1.get() - 4.0).abs() < 1e-10 && sound_events[4].2);
    assert!(sound_events[5].0 == [Note::from_midi(76, false).unwrap()] && (sound_events[5].1.get() - 1.5).abs() < 1e-10 && sound_events[5].2);
    assert!(sound_events[6].0 == [Note::from_midi(104, true).unwrap()] && (sound_events[6].1.get() - 0.5).abs() < 1e-10 && sound_events[6].2);
    assert!(sound_events[7].0 == [Note::from_midi(45, false).unwrap(), Note::from_midi(58, true).unwrap()] && (sound_events[7].1.get() - 0.9).abs() < 1e-10 && sound_events[7].2);
    assert!(sound_events[8].0 == [Note::from_midi(45, false).unwrap(), Note::from_midi(57, false).unwrap(), Note::from_midi(69, false).unwrap(), Note::from_midi(73, true).unwrap()] && (sound_events[8].1.get() - 0.1).abs() < 1e-10 && sound_events[8].2);
    assert!(sound_events[9].0 == [] && (sound_events[9].1.get() - 0.2).abs() < 1e-10 && sound_events[9].2);
    assert!(sound_events[10].0 == [] && (sound_events[10].1.get() - 1.75).abs() < 1e-10 && sound_events[10].2);
    assert!(sound_events[11].0 == [] && (sound_events[11].1.get() - 2.4).abs() < 1e-10 && sound_events[11].2);
    assert!(sound_events[12].0 == [] && (sound_events[12].1.get() - 4.0).abs() < 1e-10 && sound_events[12].2);
}
