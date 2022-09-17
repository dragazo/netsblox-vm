use std::prelude::v1::*;
use std::cell::RefCell;
use std::rc::Rc;
use std::fmt::Write;

use crate::*;
use crate::gc::*;
use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;

use super::*;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proc: GcCell<'gc, Process<'gc, StdSystem>>,
    glob: GcCell<'gc, GlobalContext<'gc>>,
}
make_arena!(EnvArena, Env);

fn get_running_proc(xml: &str, settings: Settings, system: &StdSystem) -> EnvArena {
    EnvArena::new(Default::default(), |mc| {
        let parser = ast::ParserBuilder::default().build().unwrap();
        let ast = parser.parse(xml).unwrap();
        assert_eq!(ast.roles.len(), 1);

        let glob = GcCell::allocate(mc, GlobalContext::from_ast(mc, &ast.roles[0]));
        let (code, locs) = ByteCode::compile(&ast.roles[0]);
        let main = locs.funcs.iter().find(|x| x.0.trans_name.trim() == "main").expect("no main function at global scope");

        let mut proc = Process::new(Rc::new(code), main.1, glob, glob.read().entities[0], settings);
        assert!(!proc.is_running());
        proc.initialize(Default::default(), None, None, system);
        assert!(proc.is_running());

        Env { glob, proc: GcCell::allocate(mc, proc) }
    })
}

fn run_till_term<F>(env: &mut EnvArena, system: &StdSystem, and_then: F) where F: for<'gc> FnOnce(MutationContext<'gc, '_>, &Env, Result<(Option<Value<'gc>>, usize), ExecError>) {
    env.mutate(|mc, env| {
        let mut proc = env.proc.write(mc);
        assert!(proc.is_running());

        let mut yields = 0;
        let ret = loop {
            match proc.step(mc, &system) {
                Ok(ProcessStep::Idle) => panic!(),
                Ok(ProcessStep::Normal) => (),
                Ok(ProcessStep::Yield) => yields += 1,
                Ok(ProcessStep::Terminate { result }) => break result,
                Ok(ProcessStep::Broadcast { .. }) => panic!("proc tests should not broadcast"),
                Err(e) => return and_then(mc, env, Err(e)),
            }
        };

        assert!(!proc.is_running());
        and_then(mc, env, Ok((ret, yields)));
    });
}

#[test]
fn test_proc_ret() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/ret.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
        Value::String(x) => assert_eq!(&*x, ""),
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sum_123n() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/sum-123n.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    for (n, expect) in [(0, simple_value!("0")), (1, simple_value!(1)), (2, simple_value!(3)), (3, simple_value!(6)), (4, simple_value!(10)), (5, simple_value!(15)), (6, simple_value!(21))] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("n", Shared::Unique((n as f64).into()));
            env.proc.write(mc).initialize(locals, None, None, &system);
        });
        run_till_term(&mut env, &system, |mc, _, res| {
            let expect = Value::from_simple(mc, expect);
            assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "sum 123n");
        });
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/recursive-factorial.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    for (n, expect) in [(0, simple_value!("1")), (1, simple_value!("1")), (2, simple_value!(2)), (3, simple_value!(6)), (4, simple_value!(24)), (5, simple_value!(120)), (6, simple_value!(720)), (7, simple_value!(5040))] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("n", Shared::Unique((n as f64).into()));
            env.proc.write(mc).initialize(locals, None, None, &system);
        });
        run_till_term(&mut env, &system, |mc, _, res| {
            let expect = Value::from_simple(mc, expect);
            assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "recursive factorial");
        });
    }
}

#[test]
fn test_proc_loops_lists_basic() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/loops-lists-basic.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expected = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expected, 1e-10, "loops lists");
    });
}

#[test]
fn test_proc_recursively_self_containing_lists() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/recursively-self-containing-lists.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| match res.unwrap().0.unwrap() {
        Value::List(res) => {
            let res = res.read();
            assert_eq!(res.len(), 4);

            fn check<'gc>(name: &str, mc: MutationContext<'gc, '_>, got: &Value<'gc>, expected_basic: &Value<'gc>) {
                let orig_got = got;
                match got {
                    Value::List(got) => {
                        let top_weak = got;
                        let got = got.read();
                        if got.len() != 11 { panic!("{} - len error - got {} expected 11", name, got.len()) }
                        let basic = Value::List(GcCell::allocate(mc, got.iter().take(10).cloned().collect()));
                        assert_values_eq(&basic, expected_basic, 1e-10, name);
                        match &got[10] {
                            Value::List(nested) => if top_weak.as_ptr() != nested.as_ptr() {
                                panic!("{} - self-containment not ref-eq - got {:?}", name, nested.read());
                            }
                            x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                        }
                        assert_eq!(orig_got.identity(), got[10].identity());
                    }
                    x => panic!("{} - not a list - got {:?}", name, x.get_type()),
                }
            }

            check("left mode", mc, &res[0], &Value::from_simple(mc, simple_value!([1,4,9,16,25,36,49,64,81,100])));
            check("right mode", mc, &res[1], &Value::from_simple(mc, simple_value!([2,4,8,16,32,64,128,256,512,1024])));
            check("both mode", mc, &res[2], &Value::from_simple(mc, simple_value!([1,4,27,256,3125,46656,823543,16777216,387420489,10000000000])));
            check("unary mode", mc, &res[3], &Value::from_simple(mc, simple_value!([-1,-2,-3,-4,-5,-6,-7,-8,-9,-10])));
        }
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sieve_of_eratosthenes() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/sieve-of-eratosthenes.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    env.mutate(|mc, env| {
        let mut locals = SymbolTable::default();
        locals.redefine_or_define("n", Shared::Unique(100.0.into()));

        let mut proc = env.proc.write(mc);
        assert!(proc.is_running());
        proc.initialize(locals, None, None, &system);
        assert!(proc.is_running());
    });

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-100, "primes");
    });
}

#[test]
fn test_proc_early_return() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/early-return.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([1,3]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-100, "res");
    });
}

#[test]
fn test_proc_short_circuit() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/short-circuit.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-100, "short circuit test");
    });
}

#[test]
fn test_proc_all_arithmetic() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/all-arithmetic.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let inf = std::f64::INFINITY;
        let expect = Value::from_simple(mc, simple_value!([
            [8.5, 2.9, -2.9, -8.5],
            [2.9, 8.5, -8.5, -2.9],
            [15.96, -15.96, -15.96, 15.96],
            [2.035714285714286, -2.035714285714286, -2.035714285714286, 2.035714285714286],
            [inf, -inf, -inf, inf],
            [130.75237792066878, 0.007648044463151016],
            [0.1, -2.7, 2.7, -0.1, 5.8, -1.3, 1.3, -5.8],
            [7, 8, -7, -8],
            [56.8, 6.3, inf, inf],
            [-56.8, 6.3, -inf, inf],
            [8, 8, -7, -7, inf, -inf],
            [7, 7, -8, -8, inf, -inf],
            [2.701851217221259, inf],
            [0.12706460860135046, 0.7071067811865475],
            [0.9918944425900297, 0.7071067811865476],
            [0.12810295445305653, 1],
            [0, 30, -30],
            [90, 60, 120],
            [0, 26.56505117707799, -26.56505117707799, 88.72696997994328, -89.91635658567779],
            [-0.6931471805599453, 0, 2.186051276738094, inf],
            [-0.3010299956639812, 0, 0.9493900066449128, inf],
            [-1, 0, 3.1538053360790355, inf],
            [1, 3.3201169227365472, 0.0001363889264820114, inf, 0],
            [1, 15.848931924611133, 1.2589254117941663e-9, inf, 0],
            [1, 2.2973967099940698, 0.002093307544016197, inf, 0],
            ["0", "1.2", "-8.9", inf, -inf],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-7, "short circuit test");
    });
}

#[test]
fn test_proc_lambda_local_shadow_capture() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/lambda-local-shadow-capture.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!(["1", 0, "1"]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "local shadow capture");
    });
}

#[test]
fn test_proc_generators_nested() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/generators-nested.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([1, 25, 169, 625, 1681, 3721, 7225, 12769, 21025, 32761]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "nested generators");
    });
}

#[test]
fn test_proc_call_in_closure() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/call-in-closure.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [2, 4, 6, 8, 10],
            [1, 3, 5, 7, 9],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "call in closure");
    });
}

#[test]
fn test_proc_warp_yields() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="counter"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/warp-yields.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    for (mode, (expected_counter, expected_yields)) in [(12, 12), (13, 13), (17, 0), (18, 0), (16, 0), (17, 2), (14, 0), (27, 3), (30, 7), (131, 109), (68, 23), (51, 0), (63, 14)].into_iter().enumerate() {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("mode", Shared::Unique((mode as f64).into()));
            env.proc.write(mc).initialize(locals, None, None, &system);
        });

        run_till_term(&mut env, &system, |mc, env, res| {
            let (res, yields) = res.unwrap();
            assert_values_eq(res.as_ref().unwrap(), &Value::from_simple(mc, simple_value!("x")), 1e-20, &format!("yield test (mode {mode}) res"));
            let counter = env.glob.read().globals.lookup("counter").unwrap().get();
            assert_values_eq(&counter, &(expected_counter as f64).into(), 1e-20, &format!("yield test (mode {mode}) value"));
            if yields != expected_yields { panic!("yield test (mode {}) yields - got {} expected {}", mode, yields, expected_yields) }
        });
    }
}

#[test]
fn test_proc_string_ops() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/string-ops.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
            [ "test", "", "23", "21", "a", "b", "", "" ],
            [
                [ "test", "", "23", "21", "a", "b", "", "" ],
                [ "perp", "", "3", "", "44", "3", "2" ],
            ],
            { "a" => [ 1, "a", [ 7, [] ], { "g" => "4", "h" => [] }], "b" => 3, "c" => "hello world" },
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
            { "a" => 1, "b" => 2, "c" => 3, "d" => 4, "e" => 5, "f" => 6, "g" => 7, "h" => 8, "i" => 9, "j" => 10 },
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "string ops");
    });
}

#[test]
fn test_proc_str_cmp_case_insensitive() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/str-cmp-case-insensitive.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            false, true, true, true, false,
            [
                false, true,
                [false, true, true, false],
            ],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "str cmp case insensitive");
    });
}

#[test]
fn test_proc_rpc_call_basic() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rpc-call-basic.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    for (lat, long, city) in [(36.1627, -86.7816, "Nashville"), (40.8136, -96.7026, "Lincoln"), (40.7608, -111.8910, "Salt Lake City")] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("lat", Shared::Unique(lat.into()));
            locals.redefine_or_define("long", Shared::Unique(long.into()));
            env.proc.write(mc).initialize(locals, None, None, &system);
        });
        run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
            Value::String(ret) => assert_eq!(&*ret, city),
            x => panic!("{:?}", x),
        });
    }
}

#[test]
fn test_proc_list_index_blocks() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-index-blocks.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "index ops");
    });
}

#[test]
fn test_proc_literal_types() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/literal-types.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([ "50e4", "50e4s" ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "literal types check");
    });
}

#[test]
fn test_proc_say() {
    let output = Rc::new(RefCell::new(String::new()));
    let output_cpy = output.clone();
    let config = StdSystemConfig::builder()
        .print(Rc::new(move |v, _| if let Some(v) = v { writeln!(*output_cpy.borrow_mut(), "{:?}", v).unwrap() }))
        .build().unwrap();
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, config);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/say.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |_, _, _| ());
    assert_eq!(output.borrow().as_str(), "\"Greetings, human.\"\n\"I will destroy him.\"\n");
}

#[test]
fn test_proc_timer_wait() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/timer-wait.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    let start = std::time::Instant::now();
    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([0.0, 0.05, 0.15, 0.3, 0.5, 0.75, 1.05, 1.4, 1.8, 2.25, 2.75]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 0.01, "timer checks");
    });
    let duration = start.elapsed().as_millis();
    assert!(duration >= 2750);
}

#[test]
fn test_proc_cons_cdr() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/cons-cdr.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "cons cdr checks");
    });
}

#[test]
fn test_proc_list_find_contains() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-find-contains.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "cons cdr checks");
    });
}

#[test]
fn test_proc_append() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/append.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [1,2,3,4,"test"],
            [],
            [1,2,3,4],
            [1,2,3,4,1,2,3,4],
            [1,2,3,4,2,3,"4"],
            [1,2,3,4,2,3,"4"],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "append result");
    });
}

#[test]
fn test_proc_foreach_mutate() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/foreach-mutate.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11],
            [2,4,6,8,10,12,14,16,18,20],
            [2, 1.5, 1.3333333, 3, 2, 1.6666666, 4, 2.5, 2, 3, 2.5, 2.33333, 4, 3, 2.666666, 5, 3.5, 3, 4, 3.5, 3.333333, 5, 4, 3.666666, 6, 4.5, 4],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "map result");
    });
}

#[test]
fn test_proc_map() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/map.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [1,2,3,4,5,6,7,8,9,10,2,4,6,8,10,12,14,16,18,20],
            [1,4,9,16,25,36,49,64,81,100],
            [1.0, 1.4142135623730951, 1.7320508075688772, 2.0, 2.23606797749979, 2.449489742783178, 2.6457513110645907, 2.8284271247461903, 3.0, 3.1622776601683795, 1.4142135623730951, 2.0, 2.449489742783178, 2.8284271247461903, 3.1622776601683795, 3.4641016151377544, 3.7416573867739413, 4.0, 4.242640687119285, 4.47213595499958],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "map result");
    });
}

#[test]
fn test_proc_keep_find() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/keep-find.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [1,2,3,4,5,6,7,8,9,10,4,5,6,7,8,9,10,11,12,13],
            [3,6,9],
            [10,11,12,13,14,15,16,17,18,19,20,17,18,19,20,21],
            14,
            "",
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "keep/find results");
    });
}

#[test]
fn test_proc_combine() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/combine.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "keep/find results");
    });
}

#[test]
fn test_proc_autofill_closure_params() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="foo"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/autofill-closure-params.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [3,6,9,12,15,18,21,24,27,30],
            [3,4,5,6,7,8,9,10,11,12],
            [1,3,5,7,9],
            55,
            3628800,
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "autofill closure params");
    });
}

#[test]
fn test_proc_pick_random() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/pick-random.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |_, _, res| {
        let results = {
            let mut out = vec![];
            for row in res.unwrap().0.unwrap().as_list().unwrap().read().iter() {
                let mut vals = vec![];
                for val in row.as_list().unwrap().read().iter() {
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

        for val in results[0].iter() {
            if !(1.0..=10.0).contains(val) || (*val != *val as i64 as f64) {
                panic!("res[0] error: {val}");
            }
        }
        for val in results[1].iter() {
            if !(-6.0..=5.0).contains(val) || (*val != *val as i64 as f64) {
                panic!("res[1] error: {val}");
            }
        }

        let mut int_count = 0;
        for val in results[2].iter() {
            if !(-6.0..=5.1).contains(val) {
                panic!("res[2] error: {val}");
            }
            if *val == *val as i64 as f64 { int_count += 1; }
        }
        assert!(int_count <= 5); // hard to test rng, but this is almost certainly true

        int_count = 0;
        for val in results[3].iter() {
            if !(0.0..=0.9999).contains(val) {
                panic!("res[3] error: {val}");
            }
            if *val == *val as i64 as f64 { int_count += 1; }
        }
        assert!(int_count <= 5); // hard to test rng, but this is almost certainly true
    });
}

#[test]
fn test_proc_rand_list_ops() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rand-list-ops.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |_, _, res| {
        let (results, last) = {
            fn extract_value(val: &Value) -> String {
                match val {
                    Value::Number(x) => x.to_string(),
                    Value::String(x) if matches!(x.as_str(), "hello" | "goodbye") => x.as_str().to_owned(),
                    x => panic!("{x:?}"),
                }
            }

            let mut out = vec![];
            let res = res.unwrap().0.unwrap().as_list().unwrap();
            let res = res.read();
            let mut res = res.iter();
            let last = loop {
                match res.next().unwrap() {
                    Value::List(row) => {
                        let mut vals = vec![];
                        for val in row.read().iter() {
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
        assert!(results[1].iter().any(|x| x == "hello"));
        assert!(!results[1].iter().any(|x| x == "goodbye"));
        assert!(results[2].iter().any(|x| x == "goodbye"));

        assert!(results[2].contains(&last));
    });
}

#[test]
fn test_proc_variadic_sum_product() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-sum-product.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "variadic sum product");
    });
}

#[test]
fn test_proc_variadic_min_max() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/variadic-min-max.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([ 1, 2, 9, 17 ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "variadic min/max");
    });
}

#[test]
fn test_proc_atan2_new_cmp() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/atan2-new-cmp.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [18.43494882, 116.5650511, -32.0053832, -158.198590],
            [14.03624346, 53.13010235, -18.4349488],
            [false, true, true],
            [true, true, false],
            [true, false, true],
            [true, false, true],
            [false, true, true],
            [false, true],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "atan2 and new cmp");
    });
}

#[test]
fn test_proc_flatten() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/flatten.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            ["3", "6", "7", "10", "12", "16", "20"],
            ["6", "1", "3", "6", "1", "3", "6", "1", "3"],
            ["hello world"],
            [""],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "flatten");
    });
}

#[test]
fn test_proc_list_len_rank_dims() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-len-rank-dims.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            [0, 1, [0]],
            [3, 1, [3]],
            [3, 2, [3, 0]],
            [3, 2, [3, 1]],
            [5, 3, [5, 3, 1]],
            [6, 5, [6, 3, 1, 3, 1]],
            [2, 2, [2, 10]],
            [2, 2, [2, 10]],
            [0, []],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "list len, rank, dims");
    });
}

#[test]
fn test_proc_list_rev() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-rev.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            ["2", "4", "1"],
            ["2", ["6", "4", "3"], "8", "1"],
            [["6", ["6", "4", "3"], "3"], ["6", "4", "3"], "8", "1"],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "list rev");
    });
}

#[test]
fn test_proc_list_reshape() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-reshape.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
            [],
            "3",
            "3",
            [[6, 6, 6], [6, 6, 6]],
            [["", ""], ["", ""]],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "list reshape");
    });
}

#[test]
fn test_proc_list_json() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-json.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
            r#"[]"#,
            r#"["test"]"#,
            r#"["test",25.0,"12"]"#,
            r#"[["1",["2"],[],[["2"]]],"\"another\"",["1",["2"],[],[["2"]]],"[{}]"]"#,
            r#"14.0"#,
            r#""hello world \"again\"""#,
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "list json");
    });
}

#[test]
fn test_proc_list_combinations() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None, StdSystemConfig::builder().build().unwrap());
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/list-combinations.xml"),
        methods = "",
    ), Settings::builder().build().unwrap(), &system);

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([
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
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-5, "list combinations");
    });
}
