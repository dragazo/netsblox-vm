use std::prelude::v1::*;
use std::rc::Rc;

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

fn get_running_proc(xml: &str) -> EnvArena {
    EnvArena::new(Default::default(), |mc| {
        let parser = ast::ParserBuilder::default().build().unwrap();
        let ast = parser.parse(xml).unwrap();
        assert_eq!(ast.roles.len(), 1);

        let glob = GcCell::allocate(mc, GlobalContext::from_ast(mc, &ast.roles[0]));
        let (code, locs) = ByteCode::compile(&ast.roles[0]);
        let main = locs.funcs.iter().find(|x| x.0.trans_name.trim() == "main").expect("no main function at global scope");

        let mut proc = Process::new(Rc::new(code), main.1, glob, glob.read().entities[0], SettingsBuilder::default().build().unwrap());
        assert!(!proc.is_running());
        proc.initialize(Default::default(), None);
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
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/ret.xml"),
        methods = "",
    ));

    run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
        Value::String(x) => assert_eq!(&*x, ""),
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sum_123n() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/sum-123n.xml"),
        methods = "",
    ));

    for (n, expect) in [(0.0, 0.0), (1.0, 1.0), (2.0, 3.0), (3.0, 6.0), (4.0, 10.0), (5.0, 15.0), (6.0, 21.0)] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("n", Shared::Unique(n.into()));
            env.proc.write(mc).initialize(locals, None);
        });
        run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
            Value::Number(ret) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        });
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/recursive-factorial.xml"),
        methods = "",
    ));

    for (n, expect) in [(0.0, 1.0), (1.0, 1.0), (2.0, 2.0), (3.0, 6.0), (4.0, 24.0), (5.0, 120.0), (6.0, 720.0), (7.0, 5040.0)] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("n", Shared::Unique(n.into()));
            env.proc.write(mc).initialize(locals, None);
        });
        run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
            Value::Number(ret) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        });
    }
}

#[test]
fn test_proc_loops_lists_basic() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/loops-lists-basic.xml"),
        methods = "",
    ));

    run_till_term(&mut env, &system, |mc, _, res| {
        let expected = Value::from_simple(mc, simple_value!([
            [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0],
            [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0],
            [1.0,2.0,3.0,4.0,5.0,6.0,7.0],
            [2.0,3.0,4.0,5.0,6.0,7.0],
            [3.0,4.0,5.0,6.0,7.0],
            [4.0,5.0,6.0,7.0],
            [5.0,6.0,7.0],
            [6.0,7.0],
            [7.0],
            [8.0],
            [9.0,8.0],
            [10.0,9.0,8.0],
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
            [56.0,44.0,176.0],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expected, 1e-10, "loops lists");
    });
}

#[test]
fn test_proc_recursively_self_containing_lists() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/recursively-self-containing-lists.xml"),
        methods = "",
    ));

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
                        let basic = Value::List(GcCell::allocate(mc, got[..10].iter().cloned().collect()));
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

            check("left mode", mc, &res[0], &Value::from_simple(mc, simple_value!([1.0,4.0,9.0,16.0,25.0,36.0,49.0,64.0,81.0,100.0])));
            check("right mode", mc, &res[1], &Value::from_simple(mc, simple_value!([2.0,4.0,8.0,16.0,32.0,64.0,128.0,256.0,512.0,1024.0])));
            check("both mode", mc, &res[2], &Value::from_simple(mc, simple_value!([1.0,4.0,27.0,256.0,3125.0,46656.0,823543.0,16777216.0,387420489.0,10000000000.0])));
            check("unary mode", mc, &res[3], &Value::from_simple(mc, simple_value!([-1.0,-2.0,-3.0,-4.0,-5.0,-6.0,-7.0,-8.0,-9.0,-10.0])));
        }
        x => panic!("{:?}", x),
    });
}

#[test]
fn test_proc_sieve_of_eratosthenes() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/sieve-of-eratosthenes.xml"),
        methods = "",
    ));

    env.mutate(|mc, env| {
        let mut locals = SymbolTable::default();
        locals.redefine_or_define("n", Shared::Unique(100.0.into()));

        let mut proc = env.proc.write(mc);
        assert!(proc.is_running());
        proc.initialize(locals, None);
        assert!(proc.is_running());
    });

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-100, "primes");
    });
}

#[test]
fn test_proc_early_return() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/early-return.xml"),
        methods = "",
    ));

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([1,3]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-100, "res");
    });
}

#[test]
fn test_proc_short_circuit() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/short-circuit.xml"),
        methods = "",
    ));

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
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/all-arithmetic.xml"),
        methods = "",
    ));

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
            [7.0, 8.0, -7.0, -8.0],
            [56.8, 6.3, inf, inf],
            [-56.8, 6.3, -inf, inf],
            [8.0, 8.0, -7.0, -7.0, inf, -inf],
            [7.0, 7.0, -8.0, -8.0, inf, -inf],
            [2.701851217221259, inf],
            [0.12706460860135046, 0.7071067811865475],
            [0.9918944425900297, 0.7071067811865476],
            [0.12810295445305653, 1.0],
            [0.0, 30.0, -30.0],
            [90.0, 60.0, 120.0],
            [0.0, 26.56505117707799, -26.56505117707799, 88.72696997994328, -89.91635658567779],
            [-0.6931471805599453, 0.0, 2.186051276738094, inf],
            [-0.3010299956639812, 0.0, 0.9493900066449128, inf],
            [-1.0, 0.0, 3.1538053360790355, inf],
            [1.0, 3.3201169227365472, 0.0001363889264820114, inf, 0.0],
            [1.0, 15.848931924611133, 1.2589254117941663e-9, inf, 0.0],
            [1.0, 2.2973967099940698, 0.002093307544016197, inf, 0.0],
            [0.0, 1.2, -8.9, inf, -inf],
        ]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-7, "short circuit test");
    });
}

#[test]
fn test_proc_lambda_local_shadow_capture() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/lambda-local-shadow-capture.xml"),
        methods = "",
    ));

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([1.0, 0.0, 1.0]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "local shadow capture");
    });
}

#[test]
fn test_proc_generators_nested() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/generators-nested.xml"),
        methods = "",
    ));

    run_till_term(&mut env, &system, |mc, _, res| {
        let expect = Value::from_simple(mc, simple_value!([1, 25, 169, 625, 1681, 3721, 7225, 12769, 21025, 32761]));
        assert_values_eq(&res.unwrap().0.unwrap(), &expect, 1e-20, "nested generators");
    });
}

#[test]
fn test_proc_call_in_closure() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/call-in-closure.xml"),
        methods = "",
    ));

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
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = r#"<variable name="counter"><l>0</l></variable>"#,
        fields = "",
        funcs = include_str!("blocks/warp-yields.xml"),
        methods = "",
    ));

    for (mode, (expected_counter, expected_yields)) in [(12, 12), (13, 13), (17, 0), (18, 0), (16, 0), (17, 2), (14, 0), (27, 3), (30, 7), (131, 109), (68, 23), (51, 0), (63, 14)].into_iter().enumerate() {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("mode", Shared::Unique((mode as f64).into()));
            env.proc.write(mc).initialize(locals, None);
        });

        run_till_term(&mut env, &system, |_, env, res| {
            let yields = res.unwrap().1;
            let counter = env.glob.read().globals.lookup("counter").unwrap().get();
            assert_values_eq(&counter, &(expected_counter as f64).into(), 1e-20, &format!("yield test (mode {}) value", mode));
            if yields != expected_yields { panic!("yield test (mode {}) yields - got {} expected {}", mode, yields, expected_yields) }
        });
    }
}

#[test]
fn test_proc_string_ops() {
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/string-ops.xml"),
        methods = "",
    ));

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
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/str-cmp-case-insensitive.xml"),
        methods = "",
    ));

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
    let system = StdSystem::new("https://editor.netsblox.org".to_owned(), None);
    let mut env = get_running_proc(&format!(include_str!("templates/generic-static.xml"),
        globals = "",
        fields = "",
        funcs = include_str!("blocks/rpc-call-basic.xml"),
        methods = "",
    ));

    for (lat, long, city) in [(36.1627, -86.7816, "Nashville"), (40.8136, -96.7026, "Lincoln"), (40.7608, -111.8910, "Salt Lake City")] {
        env.mutate(|mc, env| {
            let mut locals = SymbolTable::default();
            locals.redefine_or_define("lat", Shared::Unique(lat.into()));
            locals.redefine_or_define("long", Shared::Unique(long.into()));
            env.proc.write(mc).initialize(locals, None);
        });
        run_till_term(&mut env, &system, |_, _, res| match res.unwrap().0.unwrap() {
            Value::String(ret) => assert_eq!(&*ret, city),
            x => panic!("{:?}", x),
        });
    }
}
