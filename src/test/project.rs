use std::prelude::v1::*;
use std::collections::BTreeSet;
use std::rc::Rc;

use crate::*;
use crate::gc::*;
use crate::json::*;
use crate::bytecode::*;
use crate::project::*;
use crate::std_system::*;

use super::*;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proj: GcCell<'gc, Project<'gc, C, StdSystem<C>>>,
}
type EnvArena = Arena<Rootable![Env<'gc>]>;

fn get_running_project(xml: &str, system: Rc<StdSystem<C>>) -> EnvArena {
    EnvArena::new(Default::default(), |mc| {
        let parser = ast::Parser::default();
        let ast = parser.parse(xml).unwrap();
        assert_eq!(ast.roles.len(), 1);

        let (bytecode, init_info, _, _) = ByteCode::compile(&ast.roles[0]).unwrap();

        let mut proj = Project::from_init(mc, &init_info, Rc::new(bytecode), Settings::default(), system);
        proj.input(Input::Start);
        Env { proj: GcCell::allocate(mc, proj) }
    })
}

fn run_till_term<'gc>(mc: MutationContext<'gc, '_>, proj: &mut Project<'gc, C, StdSystem<C>>) -> Result<(), ExecError<C, StdSystem<C>>> {
    loop {
        match proj.step(mc) {
            ProjectStep::Idle => return Ok(()),
            ProjectStep::Error { error, .. } => return Err(error),
            ProjectStep::Normal | ProjectStep::ProcessTerminated { .. } | ProjectStep::Yield => (),
        }
    }
}

#[test]
fn test_proj_counting() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/counting.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &Number::new(60.0).unwrap().into(), 1e-20, "counter");
    });
}

#[test]
fn test_proj_effects() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/effects.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            [0, 0, 0, 0, 0, 0, 0, 0, 0],
            [12, 47, 32, 14, 11, -37, 123, 65, 74],
            [54, 79, 87, 7, 23, 37, 168, 66, -6],
            [350, 0, 0, 0, 23, 37, 168, 66, -6],
            [40, 100, 100, 100, 23, 37, 168, 66, -6],
            [120, 0, 0, 0, 23, 37, 168, 66, -6],
            [301, 100, 100, 100, 23, 37, 168, 66, -6],
            [0, 0, 0, 0, 0, 0, 0, 0, 0],
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_costumes() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/costumes.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let res = global_context.globals.lookup("res").unwrap().get().clone();
        match &res {
            Value::List(x) => {
                let x = x.read();
                assert_eq!(x.len(), 16);
                let costumes = match &x[0] {
                    Value::List(x) => {
                        let x = x.read();
                        assert_eq!(x.len(), 5);
                        x.iter().map(|x| match x {
                            Value::Image(x) => x.clone(),
                            x => panic!("{x:?}"),
                        }).collect::<Vec<_>>()
                    }
                    x => panic!("{x:?}"),
                };
                let costume_set = costumes.iter().map(Rc::as_ptr).collect::<BTreeSet<_>>();
                assert_eq!(costume_set.len(), 5);

                let chart = match &x[9] {
                    Value::List(x) => match &x.read()[0] {
                        Value::Image(x) => x.clone(),
                        x => panic!("{x:?}"),
                    }
                    Value::Image(x) => x.clone(),
                    x => panic!("{x:?}"),
                };
                assert!(!costume_set.contains(&Rc::as_ptr(&chart)));

                for idx in [1, 6, 14] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &costumes[1])),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 2.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [2, 7, 8, 15] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::String(x) => assert_eq!(x.as_str(), ""),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 0.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [3] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &costumes[3])),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 4.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [4, 11] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &costumes[4])),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 5.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [5, 12] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &costumes[0])),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 1.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [9, 10] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &chart)),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 0.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
                for idx in [13] {
                    match &x[idx] {
                        Value::List(x) => {
                            let x = x.read();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Image(x) => assert!(Rc::ptr_eq(x, &costumes[2])),
                                x => panic!("{x:?}"),
                            }
                            match &x[1] {
                                Value::Number(x) => assert_eq!(x.get(), 3.0),
                                x => panic!("{x:?}"),
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
            }
            x => panic!("{x:?}"),
        }
    });
}

#[test]
fn test_proj_broadcast() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/broadcast.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get().clone(), &Number::new(320.0).unwrap().into(), 1e-20, "counter");
        let expected = Value::from_json(mc, json!([
            "before 1",
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
            "after 1",
            70, 80, 90, 100, 110, 120, 130, 140, 150, 160,
            "before 2",
            "after 2",
            170, 171, 173, 176, 186, 187, 189, 192, 202, 203, 205, 208, 218, 219, 221, 224, 234, 235, 237, 240, 250, 251, 253, 256, 266, 267, 269, 272, 282, 283, 285, 288, 298, 299, 301, 304, 314, 315, 317, 320,
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_loop_yields() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/loop-yields.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get().clone(), &Number::new(150.0).unwrap().into(), 1e-20, "counter");
        let expected = Value::from_json(mc, json!([
            1, 3, 6, 10, 15, 16, 18, 21, 25, 30, 31, 33, 36, 40, 45, 46, 48, 51, 55, 60, 61, 63, 66, 70, 75,
            76, 78, 81, 85, 90, 91, 93, 96, 100, 105, 106, 108, 111, 115, 120, 121, 123, 126, 130, 135, 136, 138, 141, 145, 150
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("history").unwrap().get().clone(), &expected, 1e-20, "history");
    });
}

#[test]
fn test_proj_parallel_rpcs() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/parallel-rpcs.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        assert_eq!(global_context.globals.lookup("input").unwrap().get().as_list().unwrap().read().len(), 0);

        let meta: Vec<_> = global_context.globals.lookup("meta").unwrap().get().as_list().unwrap().read().iter().map(|x| x.to_number().unwrap()).collect();
        if meta.len() != 4 || meta.iter().map(|x| x.get()).sum::<f64>() != 216.0 || !meta.iter().all(|&x| x.get() >= 30.0) {
            panic!("{meta:?}");
        }

        let mut output: Vec<_> = global_context.globals.lookup("output").unwrap().get().as_list().unwrap().read().iter().map(|row| {
            let vals: Vec<_> = row.as_list().unwrap().read().iter().map(|x| {
                let v = x.to_number().unwrap().get();
                assert_eq!(v as i64 as f64, v);
                v as i64
            }).collect();
            assert_eq!(vals.len(), 4);
            (vals[0], vals[1], vals[2], vals[3])
        }).collect();
        output.sort();
        assert_eq!(output.len(), 216);
        let mut res = output.iter().copied();
        for r in 1..=6u32 {
            for g in 1..=6u32 {
                for b in 1..=6u32 {
                    let encoded = ((0xff << 24) | (r << 16) | (g << 8) | b) as i32 as i64;
                    let vals = res.next().unwrap();
                    if vals.0 != r as i64 || vals.1 != g as i64 || vals.2 != b as i64 || vals.3 != encoded {
                        panic!("got {vals:?} - expected {:?}", (r, g, b, encoded));
                    }
                }
            }
        }
    });
}

#[test]
fn test_proj_wait_until() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/wait-until.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        assert_values_eq(&global_context.globals.lookup("mark").unwrap().get(), &Value::from_json(mc, json!(64)).unwrap(), 1e-20, "after wait value");
        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &Value::from_json(mc, json!(128)).unwrap(), 1e-20, "final counter value");
    });
}
