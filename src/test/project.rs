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

#[derive(Educe)]
#[educe(Debug)]
enum SpecialEvent<'gc, C: CustomTypes<S>, S: System<C>> {
    Watcher { create: bool, watcher: Watcher<'gc, C, S> },
    Pause,
}

fn run_till_term<'gc>(mc: MutationContext<'gc, '_>, proj: &mut Project<'gc, C, StdSystem<C>>) -> Result<Vec<SpecialEvent<'gc, C, StdSystem<C>>>, ExecError<C, StdSystem<C>>> {
    let mut special_events = vec![];
    loop {
        match proj.step(mc) {
            ProjectStep::Idle => return Ok(special_events),
            ProjectStep::Error { error, .. } => return Err(error),
            ProjectStep::Normal | ProjectStep::ProcessTerminated { .. } | ProjectStep::Yield => (),
            ProjectStep::Watcher { create, watcher } => special_events.push(SpecialEvent::Watcher { create, watcher }),
            ProjectStep::Pause => {
                special_events.push(SpecialEvent::Pause);
                return Ok(special_events); // simulate actually pausing
            }
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
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
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
fn test_proj_size_visible() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
    let proj = get_running_project(include_str!("projects/size-visible.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            [81, false],
            [44, false],
            [44, true],
            [44, true],
            [44, false],
            [44, false],
            [115, false],
            [196, false],
            [0, false],
            [15, false],
            [0, false],
            [4, false],
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_motion() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
    let proj = get_running_project(include_str!("projects/motion.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            [-42, 67, 287],
            [-48.69413329174131, 69.04660193305915, 287],
            [-48.69413329174131, 69.04660193305915, 307],
            [-48.69413329174131, 69.04660193305915, 227],
            [17.859053555603275, 131.10845269874653, 227],
            [17.859053555603275, 131.10845269874653, 33],
            [17.859053555603275, 131.10845269874653, 93],
            [29.842607972658175, 130.48042122383123, 93],
            [-0.11627806997899777, 132.0504999111196, 93],
            [-0.11627806997899777, 132.0504999111196, 42],
            [-75, 63, 42],
            [-54, 63, 42],
            [-57, 63, 42],
            [78, 63, 42],
            [-13, 63, 42],
            [-13, 161, 42],
            [-13, 146, 42],
            [-13, -64, 42],
            [-13, 2, 42],
            [-13, 2, 245],
            [-13, 2, 8],
            [-13, 2, 98.74616226255522],
            [-13, 2, 110.74616226255603],
            [0, 0, 110.74616226255603],
            [31, -120, 110.74616226255603],
            [31, -120, 355.7636052009412],
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_pen_basic() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
    let proj = get_running_project(include_str!("projects/pen-basic.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            [1, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, false],
            [1, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, false],
            [1, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, false],
            [1, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [1, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [0, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [17, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [20, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [12, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [0, 187.1287078857422, 79.21568751335144, 100, 71.37254774570465, true],
            [0, 29.473684310913086, 100, 89.41176533699036, 0, true],
            [0, 299.2592468261719, 63.52940797805786, 100, 0, true],
            [0, 230.39999389648438, 100, 49.01960790157318, 0, true],
            [0, 240.39999389648438, 100, 49.01960790157318, 0, true],
            [0, 219.39999389648438, 100, 49.01960790157318, 0, true],
            [0, 140.39999389648438, 100, 49.01960790157318, 0, true],
            [0, 328.3999938964844, 100, 49.01960790157318, 0, true],
            [0, 73, 100, 49.01960790157318, 0, true],
            [0, 29, 100, 49.01960790157318, 0, true],
            [0, 345, 100, 49.01960790157318, 0, true],
            [0, 345, 100, 49.01960790157318, 0, true],
            [0, 345, 91, 49.01960790157318, 0, true],
            [0, 345, 0, 49.01960790157318, 0, true],
            [0, 345, 100, 49.01960790157318, 0, true],
            [0, 345, 35, 49.01960790157318, 0, true],
            [0, 345, 100, 49.01960790157318, 0, true],
            [0, 345, 0, 49.01960790157318, 0, true],
            [0, 345, 0, 61.01960790157318, 0, true],
            [0, 345, 0, 43.01960790157318, 0, true],
            [0, 345, 0, 100, 0, true],
            [0, 345, 0, 0, 0, true],
            [0, 345, 0, 61, 0, true],
            [0, 345, 0, 100, 0, true],
            [0, 345, 0, 0, 0, true],
            [0, 345, 0, 0, 7, true],
            [0, 345, 0, 0, 0, true],
            [0, 345, 0, 0, 100, true],
            [0, 345, 0, 0, 0, true],
            [0, 345, 0, 0, 27, true],
            [0, 345, 0, 0, 100, true],
            [0, 345, 0, 0, 0, true],
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_watchers() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
    let proj = get_running_project(include_str!("projects/watchers.xml"), system);
    proj.mutate(|mc, proj| {
        let events = run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();

        let mapped = events.iter().map(|x| match x {
            SpecialEvent::Watcher { create, watcher } => (*create, watcher.name.as_str()),
            _ => panic!("{x:?}"),
        }).collect::<Vec<_>>();

        let expected = [
            (true, "my global"),
            (true, "my field"),
            (false, "my global"),
            (false, "my local"),
            (false, "my local"),
            (true, "my local"),
            (false, "my field"),
        ];

        assert_eq!(mapped, expected);
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
fn test_proj_broadcast_to() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/broadcast-to.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            "stage 1", "stage 2", "turtle 1", "turtle 2", "duck 1", "duck 2", "dog 1", "dog 2", "---",
            "stage 1", "stage 2", "turtle 1", "turtle 2", "duck 1", "duck 2", "dog 1", "dog 2", "---",
            "duck 1", "duck 2", "---",
            "dog 1", "dog 2", "---",
            "stage 1", "stage 2", "---",
            "turtle 1", "turtle 2", "---",
            "duck 1", "duck 2", "---",
            "---",
            "dog 1", "dog 2", "---",
            "turtle 1", "turtle 2", "duck 1", "duck 2", "---",
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("log").unwrap().get().clone(), &expected, 1e-20, "log");
    });
}

#[test]
fn test_proj_any_msg() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/any-msg.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            ["initial", ""],
            ["dog msg 1", "msg 1"],
            ["dog any", "msg 1"],
            ["cat msg 1", "msg 1"],
            ["cat any", "msg 1"],
            ["horse msg 1", "msg 1"],
            ["horse any", "msg 1"],
            "---",
            ["dog msg 2", "msg 2"],
            ["dog any", "msg 2"],
            ["cat msg 2", "msg 2"],
            ["cat any", "msg 2"],
            ["horse msg 2", "msg 2"],
            ["horse any", "msg 2"],
            "---",
            ["dog any", "msg 3"],
            ["cat any", "msg 3"],
            ["horse any", "msg 3"],
            "---",
            ["cat msg 1", "msg 1"],
            ["cat any", "msg 1"],
            "---",
            ["dog msg 2", "msg 2"],
            ["dog any", "msg 2"],
            "---",
            ["horse any", "msg 3"],
            "---",
            ["dog any", "msg 3"],
            ["horse any", "msg 3"],
            "---",
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("log").unwrap().get().clone(), &expected, 1e-20, "log");
    });
}

#[test]
fn test_proj_pause() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, Config::default()));
    let proj = get_running_project(include_str!("projects/pause.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!("5")).unwrap();
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
fn test_proj_run_call_ask_tell() {
    let system = Rc::new(StdSystem::new(BASE_URL.to_owned(), None, default_properties_config()));
    let proj = get_running_project(include_str!("projects/run-call-ask-tell.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc)).unwrap();
        let global_context = proj.proj.read().get_global_context();
        let global_context = global_context.read();

        let expected = Value::from_json(mc, json!([
            [0.0, [87, 25, 10], [74, 65, 14], [45, 25, 201]],
            [0.1, [87, 25, 10], [74, 65, 14], [45, 25, 201]],
            [0.2, [87, 25, 10], [74, 65, 14], [45, 25, 201]],
            "24",
            [0.3, [87, 25, 10], [74, 65, 14], [45, 25, 201]],
            "17",
            [0.4, [87, 25, 10], [74, 65, 14], [45, 25, 201]],
            [0.4, [17, -95, 23], [74, 65, 14], [45, 25, 201]],
            [0.4, [17, -95, 23], [41, 35, 65], [45, 25, 201]],
            [0.4, [17, -95, 23], [41, 35, 65], [-108, 105, 356]],
        ])).unwrap();
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 0.1, "res");
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
