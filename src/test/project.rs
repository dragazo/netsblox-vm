use alloc::collections::BTreeSet;
use alloc::rc::Rc;
use alloc::sync::Arc;
use core::cell::RefCell;

use crate::*;
use crate::gc::*;
use crate::json::*;
use crate::real_time::*;
use crate::bytecode::*;
use crate::project::*;
use crate::std_system::*;
use crate::compact_str::CompactString;

use super::*;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proj: Gc<'gc, RefLock<Project<'gc, C, StdSystem<C>>>>,
}
type EnvArena = Arena<Rootable![Env<'_>]>;

fn get_running_project(xml: &str, system: Rc<StdSystem<C>>) -> EnvArena {
    EnvArena::new(|mc| {
        let parser = ast::Parser::default();
        let ast = parser.parse(xml).unwrap();
        assert_eq!(ast.roles.len(), 1);

        let (bytecode, init_info, _, _) = ByteCode::compile(&ast.roles[0]).unwrap();

        let mut proj = Project::from_init(mc, &init_info, Rc::new(bytecode), Settings::default(), system);
        proj.input(mc, Input::Start);
        Env { proj: Gc::new(mc, RefLock::new(proj)) }
    })
}

#[derive(Educe)]
#[educe(Debug)]
enum SpecialEvent<'gc, C: CustomTypes<S>, S: System<C>> {
    Watcher { create: bool, watcher: Watcher<'gc, C, S> },
    Pause,
}

fn run_till_term<'gc>(mc: &Mutation<'gc>, proj: &mut Project<'gc, C, StdSystem<C>>) -> Result<Vec<SpecialEvent<'gc, C, StdSystem<C>>>, ExecError<C, StdSystem<C>>> {
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
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/counting.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &Number::new(60.0).unwrap().into(), 1e-20, "counter");
    });
}

#[test]
fn test_proj_effects() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/effects.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            [0, 0, 0, 0, 0, 0, 0, 0, 0],
            [12, 47, 32, 14, 11, -37, 123, 65, 74],
            [54, 79, 87, 7, 23, 37, 168, 66, -6],
            [350, 0, 0, 0, 23, 37, 168, 66, -6],
            [40, 100, 100, 100, 23, 37, 168, 66, -6],
            [120, 0, 0, 0, 23, 37, 168, 66, -6],
            [301, 100, 100, 100, 23, 37, 168, 66, -6],
            [0, 0, 0, 0, 0, 0, 0, 0, 0],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_size_visible() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/size-visible.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_motion() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/motion.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_pen_basic() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/pen-basic.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_watchers() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/watchers.xml"), system);
    proj.mutate(|mc, proj| {
        let events = run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();

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
fn test_proj_stop_current() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/stop-current.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["2", 1],
            ["3", 1],
            ["4", 1],
            ["1", 2],
            ["2", 2],
            ["3", 2],
            ["4", 2],
            ["1", 3],
            ["2", 3],
            ["3", 3],
            ["1", 4],
            ["3", 4],
            ["1", 5],
            ["3", 5],
            ["1", 6],
            ["3", 6],
            ["1", 7],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_stop_all() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/stop-all.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["2", 1],
            ["3", 1],
            ["4", 1],
            ["5", 1],
            ["6", 1],
            ["7", 1],
            ["8", 1],
            ["1", 2],
            ["2", 2],
            ["3", 2],
            ["4", 2],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_stop_others() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/stop-others.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["2", 1],
            ["3", 1],
            ["4", 1],
            ["5", 1],
            ["6", 1],
            ["7", 1],
            ["8", 1],
            ["1", 2],
            ["2", 2],
            ["3", 2],
            ["4", 2],
            ["4", 3],
            ["4", 4],
            ["4", 5],
            ["4", 6],
            ["4", 7],
            ["4", 8],
            ["4", 9],
            ["4", 10],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_stop_my_others() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/stop-my-others.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["2", 1],
            ["3", 1],
            ["4", 1],
            ["5", 1],
            ["6", 1],
            ["7", 1],
            ["8", 1],
            ["1", 2],
            ["2", 2],
            ["3", 2],
            ["4", 2],
            ["5", 2],
            ["6", 2],
            ["7", 2],
            ["8", 2],
            ["4", 3],
            ["5", 3],
            ["6", 3],
            ["7", 3],
            ["8", 3],
            ["4", 4],
            ["5", 4],
            ["6", 4],
            ["4", 5],
            ["6", 5],
            ["4", 6],
            ["6", 6],
            ["4", 7],
            ["6", 7],
            ["4", 8],
            ["6", 8],
            ["4", 9],
            ["6", 9],
            ["4", 10],
            ["6", 10],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_stop_my_others_context() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/stop-my-others-context.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["1", 1],
            ["2", 1],
            ["3", 1],
            ["4", 1],
            ["1", 2],
            ["2", 2],
            ["3", 2],
            ["4", 2],
            ["1", 3],
            ["2", 3],
            ["1", 4],
            ["2", 4],
            ["1", 5],
            ["2", 5],
            ["1", 6],
            ["2", 6],
            ["1", 7],
            ["2", 7],
            ["1", 8],
            ["2", 8],
            ["1", 9],
            ["2", 9],
            ["1", 10],
            ["2", 10],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_delete_clone() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/delete-clone.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            "---",
            "---",
            [1, "1", 1],
            [1, "2", 1],
            [1, "1", 2],
            [1, "2", 2],
            [1, "1", 3],
            [1, "2", 3],
            [1, "1", 4],
            [1, "2", 4],
            [1, "1", 5],
            [1, "2", 5],
            [1, "1", 6],
            "---",
            "+++",
            "+++",
            "+++",
            "---",
            [2, "1", 1],
            [2, "2", 1],
            "---",
            [3, "1", 1],
            [3, "2", 1],
            [3, "1", 2],
            [3, "2", 2],
            "---",
            [4, "1", 1],
            [4, "2", 1],
            [4, "1", 2],
            [4, "2", 2],
            [4, "1", 3],
            [4, "2", 3],
            "---",
            "AHHH!!!",
            "---",
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("log").unwrap().get(), &expected, 1e-10, "log");
    });
}

#[test]
fn test_proj_costume_names() {
    let config = Config::<C, StdSystem<C>> {
        command: Some(Rc::new(|_, key, command, _| match command {
            Command::SetCostume => {
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            _ => CommandStatus::UseDefault { key, command },
        })),
        request: None,
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/costume-names.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            0,
            "",
            "",
            "",
            "IndexOutOfBounds { index: 0, len: 3 }",
            ["squiggle", "squiggle", "squiggle", "squiggle", "squiggle", 1, "squiggle", "squiggle"],
            ["zap", "zap", "zap", "zap", "zap", 3, "zap", "zap"],
            ["zip", "zip", "zip", "zip", "zip", 2, "zip", "zip"],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-10, "res");
    });
}

#[test]
fn test_proj_sound_names() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/sound-names.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["boop", "boop", "boop", "boop"],
            ["bop", "bop", "bop", "bop"],
            ["swoop", "swoop", "swoop", "swoop"],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("gtf").unwrap().get(), &expected, 1e-10, "gtf");
    });
}

#[test]
fn test_proj_sounds() {
    let sound_events = Rc::new(RefCell::new(vec![]));
    let sound_events_clone = sound_events.clone();
    let config = Config::<C, StdSystem<C>> {
        request: None,
        command: Some(Rc::new(move |_, key, command, _| match command {
            Command::StopSounds => {
                sound_events_clone.borrow_mut().push(None);
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            Command::PlaySound { sound, blocking } => {
                sound_events_clone.borrow_mut().push(Some((sound, blocking)));
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            _ => CommandStatus::UseDefault { key, command },
        })),
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/sounds.xml"), system);

    let expect_prefixes = [
        [82, 73, 70, 70, 212, 28, 0, 0].as_slice(),
        [73, 68, 51, 3, 0, 0, 0, 0].as_slice(),
        [82, 73, 70, 70, 40, 2, 0, 0].as_slice(),
    ];

    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let res = global_context.globals.lookup("res").unwrap().get().clone();
        match &res {
            Value::List(x) => {
                let x = &*x.borrow();
                assert_eq!(x.len(), 3);
                for (i, v) in x.iter().enumerate() {
                    match v {
                        Value::Audio(sound) => {
                            if !sound.content.starts_with(expect_prefixes[i]) {
                                panic!("{i}: {:?}", sound.content);
                            }
                        }
                        x => panic!("{x:?}"),
                    }
                }
            }
            x => panic!("{x:?}"),
        }
    });

    let sound_events = &*sound_events.borrow();
    assert_eq!(sound_events.len(), 27);

    assert!(sound_events[0].is_none());

    assert!(sound_events[1].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && !sound_events[1].as_ref().unwrap().1);
    assert!(sound_events[2].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && !sound_events[2].as_ref().unwrap().1);
    assert!(sound_events[3].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && !sound_events[3].as_ref().unwrap().1);

    assert!(sound_events[4].is_none());

    assert!(sound_events[5].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && sound_events[5].as_ref().unwrap().1);
    assert!(sound_events[6].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && sound_events[6].as_ref().unwrap().1);
    assert!(sound_events[7].is_none());
    assert!(sound_events[8].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && sound_events[8].as_ref().unwrap().1);

    assert!(sound_events[9].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && !sound_events[9].as_ref().unwrap().1);
    assert!(sound_events[10].is_none());
    assert!(sound_events[11].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && sound_events[11].as_ref().unwrap().1);

    assert!(sound_events[12].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && !sound_events[12].as_ref().unwrap().1);
    assert!(sound_events[13].is_none());
    assert!(sound_events[14].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && sound_events[14].as_ref().unwrap().1);

    assert!(sound_events[15].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && !sound_events[15].as_ref().unwrap().1);
    assert!(sound_events[16].is_none());
    assert!(sound_events[17].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && sound_events[17].as_ref().unwrap().1);

    assert!(sound_events[18].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && !sound_events[18].as_ref().unwrap().1);
    assert!(sound_events[19].is_none());
    assert!(sound_events[20].is_none());
    assert!(sound_events[21].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && !sound_events[21].as_ref().unwrap().1);
    assert!(sound_events[22].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && !sound_events[22].as_ref().unwrap().1);

    assert!(sound_events[23].as_ref().unwrap().0.content.starts_with(expect_prefixes[1]) && sound_events[26].as_ref().unwrap().1);
    assert!(sound_events[24].as_ref().unwrap().0.content.starts_with(expect_prefixes[0]) && sound_events[24].as_ref().unwrap().1);
    assert!(sound_events[25].is_none());
    assert!(sound_events[26].as_ref().unwrap().0.content.starts_with(expect_prefixes[2]) && sound_events[26].as_ref().unwrap().1);
}

#[test]
fn test_proj_costumes() {
    let config = Config::<C, StdSystem<C>> {
        request: None,
        command: Some(Rc::new(move |_, key, command, _| match command {
            Command::SetCostume => {
                key.complete(Ok(()));
                CommandStatus::Handled
            }
            _ => CommandStatus::UseDefault { key, command },
        })),
    };
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, config, Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/costumes.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let res = global_context.globals.lookup("res").unwrap().get().clone();
        match &res {
            Value::List(x) => {
                let x = x.borrow();
                assert_eq!(x.len(), 16);
                let costumes = match &x[0] {
                    Value::List(x) => {
                        let x = x.borrow();
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
                    Value::List(x) => match &x.borrow()[0] {
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
                            let x = x.borrow();
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
                            let x = x.borrow();
                            assert_eq!(x.len(), 2);
                            match &x[0] {
                                Value::Text(x) => assert_eq!(x.as_str(), ""),
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
                            let x = x.borrow();
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
                            let x = x.borrow();
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
                            let x = x.borrow();
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
                            let x = x.borrow();
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
                            let x = x.borrow();
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
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/broadcast.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get().clone(), &Number::new(320.0).unwrap().into(), 1e-20, "counter");
        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            "before 1",
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
            "after 1",
            70, 80, 90, 100, 110, 120, 130, 140, 150, 160,
            "before 2",
            "after 2",
            170, 171, 173, 176, 186, 187, 189, 192, 202, 203, 205, 208, 218, 219, 221, 224, 234, 235, 237, 240, 250, 251, 253, 256, 266, 267, 269, 272, 282, 283, 285, 288, 298, 299, 301, 304, 314, 315, 317, 320,
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_delayed_capture_upvar() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/delayed-capture-upvar.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["test 1", 13],
            ["test 1", 13],
            ["test 1", 13],
            ["test 2", 13],
            ["test 2", 13],
            ["test 2", 13],
            ["test 3", 13],
            ["test 3", 13],
            ["test 3", 13],
            ["tracking 4", 0],
            ["tracking 4", 0],
            ["tracking 4", 0],
            ["test 4", 11],
            ["test 4", 12],
            ["test 4", 13],
            ["tracking 5", 0],
            ["tracking 5", 0],
            ["tracking 5", 0],
            ["test 5", 11],
            ["test 5", 12],
            ["test 5", 13],
            ["tracking 6", 0],
            ["tracking 6", 0],
            ["tracking 6", 0],
            ["test 6", 11],
            ["test 6", 12],
            ["test 6", 13],
            ["test 7", 11],
            ["test 7", 12],
            ["test 7", 13],
            ["test 8", 11],
            ["test 8", 12],
            ["test 8", 13],
            ["test 9", 11],
            ["test 9", 12],
            ["test 9", 13],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_broadcast_to() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/broadcast-to.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("log").unwrap().get().clone(), &expected, 1e-20, "log");
    });
}

#[test]
fn test_proj_messaging() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/messaging.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            25,
            [49, 121, 169],
            [49, [256, 16], 169],
            [9, 4],
            ["2", 5, 9],
            ["2", 6, 24],
            ["2", [3, 4], [7, 8]],
            ["2", [2, 4], [8, 16]],
            [["6", "3"], [7, 5], [11, 9]],
            [["6", "3"], [6, 6], [24, 24]],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_any_msg() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/any-msg.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("log").unwrap().get().clone(), &expected, 1e-20, "log");
    });
}

#[test]
fn test_proj_launch() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/launch.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["start", 0],
            ["run", 0.05],
            ["run", 0.1],
            ["run", 0.15],
            ["run", 0.2],
            ["run", 0.25],
            ["run", 0.3],
            ["run", 0.35],
            ["run", 0.4],
            ["run", 0.45],
            ["run", 0.5],
            ["mid", 0.5],
            ["done", 0.5],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
            ["launch", 0.55],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 0.005, "res");
    });
}

#[test]
fn test_proj_cloning() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/cloning.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            "0", 1, 2, 3, 4, 5, 6, 7, 8,
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("foo").unwrap().get().clone(), &expected, 0.005, "foo");
    });
}

#[test]
fn test_proj_pause() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/pause.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!("5")).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 1e-20, "res");
    });
}

#[test]
fn test_proj_loop_yields() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/loop-yields.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get().clone(), &Number::new(150.0).unwrap().into(), 1e-20, "counter");
        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            1, 3, 6, 10, 15, 16, 18, 21, 25, 30, 31, 33, 36, 40, 45, 46, 48, 51, 55, 60, 61, 63, 66, 70, 75,
            76, 78, 81, 85, 90, 91, 93, 96, 100, 105, 106, 108, 111, 115, 120, 121, 123, 126, 130, 135, 136, 138, 141, 145, 150
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("history").unwrap().get().clone(), &expected, 1e-20, "history");
    });
}

#[test]
fn test_proj_run_call_ask_tell() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/run-call-ask-tell.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
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
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 0.1, "res");
    });
}

#[test]
fn test_proj_custom_events() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, default_properties_config(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/custom-events.xml"), system);
    proj.mutate(|mc, proj| {
        let mut proj = proj.proj.borrow_mut(mc);
        proj.input(mc, Input::CustomEvent { name: "receiveTest1".into(), args: Default::default(), interrupt: false, max_queue: usize::MAX });
        proj.input(mc, Input::CustomEvent { name: "receiveTest1".into(), args: Default::default(), interrupt: false, max_queue: usize::MAX });
        proj.input(mc, Input::CustomEvent { name: "receiveTest1".into(), args: Default::default(), interrupt: false, max_queue: usize::MAX });
        proj.input(mc, Input::CustomEvent { name: "receiveTest3".into(), args: vec![(CompactString::new("val"), Number::new(34.0).unwrap().into()), (CompactString::new("derp"), Number::new(12.0).unwrap().into())].into_iter().collect(), interrupt: false, max_queue: 0 });
        proj.input(mc, Input::CustomEvent { name: "receiveTest3".into(), args: vec![(CompactString::new("val"), Number::new(420.0).unwrap().into()), (CompactString::new("derp"), Number::new(69.0).unwrap().into())].into_iter().collect(), interrupt: false, max_queue: 0 });
        proj.input(mc, Input::CustomEvent { name: "receiveTest2".into(), args: vec![(CompactString::new("merp"), CompactString::new("hello world").into())].into_iter().collect(), interrupt: true, max_queue: 0 });
        proj.input(mc, Input::CustomEvent { name: "receiveTest2".into(), args: vec![(CompactString::new("merp"), CompactString::new("goodbye world").into())].into_iter().collect(), interrupt: true, max_queue: 0 });
        run_till_term(mc, &mut *proj).unwrap();
        let global_context = proj.get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([
            ["here 1"],
            ["here 2"],
            ["here 5", 34, 12, 22],
            ["here 6", 34, 12, 3412],
            ["here 3", "goodbye world", "goodbye worldgoodbye world"],
            ["here 4", "goodbye world", "goodbye world-goodbye world"],
            ["here 1"],
            ["here 2"],
            ["here 1"],
            ["here 2"],
        ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get().clone(), &expected, 0.1, "res");
    });
}

#[test]
fn test_proj_parallel_rpcs() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/parallel-rpcs.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        assert_eq!(global_context.globals.lookup("input").unwrap().get().as_list().unwrap().borrow().len(), 0);

        let meta: Vec<_> = global_context.globals.lookup("meta").unwrap().get().as_list().unwrap().borrow().iter().map(|x| x.as_number().unwrap()).collect();
        if meta.len() != 4 || meta.iter().map(|x| x.get()).sum::<f64>() != 216.0 || !meta.iter().all(|&x| x.get() >= 30.0) {
            panic!("{meta:?}");
        }

        let mut output: Vec<_> = global_context.globals.lookup("output").unwrap().get().as_list().unwrap().borrow().iter().map(|row| {
            let vals: Vec<_> = row.as_list().unwrap().borrow().iter().map(|x| {
                let v = x.as_number().unwrap().get();
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
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/wait-until.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        assert_values_eq(&global_context.globals.lookup("mark").unwrap().get(), &Value::from_simple(mc, SimpleValue::from_json(json!(64)).unwrap()), 1e-20, "after wait value");
        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &Value::from_simple(mc, SimpleValue::from_json(json!(128)).unwrap()), 1e-20, "final counter value");
    });
}

#[test]
fn test_proj_nested_lists_consts() {
    let system = Rc::new(StdSystem::new_sync(CompactString::new(BASE_URL), None, Config::default(), Arc::new(Clock::new(UtcOffset::UTC, None))));
    let proj = get_running_project(include_str!("projects/nested-lists-consts.xml"), system);
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.borrow_mut(mc)).unwrap();
        let global_context = proj.proj.borrow().get_global_context();
        let global_context = global_context.borrow();

        let expected = Value::from_simple(mc, SimpleValue::from_json(json!([ "a", "b", ["c", "d", ["e", "f", "g"], "h"], "i", "j" ])).unwrap());
        assert_values_eq(&global_context.globals.lookup("abc").unwrap().get(), &expected, 1e-20, "nested lists consts");
    });
}

#[test]
fn test_proj_sizes() {
    fn bytecode_size(xml: &str) -> usize {
        let role = &ast::Parser::default().parse(xml).unwrap().roles[0];
        ByteCode::compile(role).unwrap().0.total_size()
    }

    let mut good = true;
    macro_rules! check_bytecode_size {
        ($path:literal, $expected:literal) => {{
            let got = bytecode_size(include_str!($path));
            let expected = $expected;
            if got != expected {
                println!("{} got {} expected {}", $path, got, expected);
                good = false;
            }
        }}
    }

    check_bytecode_size!("projects/any-msg.xml", 390);
    check_bytecode_size!("projects/broadcast-to.xml", 379);
    check_bytecode_size!("projects/broadcast.xml", 239);
    check_bytecode_size!("projects/cloning.xml", 86);
    check_bytecode_size!("projects/costumes.xml", 280);
    check_bytecode_size!("projects/counting.xml", 97);
    check_bytecode_size!("projects/custom-events.xml", 180);
    check_bytecode_size!("projects/delayed-capture-upvar.xml", 808);
    check_bytecode_size!("projects/delete-clone.xml", 438);
    check_bytecode_size!("projects/effects.xml", 236);
    check_bytecode_size!("projects/launch.xml", 150);
    check_bytecode_size!("projects/loop-yields.xml", 218);
    check_bytecode_size!("projects/messaging.xml", 387);
    check_bytecode_size!("projects/motion.xml", 230);
    check_bytecode_size!("projects/nested-lists-consts.xml", 0);
    check_bytecode_size!("projects/parallel-rpcs.xml", 420);
    check_bytecode_size!("projects/pause.xml", 16);
    check_bytecode_size!("projects/pen-basic.xml", 336);
    check_bytecode_size!("projects/run-call-ask-tell.xml", 334);
    check_bytecode_size!("projects/size-visible.xml", 96);
    check_bytecode_size!("projects/stop-all.xml", 688);
    check_bytecode_size!("projects/stop-current.xml", 349);
    check_bytecode_size!("projects/stop-my-others-context.xml", 372);
    check_bytecode_size!("projects/stop-my-others.xml", 691);
    check_bytecode_size!("projects/stop-others.xml", 688);
    check_bytecode_size!("projects/wait-until.xml", 72);
    check_bytecode_size!("projects/watchers.xml", 58);

    assert!(good);
}