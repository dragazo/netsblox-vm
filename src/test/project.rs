use std::prelude::v1::*;

use netsblox_ast as ast;

use crate::*;
use crate::gc::*;
use crate::runtime::*;
use crate::process::*;
use crate::project::*;

use super::assert_values_eq;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proj: GcCell<'gc, Project<'gc, StdSystem>>,
}
make_arena!(EnvArena, Env);

fn get_running_project(xml: &str) -> EnvArena {
    EnvArena::new(Default::default(), |mc| {
        let parser = ast::ParserBuilder::default().build().unwrap();
        let ast = parser.parse(xml).unwrap();
        assert_eq!(ast.roles.len(), 1);

        let settings = SettingsBuilder::default().build().unwrap();
        let mut proj = Project::from_ast(mc, &ast.roles[0], settings);
        proj.input(Input::Start);
        Env { proj: GcCell::allocate(mc, proj) }
    })
}

fn run_till_term<'gc>(mc: MutationContext<'gc, '_>, proj: &mut Project<'gc, StdSystem>) {
    let mut system = StdSystem::new();
    loop {
        match proj.step(mc, &mut system) {
            ProjectStep::Idle => return,
            ProjectStep::Normal => (),
        }
    }
}

#[test]
fn test_proj_counting() {
    let mut proj = get_running_project(include_str!("projects/counting.xml"));
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc));
        let global_context = proj.proj.read().global_context();
        let global_context = global_context.read();

        let expected = Value::from_simple(mc, simple_value!([
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
        ]));
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res");
        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &60.0.into(), 1e-20, "counter");
    });
}

#[test]
fn test_proj_broadcast() {
    let mut proj = get_running_project(include_str!("projects/broadcast.xml"));
    proj.mutate(|mc, proj| {
        run_till_term(mc, &mut *proj.proj.write(mc));
        let global_context = proj.proj.read().global_context();
        let global_context = global_context.read();

        assert_values_eq(&global_context.globals.lookup("counter").unwrap().get(), &320.0.into(), 1e-20, "counter");
        let expected = Value::from_simple(mc, simple_value!([
            "before 1",
            1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
            "after 1",
            70, 80, 90, 100, 110, 120, 130, 140, 150, 160,
            "before 2",
            "after 2",
            170, 171, 173, 176, 186, 187, 189, 192, 202, 203, 205, 208, 218, 219, 221, 224, 234, 235, 237, 240, 250, 251, 253, 256, 266, 267, 269, 272, 282, 283, 285, 288, 298, 299, 301, 304, 314, 315, 317, 320,
        ]));
        assert_values_eq(&global_context.globals.lookup("res").unwrap().get(), &expected, 1e-20, "res")
    });
}