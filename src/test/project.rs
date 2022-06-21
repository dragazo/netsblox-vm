use std::prelude::v1::*;

use netsblox_ast as ast;

use crate::runtime::*;
use crate::process::*;
use crate::project::*;

use super::assert_values_eq;

fn get_running_project(xml: &str) -> Project<StdSystem> {
    let parser = ast::ParserBuilder::default().build().unwrap();
    let ast = parser.parse(xml).unwrap();
    assert_eq!(ast.roles.len(), 1);

    let settings = SettingsBuilder::default().build().unwrap();
    let mut proj = Project::from_ast(&ast.roles[0], settings);
    proj.input(Input::Start);
    proj
}

fn run_till_term(project: &mut Project<StdSystem>) {
    let mut system = StdSystem::new();
    loop {
        match project.step(&mut system) {
            ProjectStep::Idle => return,
            ProjectStep::Normal => (),
        }
    }
}

#[test]
fn test_proj_counting() {
    let mut project = get_running_project(include_str!("projects/counting.xml"));
    run_till_term(&mut project);
    let runtime = project.runtime_mut();

    assert_values_eq(&runtime.globals.lookup("counter").unwrap().get_clone(), &60.0.into(), 1e-20, "counter");

    let expected = Value::from_vec([
        1, 3, 6, 7, 9, 12, 13, 15, 18, 19, 21, 24, 25, 27, 30, 31, 33, 36, 37, 39, 42, 43, 45, 48, 49, 51, 54, 55, 57, 60,
    ].into_iter().map(|x| (x as f64).into()).collect(), &mut runtime.ref_pool);
    assert_values_eq(&runtime.globals.lookup("res").unwrap().get_clone(), &expected, 1e-20, "res")
}
