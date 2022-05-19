use std::prelude::v1::*;
use std::rc::Rc;

use netsblox_ast as ast;

use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;

fn get_running_proc(xml: &str, locals: SymbolTable, ref_pool: &mut RefPool) -> (Process, SymbolTable, SymbolTable) {
    let parser = ast::ParserBuilder::default().build().unwrap();
    let ast = parser.parse(xml).unwrap();
    let (code, locs) = ByteCode::compile(&ast.roles[0]);
    let mut proc = Process::new(Rc::new(code), 1024);
    assert!(!proc.is_running());

    let main = locs.funcs.iter().find(|x| x.0.trans_name == "main").expect("no main function at global scope");
    proc.initialize(main.1, locals);
    assert!(proc.is_running());

    let globals = SymbolTable::from_globals(&ast.roles[0], ref_pool);
    let fields = SymbolTable::from_fields(&ast.roles[0].sprites[0], ref_pool);

    (proc, globals, fields)
}

//<variable name="field"><l>0</l></variable>

#[test]
fn test_proc_ret() {
    let mut ref_pool = RefPool::new(true);
    let locals = SymbolTable::default();
    let (mut proc, mut globals, mut fields) = get_running_proc(&format!(include_str!("templates/single-func.xml"),
        globals = "",
        fields = "",
        funcs = r#"<block-definition s="main" type="command" category="motion"><header></header><code></code><translations></translations><inputs></inputs><script><block s="doDeclareVariables"><list><l>local</l></list></block></script></block-definition>"#,
        methods = "",
    ), locals, &mut ref_pool);

    let ret = loop {
        match proc.step(&mut ref_pool, &mut globals, &mut fields) {
            StepResult::Idle => panic!(),
            StepResult::Normal | StepResult::Yield => (),
            StepResult::Terminate(e) => break e.unwrap(),
        }
    };
    assert!(!proc.is_running());

    match ret.unwrap() {
        Value::RefValue(key) => match ref_pool.get(key).unwrap() {
            RefValue::String(x) => assert_eq!(x, ""),
            x => panic!("{:?}", x),
        }
        x => panic!("{:?}", x),
    }
}
