use std::prelude::v1::*;
use std::rc::Rc;

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
    let fields = SymbolTable::from_fields(&ast.roles[0].sprites[0], ref_pool);

    (proc, globals, fields, main.1)
}

fn run_till_term(proc: &mut Process, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<Option<Value>, ExecError> {
    assert!(proc.is_running());
    let ret = loop {
        match proc.step(ref_pool, globals, fields) {
            StepResult::Idle => panic!(),
            StepResult::Normal | StepResult::Yield => (),
            StepResult::Terminate(e) => break e,
        }
    };
    assert!(!proc.is_running());
    ret
}

//<variable name="field"><l>0</l></variable>

#[test]
fn test_proc_ret() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, _) = get_running_proc(&format!(include_str!("templates/single-func.xml"),
        globals = "",
        fields = "",
        funcs = r#"<block-definition s="main" type="command" category="motion"><header></header><code></code><translations></translations><inputs></inputs><script><block s="doDeclareVariables"><list><l>local</l></list></block></script></block-definition>"#,
        methods = "",
    ), SymbolTable::default(), &mut ref_pool);

    match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
        Value::RefValue(key) => match ref_pool.get(key).unwrap() {
            RefValue::String(x) => assert_eq!(x, ""),
            x => panic!("{:?}", x),
        }
        x => panic!("{:?}", x),
    }
}

#[test]
fn test_proc_sum_123n() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, main) = get_running_proc(&format!(include_str!("templates/single-func.xml"),
        globals = "",
        fields = "",
        funcs = r#"<block-definition s="main %&apos;n&apos;" type="reporter" category="custom"><header></header><code></code><translations></translations><inputs><input type="%n"></input></inputs><script><block s="doDeclareVariables"><list><l>sum</l><l>i</l></list></block><block s="doSetVar"><l>sum</l><l>0</l></block><block s="doSetVar"><l>i</l><l>1</l></block><block s="doForever"><script><block s="doIf"><block s="reportGreaterThan"><block var="i"/><block var="n"/></block><script><block s="doReport"><block var="sum"/></block></script></block><block s="doChangeVar"><l>sum</l><block var="i"/></block><block s="doChangeVar"><l>i</l><l>1</l></block></script></block></script></block-definition>"#,
        methods = "",
    ), Default::default(), &mut ref_pool);

    for (n, expect) in [(0.0, 0.0), (1.0, 1.0), (2.0, 3.0), (3.0, 6.0), (4.0, 10.0), (5.0, 15.0), (6.0, 21.0)] {
        let mut locals = SymbolTable::default();
        locals.set_or_define("n", n.into());
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
            Value::CopyValue(CopyValue::Number(ret)) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}

#[test]
fn test_proc_recursive_factorial() {
    let mut ref_pool = RefPool::new(true);
    let (mut proc, mut globals, mut fields, main) = get_running_proc(&format!(include_str!("templates/single-func.xml"),
        globals = "",
        fields = "",
        funcs = r#"<block-definition s="main %&apos;n&apos;" type="reporter" category="custom"><header></header><code></code><translations></translations><inputs><input type="%s"></input></inputs><script><block s="doReport"><block s="reportIfElse"><block s="reportLessThan"><block var="n"/><l>2</l></block><l>1</l><block s="reportProduct"><block var="n"/><custom-block s="main %s"><block s="reportDifference"><block var="n"/><l>1</l></block></custom-block></block></block></block></script></block-definition>"#,
        methods = "",
    ), Default::default(), &mut ref_pool);

    for (n, expect) in [(0.0, 1.0), (1.0, 1.0), (2.0, 2.0), (3.0, 6.0), (4.0, 24.0), (5.0, 120.0), (6.0, 720.0), (7.0, 5040.0)] {
        let mut locals = SymbolTable::default();
        locals.set_or_define("n", n.into());
        proc.initialize(main, locals);
        match run_till_term(&mut proc, &mut ref_pool, &mut globals, &mut fields).unwrap().unwrap() {
            Value::CopyValue(CopyValue::Number(ret)) => assert_eq!(ret, expect),
            x => panic!("{:?}", x),
        }
    }
}
