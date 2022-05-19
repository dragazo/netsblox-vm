//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;

use netsblox_ast as ast;

pub(crate) enum Instruction {
    Assign { vars: Vec<String> }, // consumes 1 value from stack
    Return, // return value on top of stack

    PushValue { value: ast::Value }, // adds 1 value to stack
    PopValue, // consumes 1 value from stack
}

/// A interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::process::Process) is an execution primitive that can be used to execute generated `ByteCode`.
pub struct ByteCode(pub(crate) Vec<Instruction>);
/// Location info for a [`ByteCode`] object.
pub struct EntityLocations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub scripts: Vec<(&'a ast::Script, usize)>,
}
/// Location info for a [`ByteCode`] object.
pub struct Locations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub entities: Vec<(&'a ast::Sprite, EntityLocations<'a>)>,
}
impl ByteCode {
    fn append_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Value(v) => self.0.push(Instruction::PushValue { value: v.clone() }),
            _ => unimplemented!(),
        }
    }
    fn append_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Assign { vars, value, .. } => {
                self.append_expr(value);
                self.0.push(Instruction::Assign { vars: vars.iter().map(|x| x.trans_name.clone()).collect() })
            }
            _ => unimplemented!(),
        }
    }
    fn append_stmts_ret(&mut self, stmts: &[ast::Stmt]) {
        for stmt in stmts {
            self.append_stmt(stmt);
        }
        self.0.push(Instruction::PushValue { value: "".into() });
        self.0.push(Instruction::Return);
    }
    /// Compiles a single project role into an executable form.
    /// Also emits the symbol table of functions and scripts,
    /// which is needed to execute a specific segment of code.
    pub fn compile(role: &ast::Role) -> (ByteCode, Locations) {
        let mut code = ByteCode(vec![]);

        let mut funcs = Vec::with_capacity(role.funcs.len());
        for func in role.funcs.iter() {
            funcs.push((func, code.0.len()));
            code.append_stmts_ret(&func.stmts)
        }

        let mut entities = Vec::with_capacity(role.sprites.len());
        for entity in role.sprites.iter() {
            let mut funcs = Vec::with_capacity(entity.funcs.len());
            for func in entity.funcs.iter() {
                funcs.push((func, code.0.len()));
                code.append_stmts_ret(&func.stmts);
            }

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for script in entity.scripts.iter() {
                scripts.push((script, code.0.len()));
                code.append_stmts_ret(&script.stmts);
            }

            entities.push((entity, EntityLocations { funcs, scripts }));
        }

        (code, Locations { funcs, entities })
    }
}
