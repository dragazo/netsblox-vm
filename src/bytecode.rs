use std::prelude::v1::*;

use netsblox_ast as ast;

pub enum Instruction {
    Assign { vars: Vec<String> }, // consumes 1 value from stack
    Return, // return value on top of stack

    PushValue { value: ast::Value }, // adds 1 expr to stack
    PopValue, // consumes 1 expr from stack
}

pub struct ByteCode(Vec<Instruction>);
pub struct EntityLocations {
    pub funcs: Vec<usize>,
    pub scripts: Vec<usize>,
}
pub struct Locations {
    pub funcs: Vec<usize>,
    pub entities: Vec<EntityLocations>,
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
    pub fn compile(script: &ast::Role) -> (ByteCode, Locations) {
        let mut code = ByteCode(vec![]);

        let mut funcs = Vec::with_capacity(script.funcs.len());
        for func in script.funcs.iter() {
            funcs.push(code.0.len());
            code.append_stmts_ret(&func.stmts)
        }

        let mut entities = Vec::with_capacity(script.sprites.len());
        for entity in script.sprites.iter() {
            let mut funcs = Vec::with_capacity(entity.funcs.len());
            for func in entity.funcs.iter() {
                funcs.push(code.0.len());
                code.append_stmts_ret(&func.stmts);
            }

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for script in entity.scripts.iter() {
                scripts.push(code.0.len());
                code.append_stmts_ret(&script.stmts);
            }

            entities.push(EntityLocations { funcs, scripts });
        }

        (code, Locations { funcs, entities })
    }
}
