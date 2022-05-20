//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;

use netsblox_ast as ast;

#[derive(Clone, Copy, Debug)]
pub(crate) enum BinaryOp {
    Add, Sub,
    Greater,
}

#[derive(Debug)]
pub(crate) enum Instruction {
    /// Do nothing for one cycle.
    Noop,

    /// Pushes 1 value to the value stack.
    PushValue { value: ast::Value },
    /// Pushes 1 value to the value stack, as looked up from the current execution context.
    PushVariable { var: String },
    /// Consumes 1 value from the value stack and discards it.
    PopValue,

    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the value `f(a, b)` onto the value stack.
    BinaryOp { op: BinaryOp },

    /// Consumes 1 value from the value stack and assigns it to all of the specified variables.
    Assign { vars: Vec<String> },
    /// Consumes 1 value, `b` from the value stack, fetches the variable `a`, and assigns it `f(a, b)`.
    BinaryOpAssign { var: String, op: BinaryOp },

    /// Unconditionally jumps to the given location.
    Jump { pos: usize },
    /// Pops a value from the value stack and jumps to the given location if its truthyness value is equal to `when`
    ConditionalJump { pos: usize, when: bool },

    /// Consumes `args.len()` arguments from the value stack to assign to a new context (in reverse order).
    /// Pushes the new context onto the context stack.
    /// Pushes the return address onto the call stack.
    /// Jumps to the given location.
    Call { pos: usize, args: Vec<String> },
    /// Pops a return address from the call stack and jumps to it.
    /// The return value is left on the top of the value stack.
    /// If the call stack is empty, this instead terminates the process
    /// with the reported value being the (only) value remaining in the value stack.
    Return,
}

/// A interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::process::Process) is an execution primitive that can be used to execute generated `ByteCode`.
#[derive(Debug)]
pub struct ByteCode(pub(crate) Vec<Instruction>);
/// Location info for a [`ByteCode`] object.
#[derive(Debug)]
pub struct EntityLocations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub scripts: Vec<(&'a ast::Script, usize)>,
}
/// Location info for a [`ByteCode`] object.
#[derive(Debug)]
pub struct Locations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub entities: Vec<(&'a ast::Sprite, EntityLocations<'a>)>,
}
impl ByteCode {
    fn append_expr_binary_op(&mut self, left: &ast::Expr, right: &ast::Expr, op: BinaryOp) {
        self.append_expr(left);
        self.append_expr(right);
        self.0.push(Instruction::BinaryOp { op });
    }
    fn append_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Value(v) => self.0.push(Instruction::PushValue { value: v.clone() }),
            ast::Expr::Variable { var, .. } => self.0.push(Instruction::PushVariable { var: var.trans_name.clone() }),
            ast::Expr::Add { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Add),
            ast::Expr::Sub { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Sub),
            ast::Expr::Greater { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Greater),
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Assign { vars, value, .. } => {
                self.append_expr(value);
                self.0.push(Instruction::Assign { vars: vars.iter().map(|x| x.trans_name.clone()).collect() })
            }
            ast::Stmt::AddAssign { var, value, .. } => {
                self.append_expr(value);
                self.0.push(Instruction::BinaryOpAssign { var: var.trans_name.clone(), op: BinaryOp::Add })
            }
            ast::Stmt::Return { value, .. } => {
                self.append_expr(value);
                self.0.push(Instruction::Return);
            }
            ast::Stmt::InfLoop { stmts, .. } => {
                let top = self.0.len();
                for stmt in stmts {
                    self.append_stmt(stmt);
                }
                self.0.push(Instruction::Jump { pos: top });
            }
            ast::Stmt::If { condition, then, .. } => {
                self.append_expr(condition);
                let patch_pos = self.0.len();
                self.0.push(Instruction::Noop);
                for stmt in then {
                    self.append_stmt(stmt);
                }
                let else_pos = self.0.len();
                self.0[patch_pos] = Instruction::ConditionalJump { pos: else_pos, when: false };
            }
            x => unimplemented!("{:?}", x),
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
