//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;
use std::collections::BTreeMap;

use netsblox_ast as ast;

#[derive(Clone, Copy, Debug)]
pub(crate) enum BinaryOp {
    Add, Sub, Mul, Div,
    Greater, Less,
}

pub(crate) enum Instruction {
    /// Triggers an error when encountered.
    /// This is an internal value that is only used to denote incomplete linking results for better testing.
    /// Properly-linked byte code should not contain this value.
    Illegal,

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

    /// Consumes `params.len()` arguments from the value stack (in reverse order of the listed params) to assign to a new symbol table.
    /// Pushes the symbol table and return address to the call stack, and finally jumps to the given location.
    Call { pos: usize, params: Vec<String> },
    /// Pops a return address from the call stack and jumps to it.
    /// The return value is left on the top of the value stack.
    /// If the call stack is empty, this instead terminates the process
    /// with the reported value being the (only) value remaining in the value stack.
    Return,
}

/// A interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::process::Process) is an execution primitive that can be used to execute generated `ByteCode`.
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

#[derive(Default)]
struct ByteCodeBuilder<'a> {
    ins: Vec<Instruction>,
    call_holes: Vec<(usize, &'a ast::FnRef, Option<&'a ast::Sprite>)>,
}
impl<'a> ByteCodeBuilder<'a> {
    fn append_expr_binary_op(&mut self, left: &'a ast::Expr, right: &'a ast::Expr, op: BinaryOp, entity: Option<&'a ast::Sprite>) {
        self.append_expr(left, entity);
        self.append_expr(right, entity);
        self.ins.push(Instruction::BinaryOp { op });
    }
    fn append_expr(&mut self, expr: &'a ast::Expr, entity: Option<&'a ast::Sprite>) {
        match expr {
            ast::Expr::Value(v) => self.ins.push(Instruction::PushValue { value: v.clone() }),
            ast::Expr::Variable { var, .. } => self.ins.push(Instruction::PushVariable { var: var.trans_name.clone() }),
            ast::Expr::Add { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Add, entity),
            ast::Expr::Sub { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Sub, entity),
            ast::Expr::Mul { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Mul, entity),
            ast::Expr::Div { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Div, entity),
            ast::Expr::Greater { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Greater, entity),
            ast::Expr::Less { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Less, entity),
            ast::Expr::Conditional { condition, then, otherwise, .. } => {
                self.append_expr(condition, entity);
                let test_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                self.append_expr(then, entity);
                let jump_aft_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                let test_false_pos = self.ins.len();
                self.append_expr(otherwise, entity);
                let aft_pos = self.ins.len();

                self.ins[test_pos] = Instruction::ConditionalJump { pos: test_false_pos, when: false };
                self.ins[jump_aft_pos] = Instruction::Jump { pos: aft_pos };
            }
            ast::Expr::CallFn { function, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                self.call_holes.push((call_hole_pos, function, entity));
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmt(&mut self, stmt: &'a ast::Stmt, entity: Option<&'a ast::Sprite>) {
        match stmt {
            ast::Stmt::Assign { vars, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::Assign { vars: vars.iter().map(|x| x.trans_name.clone()).collect() })
            }
            ast::Stmt::AddAssign { var, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::BinaryOpAssign { var: var.trans_name.clone(), op: BinaryOp::Add })
            }
            ast::Stmt::Return { value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::Return);
            }
            ast::Stmt::InfLoop { stmts, .. } => {
                let top = self.ins.len();
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::Jump { pos: top });
            }
            ast::Stmt::If { condition, then, .. } => {
                self.append_expr(condition, entity);
                let patch_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity);
                }
                let else_pos = self.ins.len();
                self.ins[patch_pos] = Instruction::ConditionalJump { pos: else_pos, when: false };
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmts_ret(&mut self, stmts: &'a [ast::Stmt], entity: Option<&'a ast::Sprite>) {
        for stmt in stmts {
            self.append_stmt(stmt, entity);
        }
        self.ins.push(Instruction::PushValue { value: "".into() });
        self.ins.push(Instruction::Return);
    }
    fn link(mut self, locations: Locations<'a>) -> (ByteCode, Locations<'a>) {
        let global_fn_to_info = {
            let mut res = BTreeMap::new();
            for (func, pos) in locations.funcs.iter() {
                res.insert(&*func.trans_name, (*pos, &*func.params));
            }
            res
        };
        let entity_fn_to_info = {
            let mut res = BTreeMap::new();
            for (entity, entity_locs) in locations.entities.iter() {
                let mut inner = BTreeMap::new();
                for (func, pos) in entity_locs.funcs.iter() {
                    inner.insert(&*func.trans_name, (*pos, &*func.params));
                }
                res.insert(*entity as *const ast::Sprite, inner);
            }
            res
        };

        let get_ptr = |x: Option<&ast::Sprite>| x.map(|x| x as *const ast::Sprite).unwrap_or(std::ptr::null());
        for (hole_pos, hole_fn, hole_ent) in self.call_holes {
            let sym = &*hole_fn.trans_name;
            let &(pos, params) = entity_fn_to_info.get(&get_ptr(hole_ent)).and_then(|tab| tab.get(sym)).or_else(|| global_fn_to_info.get(sym)).unwrap();
            self.ins[hole_pos] = Instruction::Call { pos: pos, params: params.iter().map(|x| x.trans_name.clone()).collect() };
        }

        #[cfg(debug_assertions)]
        for ins in self.ins.iter() {
            if let Instruction::Illegal = ins {
                panic!();
            }
        }

        (ByteCode(self.ins), locations)
    }
}

impl ByteCode {
    /// Compiles a single project role into an executable form.
    /// Also emits the symbol table of functions and scripts,
    /// which is needed to execute a specific segment of code.
    pub fn compile(role: &ast::Role) -> (ByteCode, Locations) {
        let mut code = ByteCodeBuilder::default();

        let mut funcs = Vec::with_capacity(role.funcs.len());
        for func in role.funcs.iter() {
            funcs.push((func, code.ins.len()));
            code.append_stmts_ret(&func.stmts, None)
        }

        let mut entities = Vec::with_capacity(role.sprites.len());
        for entity in role.sprites.iter() {
            let mut funcs = Vec::with_capacity(entity.funcs.len());
            for func in entity.funcs.iter() {
                funcs.push((func, code.ins.len()));
                code.append_stmts_ret(&func.stmts, Some(entity));
            }

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for script in entity.scripts.iter() {
                scripts.push((script, code.ins.len()));
                code.append_stmts_ret(&script.stmts, Some(entity));
            }

            entities.push((entity, EntityLocations { funcs, scripts }));
        }

        code.link(Locations { funcs, entities })
    }
}
