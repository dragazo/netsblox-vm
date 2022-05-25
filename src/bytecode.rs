//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;
use std::collections::BTreeMap;

use netsblox_ast as ast;

#[derive(Clone, Copy, Debug)]
pub(crate) enum BinaryOp {
    Add, Sub, Mul, Div, Mod, Pow, Log,
    Greater, Less,
}
#[derive(Clone, Copy, Debug)]
pub(crate) enum UnaryOp {
    ToBool,
    Abs, Neg,
    Sqrt,
    Round, Floor, Ceil,
    Sin, Cos, Tan,
    Asin, Acos, Atan,
}

#[derive(Debug)]
pub(crate) enum Instruction {
    /// Triggers an error when encountered.
    /// This is an internal value that is only used to denote incomplete linking results for better testing.
    /// Properly-linked byte code should not contain this value.
    Illegal,

    /// Explicitly trigger a yield point. This instruction is otherwise a no-op.
    Yield,

    /// Pushes 1 value to the value stack.
    PushValue { value: ast::Value },
    /// Pushes 1 value to the value stack, as looked up from the current execution context.
    PushVariable { var: String },
    /// Consumes `count` values from the value stack and discards them.
    PopValues { count: usize },

    /// Pushes 1 value onto the value stack, which is a copy of item `top_index` from the value stack.
    /// The top of the stack has `top_index == 0`, the item below it has `top_index == 1`, and so on.
    DupeValue { top_index: usize },
    /// Swaps two values in the value stack, as determined by the specified top index values (see [`Instruction::DupeValue`].
    SwapValues { top_index_1: usize, top_index_2: usize },

    /// Consumes 1 value, `val`, from the value stack and pushes a shallow copy of `val` into the value stack.
    ShallowCopy,

    /// Consumes `len` values from the value stack and creates a new list with those values in reverse order.
    /// Pushes the new list back onto the value stack.
    MakeList { len: usize },
    /// Consumes two values, `b` and `a`, from the value stack and constructs a new list containing the values
    /// starting at `a` and ending at `b` (inclusive), stepping by either `+1.0` or `-1.0` depending
    /// on whether `a < b` or `b < a`. If `a == b`, then the result is `[a]`.
    /// The new list is placed back onto the value stack.
    MakeListRange,

    /// Pops a value, `x`, and a list, `list`, from the value stack and adds `x` to the end of `list`.
    ListPush,

    /// Consumes 1 value, `list`, from the value stack and pushes the the length of the list onto the value stack.
    ListLen,
    /// Consumes two values, `index` and `list`, from the value stack and pushes the value `list[index]` onto the value stack.
    ListIndex,
    /// Consumes 1 value, `list`, from the value stack and pushes the last item in the list onto the value stack.
    ListLastIndex,
    /// Pops three values, `value`, `index`, and `list`, from the value stack and assigns `list[index] = value`.
    ListIndexAssign,

    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the value `f(a, b)` onto the value stack.
    BinaryOp { op: BinaryOp },
    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the (boolean) value `a == b` onto the value stack,
    /// where `==` is a deep comparison allowing type conversions.
    /// This is similar to [`Instruction::BinaryOp`] except that it is not vectorized and always returns a single (scalar) boolean value.
    Eq,
    /// Consumes 1 value, `x`, from the value stack, and pushes the value `f(x)` onto the value stack.
    UnaryOp { op: UnaryOp },

    /// Consumes 1 value from the value stack and assigns it to all of the specified variables.
    Assign { vars: Vec<String> },
    /// Consumes 1 value, `b` from the value stack, fetches the variable `a`, and assigns it `f(a, b)`.
    BinaryOpAssign { var: String, op: BinaryOp },

    /// Unconditionally jumps to the given location.
    Jump { to: usize },
    /// Pops a value from the value stack and jumps to the given location if its truthyness value is equal to `when`
    ConditionalJump { to: usize, when: bool },

    /// Consumes `params.len()` arguments from the value stack (in reverse order of the listed params) to assign to a new symbol table.
    /// Pushes the symbol table and return address to the call stack, and finally jumps to the given location.
    Call { pos: usize, params: Vec<String> },
    /// Pops a return address from the call stack and jumps to it.
    /// The return value is left on the top of the value stack.
    /// If the call stack is empty, this instead terminates the process
    /// with the reported value being the (only) value remaining in the value stack.
    Return,
}

/// An interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::process::Process) is an execution primitive that can be used to execute generated `ByteCode`.
#[derive(Debug)]
pub struct ByteCode(pub(crate) Vec<Instruction>);
/// Location info in a [`ByteCode`] object for a particular entity.
#[derive(Debug)]
pub struct EntityLocations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub scripts: Vec<(&'a ast::Script, usize)>,
}
/// Location info in a [`ByteCode`] object.
#[derive(Debug)]
pub struct Locations<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub entities: Vec<(&'a ast::Entity, EntityLocations<'a>)>,
}

#[derive(Default)]
struct ByteCodeBuilder<'a> {
    ins: Vec<Instruction>,
    call_holes: Vec<(usize, &'a ast::FnRef, Option<&'a ast::Entity>)>,
}
impl<'a> ByteCodeBuilder<'a> {
    fn append_expr_binary_op(&mut self, left: &'a ast::Expr, right: &'a ast::Expr, op: BinaryOp, entity: Option<&'a ast::Entity>) {
        self.append_expr(left, entity);
        self.append_expr(right, entity);
        self.ins.push(Instruction::BinaryOp { op });
    }
    fn append_expr_unary_op(&mut self, value: &'a ast::Expr, op: UnaryOp, entity: Option<&'a ast::Entity>) {
        self.append_expr(value, entity);
        self.ins.push(Instruction::UnaryOp { op });
    }
    fn append_expr(&mut self, expr: &'a ast::Expr, entity: Option<&'a ast::Entity>) {
        match expr {
            ast::Expr::Value(v) => self.ins.push(Instruction::PushValue { value: v.clone() }),
            ast::Expr::Variable { var, .. } => self.ins.push(Instruction::PushVariable { var: var.trans_name.clone() }),
            ast::Expr::Add { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Add, entity),
            ast::Expr::Sub { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Sub, entity),
            ast::Expr::Mul { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Mul, entity),
            ast::Expr::Div { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Div, entity),
            ast::Expr::Pow { base, power, .. } => self.append_expr_binary_op(&*base, &*power, BinaryOp::Pow, entity),
            ast::Expr::Greater { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Greater, entity),
            ast::Expr::Less { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Less, entity),
            ast::Expr::Mod { left, right, .. } => self.append_expr_binary_op(&*left, &*right, BinaryOp::Mod, entity),
            ast::Expr::Log { base, value, .. } => self.append_expr_binary_op(&*base, &*value, BinaryOp::Log, entity),
            ast::Expr::Neg { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Neg, entity),
            ast::Expr::Abs { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Abs, entity),
            ast::Expr::Sqrt { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Sqrt, entity),
            ast::Expr::Sin { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Sin, entity),
            ast::Expr::Cos { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Cos, entity),
            ast::Expr::Tan { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Tan, entity),
            ast::Expr::Asin { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Asin, entity),
            ast::Expr::Acos { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Acos, entity),
            ast::Expr::Atan { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Atan, entity),
            ast::Expr::Round { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Round, entity),
            ast::Expr::Floor { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Floor, entity),
            ast::Expr::Ceil { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Ceil, entity),
            ast::Expr::Eq { left, right, .. } => {
                self.append_expr(left, entity);
                self.append_expr(right, entity);
                self.ins.push(Instruction::Eq);
            }
            ast::Expr::MakeList { values, .. } => {
                for value in values {
                    self.append_expr(value, entity);
                }
                self.ins.push(Instruction::MakeList { len: values.len() });
            }
            ast::Expr::ListIndex { list, index, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.ins.push(Instruction::ListIndex);
            }
            ast::Expr::ListLastIndex { list, .. } => {
                self.append_expr(list, entity);
                self.ins.push(Instruction::ListLastIndex);
            }
            ast::Expr::Listlen { value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListLen);
            }
            ast::Expr::RangeInclusive { start, stop, .. } => {
                self.append_expr(start, entity);
                self.append_expr(stop, entity);
                self.ins.push(Instruction::MakeListRange);
            }
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

                self.ins[test_pos] = Instruction::ConditionalJump { to: test_false_pos, when: false };
                self.ins[jump_aft_pos] = Instruction::Jump { to: aft_pos };
            }
            ast::Expr::Or { left, right, .. } => {
                self.append_expr(left, entity);
                self.ins.push(Instruction::DupeValue { top_index: 0 });
                let check_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);
                self.ins.push(Instruction::PopValues { count: 1 });
                self.append_expr(right, entity);
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: true };

                self.ins.push(Instruction::UnaryOp { op: UnaryOp::ToBool });
            }
            ast::Expr::And { left, right, .. } => {
                self.append_expr(left, entity);
                self.ins.push(Instruction::DupeValue { top_index: 0 });
                let check_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);
                self.ins.push(Instruction::PopValues { count: 1 });
                self.append_expr(right, entity);
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: false };

                self.ins.push(Instruction::UnaryOp { op: UnaryOp::ToBool });
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
    fn append_stmt(&mut self, stmt: &'a ast::Stmt, entity: Option<&'a ast::Entity>) {
        match stmt {
            ast::Stmt::Assign { vars, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::Assign { vars: vars.iter().map(|x| x.trans_name.clone()).collect() })
            }
            ast::Stmt::AddAssign { var, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::BinaryOpAssign { var: var.trans_name.clone(), op: BinaryOp::Add })
            }
            ast::Stmt::Push { list, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListPush);
            }
            ast::Stmt::IndexAssign { list, index, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListIndexAssign);
            }
            ast::Stmt::RunFn { function, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);
                self.ins.push(Instruction::PopValues { count: 1 });

                self.call_holes.push((call_hole_pos, function, entity));
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
                self.ins.push(Instruction::Yield);
                self.ins.push(Instruction::Jump { to: top });
            }
            ast::Stmt::UntilLoop { condition, stmts, .. } => {
                let top = self.ins.len();
                self.append_expr(condition, entity);
                let exit_jump_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::Jump { to: top });
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true };
            }
            ast::Stmt::Repeat { times, stmts, .. } => {
                self.append_expr(times, entity);

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 });
                self.ins.push(Instruction::PushValue { value: 0.0.into() });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater });
                let aft_jump_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }

                self.ins.push(Instruction::PushValue { value: 1.0.into() });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub });
                self.ins.push(Instruction::Yield);
                self.ins.push(Instruction::Jump { to: top });
                let aft = self.ins.len();

                self.ins[aft_jump_pos] = Instruction::ConditionalJump { to: aft, when: false };

                self.ins.push(Instruction::PopValues { count: 1 });
            }
            ast::Stmt::ForLoop { var, start, stop, stmts, .. } => {
                self.append_expr(start, entity);
                self.append_expr(stop, entity);

                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater });
                let delta_jump_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                self.ins.push(Instruction::PushValue { value: 1.0.into() });
                let positive_delta_end = self.ins.len();
                self.ins.push(Instruction::Illegal);
                let negative_delta_pos = self.ins.len();
                self.ins.push(Instruction::PushValue { value: (-1.0).into() });
                let aft_delta = self.ins.len();

                self.ins[delta_jump_pos] = Instruction::ConditionalJump { to: negative_delta_pos, when: true };
                self.ins[positive_delta_end] = Instruction::Jump { to: aft_delta };

                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 });
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 1 });
                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub });
                self.ins.push(Instruction::UnaryOp { op: UnaryOp::Abs });

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 });
                self.ins.push(Instruction::PushValue { value: 0.0.into() });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Less });
                let exit_jump_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::Assign { vars: vec![var.trans_name.clone()] });
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }

                self.ins.push(Instruction::PushValue { value: 1.0.into() });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub });
                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::DupeValue { top_index: 3 });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Add });
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 });
                self.ins.push(Instruction::PopValues { count: 1 });
                self.ins.push(Instruction::Yield);
                self.ins.push(Instruction::Jump { to: top });
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true };

                self.ins.push(Instruction::PopValues { count: 3 });
            }
            ast::Stmt::ForeachLoop { var, items, stmts, .. } => {
                self.append_expr(items, entity);
                self.ins.push(Instruction::ShallowCopy);
                self.ins.push(Instruction::PushValue { value: 1.0.into() });

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 });
                self.ins.push(Instruction::DupeValue { top_index: 2 });
                self.ins.push(Instruction::ListLen);
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater });
                let exit_jump_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::DupeValue { top_index: 1 });
                self.ins.push(Instruction::ListIndex);
                self.ins.push(Instruction::Assign { vars: vec![var.trans_name.clone()] });
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::PushValue { value: 1.0.into() });
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Add });
                self.ins.push(Instruction::Yield);
                self.ins.push(Instruction::Jump { to: top });
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true };

                self.ins.push(Instruction::PopValues { count: 2 });
            }
            ast::Stmt::If { condition, then, .. } => {
                self.append_expr(condition, entity);
                let patch_pos = self.ins.len();
                self.ins.push(Instruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity);
                }
                let else_pos = self.ins.len();
                self.ins[patch_pos] = Instruction::ConditionalJump { to: else_pos, when: false };
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmts_ret(&mut self, stmts: &'a [ast::Stmt], entity: Option<&'a ast::Entity>) {
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
                res.insert(*entity as *const ast::Entity, inner);
            }
            res
        };

        let get_ptr = |x: Option<&ast::Entity>| x.map(|x| x as *const ast::Entity).unwrap_or(std::ptr::null());
        for (hole_pos, hole_fn, hole_ent) in self.call_holes {
            let sym = &*hole_fn.trans_name;
            let &(pos, params) = entity_fn_to_info.get(&get_ptr(hole_ent)).and_then(|tab| tab.get(sym)).or_else(|| global_fn_to_info.get(sym)).unwrap();
            self.ins[hole_pos] = Instruction::Call { pos, params: params.iter().map(|x| x.trans_name.clone()).collect() };
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

        let mut entities = Vec::with_capacity(role.entities.len());
        for entity in role.entities.iter() {
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
