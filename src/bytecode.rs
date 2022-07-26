//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};
use std::mem;

use num_traits::FromPrimitive;

use crate::*;
use crate::gc::*;

#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub(crate) enum BinaryOp {
    Add, Sub, Mul, Div, Mod, Pow, Log,
    Greater, Less,
    SplitCustom,
}
#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub(crate) enum UnaryOp {
    ToBool, Not,
    Abs, Neg,
    Sqrt,
    Round, Floor, Ceil,
    Sin, Cos, Tan,
    Asin, Acos, Atan,
    SplitLetter, SplitWord, SplitTab, SplitCR, SplitLF, SplitCsv, SplitJson,
    Strlen,
    UnicodeToChar, CharToUnicode,
}

pub(crate) enum InternalInstruction<'a> {
    /// Triggers an error when encountered.
    /// This is an internal value that is only used to denote incomplete linking results for better testing.
    /// Properly-linked byte code should not contain this value.
    Illegal,
    /// A special instruction which is used by the linker to simulate inserting multiple instructions at a single instruction position.
    /// After linking, this variant will not be present in the resulting binary.
    /// Notably, these packed instructions must be a single logical step, because addressing is only allowed at the [`InternalInstruction`] level.
    Packed(Vec<Instruction<'a>>),
    /// A valid instruction that will be present in the resulting binary.
    Valid(Instruction<'a>),
}
impl<'a> From<Instruction<'a>> for InternalInstruction<'a> { fn from(ins: Instruction<'a>) -> Self { Self::Valid(ins) } }

#[derive(Debug)]
#[repr(u8)]
pub(crate) enum Instruction<'a> {
    /// Explicitly trigger a yield point. This instruction is otherwise a no-op.
    Yield,
    /// Marks the start of a warp section. Note that warp sections can be nested.
    WarpStart,
    /// Marks the end of a warp section started by [`Instruction::WarpStart`].
    WarpStop,

    /// Pushes 1 bool value to the value stack.
    PushBool { value: bool },
    /// Pushes 1 number value to the value stack.
    PushNumber { value: f64 },
    /// Pushes 1 string value to the value stack.
    PushString { value: &'a str },
    /// Pushes 1 value to the value stack, as looked up from the current execution context.
    PushVariable { var: &'a str },
    /// Consumes `count` values from the value stack and discards them.
    PopValue,

    /// Pushes 1 value onto the value stack, which is a copy of item `top_index` from the value stack.
    /// The top of the stack has `top_index == 0`, the item below it has `top_index == 1`, and so on.
    DupeValue { top_index: u8 },
    /// Swaps two values in the value stack, as determined by the specified top index values (see [`Instruction::DupeValue`].
    SwapValues { top_index_1: u8, top_index_2: u8 },
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

    /// Consumes 1 value, `list`, from the value stack and pushes the length of the list onto the value stack.
    ListLen,
    /// Consumes 1 value, `list`, from the value stack and pushes a bool representing if the list is empty onto the value stack.
    ListIsEmpty,

    /// Consumes three values, `value, `index`, and `list`, from the value stack and inserts `value` at position `index` of `list`.
    ListInsert,
    /// Consumes two values, `value` and `list`, from the value stack and inserts `value` at the end of `list`.
    ListInsertLast,
    /// Consumes two values, `value` and `list`, from the values stack and inserts `value` at a random position in the list.
    ListInsertRandom,

    /// Consumes two values, `index` and `list`, from the value stack and pushes the value `list[index]` onto the value stack.
    ListGet,
    /// Consumes 1 value, `list`, from the value stack and pushes the last item in the list onto the value stack.
    ListGetLast,
    /// Consumes 1 value, `list`, from the value stack and pushes a random item from the list onto the value stack.
    ListGetRandom,

    /// Consumes three values, `value`, `index`, and `list`, from the value stack and assigns `list[index] = value`.
    ListAssign,
    /// Consumes two values, `value` and `list`, from the value stack and assigns `value` to the last position in the list.
    ListAssignLast,
    /// Consumes two values, `value` and `list`, from the value stack and assigns `value` to a random position in the list.
    ListAssignRandom,

    /// Consumes two values, `index` and `list`, from the value stack and deletes item `index` from `list`.
    ListRemove,
    /// Consumes one value, `list`, from the value stack and deletes the last item from it.
    ListRemoveLast,
    /// Consumes one value, `list`, from the value stack and deletes a random item from it.
    ListRemoveRandom,

    /// Consumes `args` values from the value stack in reverse order and concatenates them into a single string, which is then pushed onto the value stack.
    Strcat { args: usize },

    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the value `f(a, b)` onto the value stack.
    BinaryOp { op: BinaryOp },
    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the (boolean) value `a == b` onto the value stack,
    /// where `==` is a deep comparison allowing type conversions.
    /// This is similar to [`Instruction::BinaryOp`] except that it is not vectorized and always returns a single (scalar) boolean value.
    Eq,
    /// Consumes 1 value, `x`, from the value stack, and pushes the value `f(x)` onto the value stack.
    UnaryOp { op: UnaryOp },

    /// Re/Declares a set of local variables, which are initialized to 0.
    /// Note that this is not equivalent to assigning a value of zero to the variable due to the potential issue of [`Shared::Aliased`].
    /// A new, [`Shared::Unique`] local variable must be created.
    DeclareLocal { var: &'a str },
    /// Consumes 1 value from the value stack and assigns it to the specified variable.
    Assign { var: &'a str },
    /// Consumes 1 value, `b` from the value stack, fetches the variable `a`, and assigns it `f(a, b)`.
    /// Equivalent to fetching the variable, performing the operation, and re-assigning the new value, but is atomic.
    BinaryOpAssign { var: &'a str, op: BinaryOp },

    /// Unconditionally jumps to the given location.
    Jump { to: usize },
    /// Pops a value from the value stack and jumps to the given location if its truthyness value is equal to `when`
    ConditionalJump { to: usize, when: bool },

    /// Pushes 1 string value onto the meta stack.
    MetaPush { value: &'a str },

    /// Consumes `params` values from the meta stack (in reverse order) which are names of parameters to pass.
    /// Then consumes `params` arguments from the value stack (in reverse order of the listed params) to assign to a new symbol table.
    /// Pushes the symbol table and return address to the call stack, and finally jumps to the given location.
    Call { pos: usize, params: usize },
    /// Consumes `captures` values from the meta stack (in reverse order), and then `params` values from the meta stack, each representing symbol names.
    /// Then creates a closure object with the given information.
    /// Captures are looked up and bound immediately based on the current execution context.
    MakeClosure { pos: usize, params: usize, captures: usize },
    /// Consumes 1 argument, `closure`, and another `args` arguments (in reverse order) from the value stack
    /// to assign to the parameters of `closure` before executing the closure's stored code.
    /// It is an error if the number of supplied arguments does not match the number of parameters.
    CallClosure { args: usize },
    /// Consumes `args` values from the meta stack and value stack, representing arguments.
    /// Then calls the given RPC, awaits the result, and pushes the return value onto the value stack.
    CallRpc { service: &'a str, rpc: &'a str, args: usize },
    /// Pops a return address from the call stack and jumps to it.
    /// The return value is left on the top of the value stack.
    /// If the call stack is empty, this instead terminates the process
    /// with the reported value being the (only) value remaining in the value stack.
    Return,

    /// Pops 1 value from the value stack, `msg_type`, and broadcasts a message to all scripts.
    /// The `wait` flag can be set to denote that the broadcasting script should wait until all receiving scripts have terminated.
    Broadcast { wait: bool },
}

pub(crate) trait Binary<'a>: Sized {
    /// Reads a value from `src` starting at `start`.
    /// Returns the read value and the position of the first byte after the read segment.
    fn read(src: &'a [u8], start: usize) -> (Self, usize);
    /// Appends a binary representation of the value to the given binary buffer.
    /// The addresses of any written pointers will be appended to `pointer_positions` (for relocation purposes).
    /// This function is not intended for use outside of [`ByteCode`] linking.
    fn append(val: &Self, out: &mut Vec<u8>, pointer_positions: &mut Vec<usize>);
}

macro_rules! binary_int_impl {
    ($($t:ty),+$(,)?) => {$(
        impl Binary<'_> for $t {
            fn read(src: &[u8], start: usize) -> (Self, usize) {
                let mut buf = [0u8; mem::size_of::<$t>()];
                buf[..].copy_from_slice(&src[start..start + mem::size_of::<$t>()]);
                (<$t>::from_le_bytes(buf), start + mem::size_of::<$t>())
            }
            fn append(val: &Self, out: &mut Vec<u8>, _: &mut Vec<usize>) {
                out.extend_from_slice(&<$t>::to_le_bytes(*val))
            }
        }
    )*}
}
binary_int_impl! { u64, u32, u16, u8, f64 }

impl Binary<'_> for BinaryOp {
    fn read(src: &[u8], start: usize) -> (Self, usize) {
        (Self::from_u8(src[start]).unwrap(), start + 1)
    }
    fn append(val: &Self, out: &mut Vec<u8>, _: &mut Vec<usize>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        out.push((*val) as u8);
    }
}
impl Binary<'_> for UnaryOp {
    fn read(src: &[u8], start: usize) -> (Self, usize) {
        (Self::from_u8(src[start]).unwrap(), start + 1)
    }
    fn append(val: &Self, out: &mut Vec<u8>, _: &mut Vec<usize>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        out.push((*val) as u8)
    }
}

type UsizeRepr = u32; // we'll assume projects don't include over 4GB of code, cause that's ridiculous
impl Binary<'_> for usize {
    fn read(src: &[u8], start: usize) -> (Self, usize) {
        let x: (UsizeRepr, usize) = Binary::read(src, start);
        debug_assert!(x.0 <= usize::MAX as UsizeRepr);
        (x.0 as usize, x.1)
    }
    fn append(val: &Self, out: &mut Vec<u8>, pointer_positions: &mut Vec<usize>) {
        assert!(*val == *val as UsizeRepr as usize);
        Binary::append(&((*val) as UsizeRepr), out, pointer_positions)
    }
}

impl<'a> Binary<'a> for &'a str {
    fn read(src: &'a [u8], start: usize) -> (Self, usize) {
        let len: (usize, usize) = Binary::read(src, start);
        (&std::str::from_utf8(&src[len.1..len.1 + len.0]).unwrap(), len.1 + len.0)
    }
    fn append(val: &Self, out: &mut Vec<u8>, pointer_positions: &mut Vec<usize>) {
        Binary::append(&val.len(), out, pointer_positions);
        out.extend_from_slice(val.as_bytes());
    }
}

impl<'a> Binary<'a> for Instruction<'a> {
    fn read(src: &'a [u8], start: usize) -> (Self, usize) {
        macro_rules! read_prefixed {
            (Instruction::$root:ident) => {
                (Instruction::$root, start + 1)
            };
            (Instruction::$root:ident { $($tt:tt)* } $(: $($vals:ident),+$(,)? )?) => {{
                #[allow(unused_mut)]
                let mut parsing_stop = start + 1;
                $($(let $vals = {
                    let x = Binary::read(src, parsing_stop);
                    parsing_stop = x.1;
                    x.0
                };)*)?
                (Instruction::$root { $($tt)* $($($vals),+ )? }, parsing_stop)
            }};
        }
        match src[start] {
            0 => read_prefixed!(Instruction::Yield),
            1 => read_prefixed!(Instruction::WarpStart),
            2 => read_prefixed!(Instruction::WarpStop),

            3 => read_prefixed!(Instruction::PushBool { value: false }),
            4 => read_prefixed!(Instruction::PushBool { value: true }),
            5 => read_prefixed!(Instruction::PushNumber {} : value),
            6 => read_prefixed!(Instruction::PushString {} : value),
            7 => read_prefixed!(Instruction::PushVariable {} : var),
            8 => read_prefixed!(Instruction::PopValue),

            9 => read_prefixed!(Instruction::DupeValue {} : top_index),
            10 => read_prefixed!(Instruction::SwapValues {} : top_index_1, top_index_2),
            11 => read_prefixed!(Instruction::ShallowCopy),

            12 => read_prefixed!(Instruction::MakeList {} : len),
            13 => read_prefixed!(Instruction::MakeListRange),

            14 => read_prefixed!(Instruction::ListLen),
            15 => read_prefixed!(Instruction::ListIsEmpty),

            16 => read_prefixed!(Instruction::ListInsert),
            17 => read_prefixed!(Instruction::ListInsertLast),
            18 => read_prefixed!(Instruction::ListInsertRandom),

            19 => read_prefixed!(Instruction::ListGet),
            20 => read_prefixed!(Instruction::ListGetLast),
            21 => read_prefixed!(Instruction::ListGetRandom),

            22 => read_prefixed!(Instruction::ListAssign),
            23 => read_prefixed!(Instruction::ListAssignLast),
            24 => read_prefixed!(Instruction::ListAssignRandom),

            25 => read_prefixed!(Instruction::ListRemove),
            26 => read_prefixed!(Instruction::ListRemoveLast),
            27 => read_prefixed!(Instruction::ListRemoveRandom),

            28 => read_prefixed!(Instruction::Strcat {} : args),

            29 => read_prefixed!(Instruction::BinaryOp {} : op),
            30 => read_prefixed!(Instruction::Eq),
            31 => read_prefixed!(Instruction::UnaryOp {} : op),

            32 => read_prefixed!(Instruction::DeclareLocal {} : var),
            33 => read_prefixed!(Instruction::Assign {} : var),
            34 => read_prefixed!(Instruction::BinaryOpAssign {} : var, op),

            35 => read_prefixed!(Instruction::Jump {} : to),
            36 => read_prefixed!(Instruction::ConditionalJump { when: false, } : to),
            37 => read_prefixed!(Instruction::ConditionalJump { when: true, } : to),

            38 => read_prefixed!(Instruction::MetaPush {} : value),

            39 => read_prefixed!(Instruction::Call {} : pos, params),
            40 => read_prefixed!(Instruction::MakeClosure {} : pos, params, captures),
            41 => read_prefixed!(Instruction::CallClosure {} : args),
            42 => read_prefixed!(Instruction::CallRpc {} : service, rpc, args),
            43 => read_prefixed!(Instruction::Return),

            44 => read_prefixed!(Instruction::Broadcast { wait: false }),
            45 => read_prefixed!(Instruction::Broadcast { wait: true }),

            _ => unreachable!(),
        }
    }
    fn append(val: &Self, out: &mut Vec<u8>, pointer_positions: &mut Vec<usize>) {
        macro_rules! append_prefixed {
            ($op:literal $(: $($($vals:ident)+),+)?) => {{
                out.push($op);
                $($( append_prefixed!(@single $($vals)+); )*)?
            }};
            (@single move $val:ident) => {{
                pointer_positions.push(out.len());
                append_prefixed!(@single $val);
            }};
            (@single $val:ident) => { Binary::append($val, out, pointer_positions) };
        }
        match val {
            Instruction::Yield => append_prefixed!(0),
            Instruction::WarpStart => append_prefixed!(1),
            Instruction::WarpStop => append_prefixed!(2),

            Instruction::PushBool { value: false } => append_prefixed!(3),
            Instruction::PushBool { value: true } => append_prefixed!(4),
            Instruction::PushNumber { value } => append_prefixed!(5: value),
            Instruction::PushString { value } => append_prefixed!(6: value),
            Instruction::PushVariable { var } => append_prefixed!(7: var),
            Instruction::PopValue => append_prefixed!(8),

            Instruction::DupeValue { top_index } => append_prefixed!(9: top_index),
            Instruction::SwapValues { top_index_1, top_index_2 } => append_prefixed!(10: top_index_1, top_index_2),
            Instruction::ShallowCopy => append_prefixed!(11),

            Instruction::MakeList { len } => append_prefixed!(12: len),
            Instruction::MakeListRange => append_prefixed!(13),

            Instruction::ListLen => append_prefixed!(14),
            Instruction::ListIsEmpty => append_prefixed!(15),

            Instruction::ListInsert => append_prefixed!(16),
            Instruction::ListInsertLast => append_prefixed!(17),
            Instruction::ListInsertRandom => append_prefixed!(18),

            Instruction::ListGet => append_prefixed!(19),
            Instruction::ListGetLast => append_prefixed!(20),
            Instruction::ListGetRandom => append_prefixed!(21),

            Instruction::ListAssign => append_prefixed!(22),
            Instruction::ListAssignLast => append_prefixed!(23),
            Instruction::ListAssignRandom => append_prefixed!(24),

            Instruction::ListRemove => append_prefixed!(25),
            Instruction::ListRemoveLast => append_prefixed!(26),
            Instruction::ListRemoveRandom => append_prefixed!(27),

            Instruction::Strcat { args } => append_prefixed!(28: args),

            Instruction::BinaryOp { op } => append_prefixed!(29: op),
            Instruction::Eq => append_prefixed!(30),
            Instruction::UnaryOp { op } => append_prefixed!(31: op),

            Instruction::DeclareLocal { var } => append_prefixed!(32: var),
            Instruction::Assign { var } => append_prefixed!(33: var),
            Instruction::BinaryOpAssign { var, op } => append_prefixed!(34: var, op),

            Instruction::Jump { to } => append_prefixed!(35: move to),
            Instruction::ConditionalJump { to, when: false } => append_prefixed!(36: move to),
            Instruction::ConditionalJump { to, when: true } => append_prefixed!(37: move to),

            Instruction::MetaPush { value } => append_prefixed!(38: value),

            Instruction::Call { pos, params } => append_prefixed!(39: move pos, params),
            Instruction::MakeClosure { pos, params, captures } => append_prefixed!(40: move pos, params, captures),
            Instruction::CallClosure { args } => append_prefixed!(41: args),
            Instruction::CallRpc { service, rpc, args } => append_prefixed!(42: service, rpc, args),
            Instruction::Return => append_prefixed!(43),

            Instruction::Broadcast { wait: false } => append_prefixed!(44),
            Instruction::Broadcast { wait: true } => append_prefixed!(45),
        }
    }
}

/// An interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::runtime::Process) is an execution primitive that can be used to execute generated [`ByteCode`].
#[derive(Debug, Collect)]
#[collect(require_static)]
pub struct ByteCode(Box<[u8]>);
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
    ins: Vec<InternalInstruction<'a>>,
    call_holes: Vec<(usize, &'a ast::FnRef, Option<&'a ast::Entity>)>, // (hole pos, function, entity)
    closure_holes: VecDeque<(usize, &'a [ast::VariableDef], &'a [ast::VariableRef], &'a [ast::Stmt], Option<&'a ast::Entity>)>, // (hole pos, params, captures, stmts, entity)
}
impl<'a> ByteCodeBuilder<'a> {
    fn append_expr_binary_op(&mut self, left: &'a ast::Expr, right: &'a ast::Expr, op: BinaryOp, entity: Option<&'a ast::Entity>) {
        self.append_expr(left, entity);
        self.append_expr(right, entity);
        self.ins.push(Instruction::BinaryOp { op }.into());
    }
    fn append_expr_unary_op(&mut self, value: &'a ast::Expr, op: UnaryOp, entity: Option<&'a ast::Entity>) {
        self.append_expr(value, entity);
        self.ins.push(Instruction::UnaryOp { op }.into());
    }
    fn append_expr(&mut self, expr: &'a ast::Expr, entity: Option<&'a ast::Entity>) {
        match expr {
            ast::Expr::Value(v) => self.ins.push(match v {
                ast::Value::Number(v) => Instruction::PushNumber { value: *v },
                ast::Value::String(v) => Instruction::PushString { value: v },
                ast::Value::Constant(v) => Instruction::PushNumber {
                    value: match v {
                        ast::Constant::Pi => std::f64::consts::PI,
                        ast::Constant::E => std::f64::consts::E,
                    }
                },
                ast::Value::Bool(v) => Instruction::PushBool { value: *v },
                ast::Value::List(_) => unreachable!(),
            }.into()),
            ast::Expr::Variable { var, .. } => self.ins.push(Instruction::PushVariable { var: &var.trans_name }.into()),
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
            ast::Expr::Not { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Not, entity),
            ast::Expr::Strlen { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::Strlen, entity),
            ast::Expr::UnicodeToChar { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::UnicodeToChar, entity),
            ast::Expr::CharToUnicode { value, .. } => self.append_expr_unary_op(&*value, UnaryOp::CharToUnicode, entity),
            ast::Expr::Eq { left, right, .. } => {
                self.append_expr(left, entity);
                self.append_expr(right, entity);
                self.ins.push(Instruction::Eq.into());
            }
            ast::Expr::MakeList { values, .. } => {
                for value in values {
                    self.append_expr(value, entity);
                }
                self.ins.push(Instruction::MakeList { len: values.len() }.into());
            }
            ast::Expr::ListIndex { list, index, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.ins.push(Instruction::ListGet.into());
            }
            ast::Expr::ListLastIndex { list, .. } => {
                self.append_expr(list, entity);
                self.ins.push(Instruction::ListGetLast.into());
            }
            ast::Expr::ListRandIndex { list, .. } => {
                self.append_expr(list, entity);
                self.ins.push(Instruction::ListGetRandom.into());
            }
            ast::Expr::Listlen { value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListLen.into());
            }
            ast::Expr::ListIsEmpty { value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListIsEmpty.into());
            }
            ast::Expr::RangeInclusive { start, stop, .. } => {
                self.append_expr(start, entity);
                self.append_expr(stop, entity);
                self.ins.push(Instruction::MakeListRange.into());
            }
            ast::Expr::Conditional { condition, then, otherwise, .. } => {
                self.append_expr(condition, entity);
                let test_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.append_expr(then, entity);
                let jump_aft_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                let test_false_pos = self.ins.len();
                self.append_expr(otherwise, entity);
                let aft_pos = self.ins.len();

                self.ins[test_pos] = Instruction::ConditionalJump { to: test_false_pos, when: false }.into();
                self.ins[jump_aft_pos] = Instruction::Jump { to: aft_pos }.into();
            }
            ast::Expr::Or { left, right, .. } => {
                self.append_expr(left, entity);
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());
                self.append_expr(right, entity);
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();

                self.ins.push(Instruction::UnaryOp { op: UnaryOp::ToBool }.into());
            }
            ast::Expr::And { left, right, .. } => {
                self.append_expr(left, entity);
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());
                self.append_expr(right, entity);
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: false }.into();

                self.ins.push(Instruction::UnaryOp { op: UnaryOp::ToBool }.into());
            }
            ast::Expr::CallFn { function, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.call_holes.push((call_hole_pos, function, entity));
            }
            ast::Expr::CallClosure { closure, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                self.append_expr(closure, entity);
                self.ins.push(Instruction::CallClosure { args: args.len() }.into());
            }
            ast::Expr::CallRpc { service, rpc, args, .. } => {
                for (arg_name, arg) in args {
                    self.ins.push(Instruction::MetaPush { value: arg_name }.into());
                    self.append_expr(arg, entity);
                }
                self.ins.push(Instruction::CallRpc { service, rpc, args: args.len() }.into());
            }
            ast::Expr::Closure { params, captures, stmts, .. } => {
                let closure_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.closure_holes.push_back((closure_hole_pos, params, captures, stmts, entity));
            }
            ast::Expr::Strcat { values, .. } => {
                for value in values {
                    self.append_expr(value, entity);
                }
                self.ins.push(Instruction::Strcat { args: values.len() }.into());
            }
            ast::Expr::TextSplit { text, mode, .. } => {
                self.append_expr(text, entity);
                let ins = match mode {
                    ast::TextSplitMode::Letter => Instruction::UnaryOp { op: UnaryOp::SplitLetter },
                    ast::TextSplitMode::Word => Instruction::UnaryOp { op: UnaryOp::SplitWord },
                    ast::TextSplitMode::Tab => Instruction::UnaryOp { op: UnaryOp::SplitTab },
                    ast::TextSplitMode::CR => Instruction::UnaryOp { op: UnaryOp::SplitCR },
                    ast::TextSplitMode::LF => Instruction::UnaryOp { op: UnaryOp::SplitLF },
                    ast::TextSplitMode::Csv => Instruction::UnaryOp { op: UnaryOp::SplitCsv },
                    ast::TextSplitMode::Json => Instruction::UnaryOp { op: UnaryOp::SplitJson },
                    ast::TextSplitMode::Custom(pattern) => {
                        self.append_expr(pattern, entity);
                        Instruction::BinaryOp { op: BinaryOp::SplitCustom }
                    }
                };
                self.ins.push(ins.into());
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmt(&mut self, stmt: &'a ast::Stmt, entity: Option<&'a ast::Entity>) {
        match stmt {
            ast::Stmt::VarDecl { vars, .. } => {
                for var in vars {
                    self.ins.push(Instruction::DeclareLocal { var: &var.trans_name }.into());
                }
            }
            ast::Stmt::Assign { var, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into())
            }
            ast::Stmt::AddAssign { var, value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::BinaryOpAssign { var: &var.trans_name, op: BinaryOp::Add }.into())
            }
            ast::Stmt::Push { list, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListInsertLast.into());
            }
            ast::Stmt::InsertAt { list, value, index, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListInsert.into());
            }
            ast::Stmt::InsertAtRand { list, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListInsertRandom.into());
            }
            ast::Stmt::RemoveAt { list, index, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.ins.push(Instruction::ListRemove.into());
            }
            ast::Stmt::IndexAssign { list, index, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(index, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListAssign.into());
            }
            ast::Stmt::LastIndexAssign { list, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListAssignLast.into());
            }
            ast::Stmt::RandIndexAssign { list, value, .. } => {
                self.append_expr(list, entity);
                self.append_expr(value, entity);
                self.ins.push(Instruction::ListAssignRandom.into());
            }
            ast::Stmt::RunFn { function, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());

                self.call_holes.push((call_hole_pos, function, entity));
            }
            ast::Stmt::RunClosure { closure, args, .. } => {
                for arg in args {
                    self.append_expr(arg, entity);
                }
                self.append_expr(closure, entity);
                self.ins.push(Instruction::CallClosure { args: args.len() }.into());
                self.ins.push(Instruction::PopValue.into());
            }
            ast::Stmt::Return { value, .. } => {
                self.append_expr(value, entity);
                self.ins.push(Instruction::Return.into());
            }
            ast::Stmt::Warp { stmts, .. } => {
                self.ins.push(Instruction::WarpStart.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::WarpStop.into());
            }
            ast::Stmt::InfLoop { stmts, .. } => {
                let top = self.ins.len();
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
            }
            ast::Stmt::UntilLoop { condition, stmts, .. } => {
                let top = self.ins.len();
                self.append_expr(condition, entity);
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();
            }
            ast::Stmt::Repeat { times, stmts, .. } => {
                self.append_expr(times, entity);

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::PushNumber { value: 0.0 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater }.into());
                let aft_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }

                self.ins.push(Instruction::PushNumber { value: 1.0 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub }.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[aft_jump_pos] = Instruction::ConditionalJump { to: aft, when: false }.into();

                self.ins.push(Instruction::PopValue.into());
            }
            ast::Stmt::ForLoop { var, start, stop, stmts, .. } => {
                self.append_expr(start, entity);
                self.append_expr(stop, entity);

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater }.into());
                let delta_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::PushNumber { value: 1.0 }.into());
                let positive_delta_end = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                let negative_delta_pos = self.ins.len();
                self.ins.push(Instruction::PushNumber { value: -1.0 }.into());
                let aft_delta = self.ins.len();

                self.ins[delta_jump_pos] = Instruction::ConditionalJump { to: negative_delta_pos, when: true }.into();
                self.ins[positive_delta_end] = Instruction::Jump { to: aft_delta }.into();

                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub }.into());
                self.ins.push(Instruction::UnaryOp { op: UnaryOp::Abs }.into());

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::PushNumber { value: 0.0 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Less }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }

                self.ins.push(Instruction::PushNumber { value: 1.0 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Sub }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 3 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Add }.into());
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();

                for _ in 0..3 {
                    self.ins.push(Instruction::PopValue.into());
                }
            }
            ast::Stmt::ForeachLoop { var, items, stmts, .. } => {
                self.append_expr(items, entity);
                self.ins.push(Instruction::ShallowCopy.into());
                self.ins.push(Instruction::PushNumber { value: 1.0 }.into());

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 2 }.into());
                self.ins.push(Instruction::ListLen.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Greater }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::ListGet.into());
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::PushNumber { value: 1.0 }.into());
                self.ins.push(Instruction::BinaryOp { op: BinaryOp::Add }.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();

                for _ in 0..2 {
                    self.ins.push(Instruction::PopValue.into());
                }
            }
            ast::Stmt::If { condition, then, .. } => {
                self.append_expr(condition, entity);
                let patch_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity);
                }
                let else_pos = self.ins.len();

                self.ins[patch_pos] = Instruction::ConditionalJump { to: else_pos, when: false }.into();
            }
            ast::Stmt::IfElse { condition, then, otherwise, .. } => {
                self.append_expr(condition, entity);
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity);
                }
                let jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                let else_pos = self.ins.len();
                for stmt in otherwise {
                    self.append_stmt(stmt, entity);
                }
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: else_pos, when: false }.into();
                self.ins[jump_pos] = Instruction::Jump { to: aft }.into();
            }
            ast::Stmt::SendLocalMessage { target, msg_type, wait, .. } => match target {
                Some(_) => unimplemented!(),
                None => {
                    self.append_expr(msg_type, entity);
                    self.ins.push(Instruction::Broadcast { wait: *wait }.into());
                }
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmts_ret(&mut self, stmts: &'a [ast::Stmt], entity: Option<&'a ast::Entity>) {
        for stmt in stmts {
            self.append_stmt(stmt, entity);
        }
        self.ins.push(Instruction::PushString { value: "".into() }.into());
        self.ins.push(Instruction::Return.into());
    }
    fn link(mut self, locations: Locations<'a>) -> (ByteCode, Locations<'a>) {
        assert!(self.closure_holes.is_empty());

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
        for (hole_pos, hole_fn, hole_ent) in self.call_holes.iter() {
            let sym = &*hole_fn.trans_name;
            let &(pos, params) = entity_fn_to_info.get(&get_ptr(*hole_ent)).and_then(|tab| tab.get(sym)).or_else(|| global_fn_to_info.get(sym)).unwrap();

            let mut ins_pack = Vec::with_capacity(params.len() + 1);
            for param in params {
                ins_pack.push(Instruction::MetaPush { value: &param.trans_name });
            }
            ins_pack.push(Instruction::Call { pos, params: params.len() });

            self.ins[*hole_pos] = InternalInstruction::Packed(ins_pack);
        }

        self.finalize(locations)
    }
    fn finalize(self, mut locations: Locations<'a>) -> (ByteCode, Locations<'a>) {
        let mut bin = Vec::with_capacity(self.ins.len() * 4);
        let mut final_ins_pos = Vec::with_capacity(self.ins.len());
        let mut pointer_positions = Vec::with_capacity(64);
        for ins in self.ins.iter() {
            final_ins_pos.push(bin.len());
            match ins {
                InternalInstruction::Illegal => unreachable!(),
                InternalInstruction::Packed(vals) => for val in vals {
                    Binary::append(val, &mut bin, &mut pointer_positions);
                }
                InternalInstruction::Valid(val) => Binary::append(val, &mut bin, &mut pointer_positions),
            }
        }

        let mut buf = Vec::with_capacity(mem::size_of::<UsizeRepr>());
        let mut discard = vec![];
        for pos in pointer_positions {
            let ins_pos: usize = Binary::read(&bin, pos).0;
            buf.clear();
            Binary::append(&final_ins_pos[ins_pos], &mut buf, &mut discard);
            debug_assert_eq!(discard.len(), 0);
            debug_assert_eq!(buf.len(), mem::size_of::<UsizeRepr>());
            bin[pos..pos + buf.len()].copy_from_slice(&buf);
        }

        for func in locations.funcs.iter_mut() {
            func.1 = final_ins_pos[func.1];
        }
        for entity in locations.entities.iter_mut() {
            for func in entity.1.funcs.iter_mut() {
                func.1 = final_ins_pos[func.1];
            }
            for script in entity.1.scripts.iter_mut() {
                script.1 = final_ins_pos[script.1];
            }
        }

        (ByteCode(bin.into_boxed_slice()), locations)
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

        while let Some((hole_pos, params, captures, stmts, entity)) = code.closure_holes.pop_front() {
            let pos = code.ins.len();
            code.append_stmts_ret(stmts, entity);

            let mut ins_pack = Vec::with_capacity(params.len() + captures.len() + 1);
            for param in params {
                ins_pack.push(Instruction::MetaPush { value: &param.trans_name });
            }
            for param in captures {
                ins_pack.push(Instruction::MetaPush { value: &param.trans_name });
            }
            ins_pack.push(Instruction::MakeClosure { pos, params: params.len(), captures: captures.len() }.into());

            code.ins[hole_pos] = InternalInstruction::Packed(ins_pack);
        }

        code.link(Locations { funcs, entities })
    }
    /// Get a reference to the raw bytecode.
    pub fn raw(&self) -> &[u8] {
        &self.0
    }
}
