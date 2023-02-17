//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.
//! 
//! To generate bytecode from a project, you can use [`ByteCode::compile`].

use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;
use std::mem;

#[cfg(feature = "std")]
use std::io::{self, Write};

#[cfg(feature = "serde")]
use serde::{Serialize, Deserialize};

use superslice::Ext;
use monostate::MustBeU128;
use num_traits::FromPrimitive;
use bin_pool::BinPool;
use checked_float::{FloatChecker, CheckedFloat};

use crate::*;
use crate::meta::*;

/// Number of bytes to display on each line of a hex dump
#[cfg(feature = "std")]
const BYTES_PER_LINE: usize = 10;

/// Max number of shrinking cycles to apply to variable width encoded values in an output binary
const SHRINK_CYCLES: usize = 3;

#[derive(Debug)]
pub enum CompileError<'a> {
    UnsupportedStmt { kind: &'a ast::StmtKind },
    UnsupportedExpr { kind: &'a ast::ExprKind },
    UnsupportedEvent { kind: &'a ast::HatKind },
    BadKeycode { key: &'a str },
    InvalidLocation { loc: &'a str },
    BadNumber { error: NumberError },
    UndefinedRef,
}
impl From<NumberError> for CompileError<'_> { fn from(error: NumberError) -> Self { Self::BadNumber { error } } }

/// Error type used by [`NumberChecker`].
#[derive(Debug)]
pub enum NumberError {
    Nan,
}

/// [`FloatChecker`] type used for validating a [`Number`].
pub struct NumberChecker;
impl FloatChecker<f64> for NumberChecker {
    type Error = NumberError;
    fn check(value: f64) -> Result<(), Self::Error> {
        if value.is_nan() { return Err(NumberError::Nan); }
        Ok(())
    }
}

/// The type used to represent numbers in the runtime.
pub type Number = CheckedFloat<f64, NumberChecker>;

#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub enum Property {
    XPos, YPos, Heading,

    Visible, Size,

    PenDown, PenSize, PenColor,
    PenColorH, PenColorS, PenColorV, PenColorT,

    Tempo, Volume, Balance,

    ColorH, ColorS, ColorV, ColorT,
    Fisheye, Whirl, Pixelate, Mosaic, Negative,
}
impl Property {
    pub(crate) fn from_effect(kind: &ast::EffectKind) -> Self {
        match kind {
            ast::EffectKind::Color => Property::ColorH,
            ast::EffectKind::Saturation => Property::ColorS,
            ast::EffectKind::Brightness => Property::ColorV,
            ast::EffectKind::Ghost => Property::ColorT,
            ast::EffectKind::Fisheye => Property::Fisheye,
            ast::EffectKind::Whirl => Property::Whirl,
            ast::EffectKind::Pixelate => Property::Pixelate,
            ast::EffectKind::Mosaic => Property::Mosaic,
            ast::EffectKind::Negative => Property::Negative,
        }
    }
}

#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub(crate) enum BinaryOp {
    Add, Sub, Mul, Div, Mod, Pow, Log, Atan2,
    Greater, GreaterEq, Less, LessEq,
    Min, Max,
    SplitBy,
    Range, Random,
    StrGet,
}
#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub(crate) enum UnaryOp {
    Not,
    Abs, Neg,
    Sqrt,
    Round, Floor, Ceil,
    Sin, Cos, Tan,
    Asin, Acos, Atan,
    SplitLetter, SplitWord, SplitTab, SplitCR, SplitLF, SplitCsv, SplitJson,
    StrLen,
    StrGetLast, StrGetRandom,
    UnicodeToChar, CharToUnicode,
}

impl From<BinaryOp> for Instruction<'_> { fn from(op: BinaryOp) -> Self { Self::BinaryOp { op } } }
impl From<UnaryOp> for Instruction<'_> { fn from(op: UnaryOp) -> Self { Self::UnaryOp { op } } }

#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub(crate) enum VariadicOp {
    Add, Mul, Min, Max,
    StrCat,
    MakeList, ListCat,
}
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub(crate) enum VariadicLen {
    Fixed(usize), Dynamic,
}
impl BinaryRead<'_> for VariadicLen {
    fn read(code: &[u8], data: &[u8], start: usize) -> (Self, usize) {
        match BinaryRead::read(code, data, start) {
            (0, aft) => (VariadicLen::Dynamic, aft),
            (x, aft) => (VariadicLen::Fixed(x - 1), aft),
        }
    }
}
impl BinaryWrite for VariadicLen {
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>) {
        let raw = match val { VariadicLen::Fixed(x) => x + 1, VariadicLen::Dynamic => 0 };
        BinaryWrite::append(&raw, code, data, relocate_info)
    }
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
    /// Pushes 1 number value to the value stack. This is a more compact encoding than [`Instruction::PushNumber`].
    PushInt { value: i32 },
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

    /// Consumes 1 value from the value stack and pushes its bool coercion value onto the stack.
    ToBool,
    /// Consumes 1 value from the value stack and pushes its number coercion value onto the stack.
    ToNumber,

    /// Consumes two values, `list` and `item`, from the value stack and constructs a new list starting with `item` and then containing all the values of `list`.
    /// The new list is pushed onto the value stack.
    ListCons,
    /// Consumes one value, `list`, from the value stack and returns a new list containing all the items of `list` except the first.
    /// The new list is pushed onto the value stack.
    ListCdr,

    /// Consumes two values, `list` and `item`, from the value stack and pushes the index of `item` in `list` (or 0 if not present) onto the value stack.
    /// Note that normal Snap!-style (deep) equality is used to test for the presence of the item.
    ListFind,
    /// Consumes two values, `item` and `list`, from the value stack and pushes a boolean representing of `list` contains `item` onto the value stack.
    /// Note that normal Snap!-style (deep) equality is used to test for the presence of the item.
    ListContains,

    /// Consumes 1 value, `list`, from the value stack and pushes a bool representing if the list is empty onto the value stack.
    ListIsEmpty,
    /// Consumes 1 value, `list`, from the value stack and pushes the length of the list onto the value stack.
    ListLength,
    /// Consumes 1 value, `list`, from the value stack and pushes a list containing the dimensions of the list onto the value stack.
    ListDims,
    /// Consumes 1 value, `list`, from the value stack and pushes the number of dimensions of the list onto the value stack.
    ListRank,

    /// Consumes 1 value, `list`, from the value stack and pushes its reversed version onto the value stack.
    ListRev,
    /// Consumes 1 value, `list`, from the value stack and pushes a flattened list containing all the same values in order onto the value stack.
    ListFlatten,
    /// Consumes `len` values from the value stack (in reverse order) representing target dimensions, as well as another value, `list`.
    /// Pushes a new tensor (list) with the desired dimensions by sourcing from `list` (with cyclic repetition) onto the value stack.
    ListReshape { len: VariadicLen },
    /// Consumes `len` values from the value stack (in reverse order) representing source lists.
    /// Pushes a new list representing the cartesian product of the source lists onto the value stack.
    ListCartesianProduct { len: VariadicLen },

    /// Consumes 1 value, `list`, from the value stack and pushes its JSON-encoded string representation onto the value stack.
    ListJson,

    /// Consumes three values, `list`, `index`, and `value, from the value stack and inserts `value` at position `index` of `list`.
    ListInsert,
    /// Consumes two values, `list` and `value`, from the value stack and inserts `value` at the end of `list`.
    ListInsertLast,
    /// Consumes two values, `list` and `value`, from the values stack and inserts `value` at a random position in the list.
    ListInsertRandom,

    /// Consumes two values, `list` and `index`, from the value stack and pushes the value `list[index]` onto the value stack.
    ListGet,
    /// Consumes 1 value, `list`, from the value stack and pushes the last item in the list onto the value stack.
    ListGetLast,
    /// Consumes 1 value, `list`, from the value stack and pushes a random item from the list onto the value stack.
    ListGetRandom,

    /// Consumes three values, `value`, `list`, and `index`, from the value stack and assigns `list[index] = value`.
    ListAssign,
    /// Consumes two values, `value` and `list`, from the value stack and assigns `value` to the last position in the list.
    ListAssignLast,
    /// Consumes two values, `value` and `list`, from the value stack and assigns `value` to a random position in the list.
    ListAssignRandom,

    /// Consumes two values, `list` and `index`, from the value stack and deletes item `index` from `list`.
    ListRemove,
    /// Consumes one value, `list`, from the value stack and deletes the last item from it.
    ListRemoveLast,
    /// Consumes one value, `list`, from the value stack and deletes all elements from it.
    ListRemoveAll,

    /// Consumes one value, `list`, from the value stack.
    /// If the list is empty, jumps to the specified position, otherwise pops the first value from the list and pushes it to the value stack.
    ListPopFirstOrElse { goto: usize },

    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the value `f(a, b)` onto the value stack.
    BinaryOp { op: BinaryOp },
    /// Consumes `len` values from the value stack (in reverse order) and combines them into one value based on `op`.
    VariadicOp { op: VariadicOp, len: VariadicLen },
    /// Consumes 2 values, `b` and `a`, from the value stack, and pushes the (boolean) value `a == b` onto the value stack,
    /// where `==` is a deep comparison allowing type conversions.
    /// This is similar to [`Instruction::BinaryOp`] except that it is not vectorized and always returns a single (scalar) boolean value.
    Eq { negate: bool },
    /// Equivalent to [`Instruction::Eq`] but uses reference equality.
    RefEq,
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
    /// Pops a return address from the call stack and jumps to it.
    /// The return value is left on the top of the value stack.
    /// If the call stack is empty, this instead terminates the process
    /// with the reported value being the (only) value remaining in the value stack.
    Return,

    /// Pushes a new error handler onto the handler stack.
    PushHandler { pos: usize, var: &'a str },
    /// Pops an error handler from the handler stack.
    PopHandler,
    /// Consumes 1 value, msg, from the value stack and converts it into a hard error.
    Throw,

    /// Consumes `args` values from the meta stack and value stack, representing arguments.
    /// Then calls the given RPC, awaits the result, and pushes the return value onto the value stack.
    CallRpc { service: &'a str, rpc: &'a str, args: usize },
    /// Pushes the last RPC error message onto the value stack.
    PushRpcError,

    /// Consumes `len` values (in reverse order) representing arguments to a system call.
    /// Consumes 1 addition value representing the system call name.
    /// Invokes the given syscall, awaits the result, and pushes the result onto the value stack.
    Syscall { len: VariadicLen },
    /// Pushes the last syscall error message onto the value stack.
    PushSyscallError,

    /// Consumes 1 value from the value stack, `msg_type`, and broadcasts a message to all scripts.
    /// The `wait` flag can be set to denote that the broadcasting script should wait until all receiving scripts have terminated.
    Broadcast { wait: bool },

    /// Consumes 1 value `msg` from the value stack and prints it to the stored printer.
    Print,
    /// Consumes 1 value, `prompt`, from the value stack and uses it as a query to get input from the user.
    /// The result is NOT stored on the value stack, and instead [`Instruction::PushAnswer`] must be used to retrieve the result.
    Ask,
    /// Pushes the most recent answer from an execution of [`Instruction::Ask`] onto the value stack, or empty string if no question has yet been asked.
    /// Note that the most recent answer is a process-local value, so this cannot retrieve the answer to a question asked by another process.
    PushAnswer,

    /// Resets the process-local timer value to the current system time.
    ResetTimer,
    /// Gets the current timer value (in seconds) and pushes its value onto the value stack.
    PushTimer,
    /// Consumes one value, `secs`, from the value stack and asynchronously waits for that amount of time to elapse.
    /// Non-positive sleep times are ignored, but still generate a yield point.
    Sleep,

    /// Consumes 1 value, `target` from the value stack, which is either a single or a list of targets.
    /// Then consumes `values` values from the value stack and meta stack, representing the fields of a message packet to send to (each) target.
    /// The `expect_reply` flag denotes if this is a blocking operation that awaits a response from the target(s).
    /// If `expect_reply` is true, the reply value (or empty string on timeout) is pushed onto the value stack.
    SendNetworkMessage { msg_type: &'a str, values: usize, expect_reply: bool },
    /// Consumes 1 value, `value`, from the value stack and sends it as the response to a received message.
    /// It is not an error to reply to a message that was not expecting a reply, in which case the value is simply discarded.
    SendNetworkReply,

    /// Pushes the current value of a property onto the value stack.
    PushProperty { prop: Property },
    /// Consumes 1 value, `value`, and assigns it to the specified property.
    SetProperty { prop: Property },
    /// Consumes 1 value, `delta`, and adds its value to the specified property.
    ChangeProperty { prop: Property },

    /// Pushes a reference to the current costume onto the value stack.
    PushCostume,
    /// Pushes the current costume number onto the value stack (or zero if using no costume or a non-static costume for the given entity).
    PushCostumeNumber,
    /// Pushes a shallow copy of the entity's list of static costumes onto the value stack.
    PushCostumeList,
    /// Consumes 1 value, `costume`, from the value stack and assigns it as the current costume.
    /// This can be an image or the name of a static costume on the entity.
    /// Empty string can be used to remove the current costume.
    SetCostume,
    /// If using a static costume, advances to the next costume (if one exists).
    /// If using dynamic costumes or no costume, does nothing.
    NextCostume,

    /// Clears all graphic effects on the entity.
    ClearEffects,

    /// Consumes 1 value, `dist`, and asynchronously moves the entity forward by that distance (or backwards if negative).
    Forward,
}

/// A key from the keyboard.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyCode {
    /// A normal character key, such as a letter, number, or special symbol.
    Char(char),
    /// The up arrow key.
    Up,
    /// The down arrow key.
    Down,
    /// The left arrow key.
    Left,
    /// The right arrow key.
    Right,
    /// Either enter/return key.
    Enter,
}

/// An event type which can be set to trigger the execution of a script.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone)]
pub enum Event {
    /// Fire when a green flag click event is issued.
    OnFlag,
    /// Fire when a message is received locally (Control message blocks).
    LocalMessage { msg_type: String },
    /// Fire when a message is received over the network (Network message blocks).
    NetworkMessage { msg_type: String, fields: Vec<String> },
    /// Fire when a key is pressed. [`None`] is used to denote any key press.
    OnKey { key_filter: Option<KeyCode> },
}

pub(crate) enum RelocateInfo {
    Code { code_addr: usize },
    Data { code_addr: usize },
}

pub(crate) trait BinaryRead<'a>: Sized {
    /// Reads a value from `src` starting at `start`.
    /// Returns the read value and the position of the first byte after the read segment.
    fn read(code: &'a [u8], data: &'a [u8], start: usize) -> (Self, usize);
}
trait BinaryWrite: Sized {
    /// Appends a binary representation of the value to the given buffers.
    /// And address/relocation information that is written will be stored in `relocate_info` in strictly ascending order of code address.
    /// This function is not intended for use outside of [`ByteCode`] linking.
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>);
}

impl BinaryRead<'_> for u8 { fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) { (code[start], start + 1) } }
impl BinaryWrite for u8 { fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) { code.push(*val) } }

impl BinaryRead<'_> for Property { fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) { (Self::from_u8(code[start]).unwrap(), start + 1) } }
impl BinaryWrite for Property {
    fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        code.push((*val) as u8)
    }
}

impl BinaryRead<'_> for BinaryOp { fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) { (Self::from_u8(code[start]).unwrap(), start + 1) } }
impl BinaryWrite for BinaryOp {
    fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        code.push((*val) as u8);
    }
}

impl BinaryRead<'_> for UnaryOp { fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) { (Self::from_u8(code[start]).unwrap(), start + 1) } }
impl BinaryWrite for UnaryOp {
    fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        code.push((*val) as u8)
    }
}

impl BinaryRead<'_> for VariadicOp { fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) { (Self::from_u8(code[start]).unwrap(), start + 1) } }
impl BinaryWrite for VariadicOp {
    fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) {
        debug_assert_eq!(mem::size_of::<Self>(), 1);
        code.push((*val) as u8);
    }
}

fn encode_u64(mut val: u64, out: &mut Vec<u8>, bytes: Option<usize>) {
    let mut blocks = ((64 - val.leading_zeros() as usize + 6) / 7).max(1);
    if let Some(bytes) = bytes {
        debug_assert!(bytes >= blocks);
        blocks = bytes;
    }

    debug_assert!((1..=10).contains(&blocks));
    for _ in 1..blocks {
        out.push((val as u8 & 0x7f) | 0x80);
        val >>= 7;
    }
    debug_assert!(val <= 0x7f);
    out.push(val as u8);
}
fn decode_u64(data: &[u8], start: usize) -> (u64, usize) {
    let (mut val, mut aft) = (0, start);
    for &b in &data[start..] {
        aft += 1;
        if b & 0x80 == 0 { break }
    }
    for &b in data[start..aft].iter().rev() {
        val = (val << 7) | (b & 0x7f) as u64;
    }
    (val, aft)
}

// encodes values as a sequence of bytes of form [1: next][7: bits] in little-endian order.
// if `relocate_info` is provided to `append`, expanded mode is used, which encodes the value with the maximum of 10 bytes.
impl BinaryRead<'_> for u64 {
    fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) {
        decode_u64(code, start)
    }
}
impl BinaryWrite for u64 {
    fn append(val: &Self, code: &mut Vec<u8>, _: &mut BinPool, _: &mut Vec<RelocateInfo>) {
        encode_u64(*val, code, None)
    }
}

#[test]
fn test_binary_u64() {
    let mut buf = vec![];
    let tests = [
        (0,                 [0x00].as_slice(),                                                       [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (1,                 [0x01].as_slice(),                                                       [0x81, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (2,                 [0x02].as_slice(),                                                       [0x82, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (0x53,              [0x53].as_slice(),                                                       [0xd3, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (0x7f,              [0x7f].as_slice(),                                                       [0xff, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (0x80,              [0x80, 0x01].as_slice(),                                                 [0x80, 0x81, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00].as_slice()),
        (0x347462356236574, [0xf4, 0xca, 0x8d, 0xb1, 0xb5, 0xc4, 0xd1, 0xa3, 0x03].as_slice(),       [0xf4, 0xca, 0x8d, 0xb1, 0xb5, 0xc4, 0xd1, 0xa3, 0x83, 0x00].as_slice()),
        (u64::MAX >> 1,     [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f].as_slice(),       [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00].as_slice()),
        (u64::MAX,          [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01].as_slice(), [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01].as_slice()),
    ];
    for (v, expect_small, expect_large) in tests {
        for (expect, expanded) in [(expect_small, false), (expect_large, true)] {
            for prefix_bytes in 0..8 {
                buf.clear();
                buf.extend(std::iter::once(0x53).cycle().take(prefix_bytes));
                encode_u64(v, &mut buf, if expanded { Some(10) } else { None });
                assert!(buf[..prefix_bytes].iter().all(|&x| x == 0x53));
                assert_eq!(&buf[prefix_bytes..], expect);
                buf.extend(std::iter::once(0xff).cycle().take(8));
                let (back, aft) = <u64 as BinaryRead>::read(&buf, &[], prefix_bytes);
                assert_eq!(back, v);
                assert_eq!(aft, prefix_bytes + expect.len());
            }
        }
    }
}

// stores the value as u64 by shifting up by one bit and storing a bitwise-not flag in the low order bit.
// the u64 value is then stored using the variable width algorithm for u64.
impl BinaryRead<'_> for i32 {
    fn read(code: &[u8], data: &[u8], start: usize) -> (Self, usize) {
        let (raw, aft) = <u64 as BinaryRead>::read(code, data, start);
        let v = (raw >> 1) as u32;
        (if raw & 1 == 0 { v } else { !v } as i32, aft)
    }
}
impl BinaryWrite for i32 {
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>) {
        let v: u64 = ((*val) as u64) << 1;
        BinaryWrite::append(&if v & 0x8000000000000000 == 0 { v } else { !v }, code, data, relocate_info)
    }
}

#[test]
fn test_binary_i32() {
    let mut buf = vec![];
    let mut discard = (BinPool::new(), vec![]);
    let tests = [
        (0,         [0x00].as_slice()),
        (-1,        [0x01].as_slice()),
        (1,         [0x02].as_slice()),
        (-2,        [0x03].as_slice()),
        (2,         [0x04].as_slice()),
        (0x543245,  [0x8a, 0xc9, 0xa1, 0x05].as_slice()),
        (-0x376224, [0xc7, 0x88, 0xbb, 0x03].as_slice()),
        (-i32::MAX, [0xfd, 0xff, 0xff, 0xff, 0x0f].as_slice()),
        (i32::MAX,  [0xfe, 0xff, 0xff, 0xff, 0x0f].as_slice()),
        (i32::MIN,  [0xff, 0xff, 0xff, 0xff, 0x0f].as_slice()),
    ];
    for (v, expect) in tests {
        for prefix_bytes in 0..8 {
            buf.clear();
            buf.extend(std::iter::once(0x53).cycle().take(prefix_bytes));
            BinaryWrite::append(&v, &mut buf, &mut discard.0, &mut discard.1);
            assert_eq!(discard.0.len(), 0);
            assert_eq!(discard.1.len(), 0);
            assert!(buf[..prefix_bytes].iter().all(|&x| x == 0x53));
            assert_eq!(&buf[prefix_bytes..], expect);
            buf.extend(std::iter::once(0xff).cycle().take(8));
            let (back, aft) = <i32 as BinaryRead>::read(&buf, &[], prefix_bytes);
            assert_eq!(back, v);
            assert_eq!(aft, prefix_bytes + expect.len());
        }
    }
}

impl BinaryRead<'_> for f64 {
    fn read(code: &[u8], data: &[u8], start: usize) -> (Self, usize) {
        let (v, aft) = <u64 as BinaryRead>::read(code, data, start);
        (f64::from_bits(v.swap_bytes()), aft)
    }
}
impl BinaryWrite for f64 {
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>) {
        BinaryWrite::append(&val.to_bits().swap_bytes(), code, data, relocate_info)
    }
}

impl BinaryRead<'_> for usize {
    fn read(code: &[u8], data: &[u8], start: usize) -> (Self, usize) {
        let (v, aft) = <u64 as BinaryRead>::read(code, data, start);
        debug_assert!(v <= usize::MAX as u64);
        (v as usize, aft)
    }
}
impl BinaryWrite for usize {
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>) {
        BinaryWrite::append(&(*val as u64), code, data, relocate_info)
    }
}

impl<'a> BinaryRead<'a> for &'a str {
    fn read(code: &'a [u8], data: &'a [u8], start: usize) -> (Self, usize) {
        let (data_pos, aft) = <usize as BinaryRead>::read(code, data, start);
        let (data_len, aft) = <usize as BinaryRead>::read(code, data, aft);
        (std::str::from_utf8(&data[data_pos..data_pos + data_len]).unwrap(), aft)
    }
}

impl<'a> BinaryRead<'a> for Instruction<'a> {
    fn read(code: &'a [u8], data: &'a [u8], start: usize) -> (Self, usize) {
        macro_rules! read_prefixed {
            (Instruction::$root:ident) => {
                (Instruction::$root, start + 1)
            };
            (Instruction::$root:ident { $($tt:tt)* } $(: $($vals:ident),+$(,)? )?) => {{
                #[allow(unused_mut)]
                let mut parsing_stop = start + 1;
                $($(let $vals = {
                    let x = BinaryRead::read(code, data, parsing_stop);
                    parsing_stop = x.1;
                    x.0
                };)*)?
                (Instruction::$root { $($tt)* $($($vals),+ )? }, parsing_stop)
            }};
        }
        match code[start] {
            0 => read_prefixed!(Instruction::Yield),
            1 => read_prefixed!(Instruction::WarpStart),
            2 => read_prefixed!(Instruction::WarpStop),

            3 => read_prefixed!(Instruction::PushBool { value: false }),
            4 => read_prefixed!(Instruction::PushBool { value: true }),

            5 => read_prefixed!(Instruction::PushInt {} : value),
            6 => read_prefixed!(Instruction::PushNumber {} : value),

            7 => read_prefixed!(Instruction::PushString { value: "" }),
            8 => read_prefixed!(Instruction::PushString {} : value),

            9 => read_prefixed!(Instruction::PushVariable {} : var),
            10 => read_prefixed!(Instruction::PopValue),

            11 => read_prefixed!(Instruction::DupeValue {} : top_index),
            12 => read_prefixed!(Instruction::SwapValues {} : top_index_1, top_index_2),

            13 => read_prefixed!(Instruction::ToBool),
            14 => read_prefixed!(Instruction::ToNumber),

            15 => read_prefixed!(Instruction::ListCons),
            16 => read_prefixed!(Instruction::ListCdr),

            17 => read_prefixed!(Instruction::ListFind),
            18 => read_prefixed!(Instruction::ListContains),

            19 => read_prefixed!(Instruction::ListIsEmpty),
            20 => read_prefixed!(Instruction::ListLength),
            21 => read_prefixed!(Instruction::ListDims),
            22 => read_prefixed!(Instruction::ListRank),

            23 => read_prefixed!(Instruction::ListRev),
            24 => read_prefixed!(Instruction::ListFlatten),
            25 => read_prefixed!(Instruction::ListReshape {} : len),
            26 => read_prefixed!(Instruction::ListCartesianProduct {} : len),

            27 => read_prefixed!(Instruction::ListJson),

            28 => read_prefixed!(Instruction::ListInsert),
            29 => read_prefixed!(Instruction::ListInsertLast),
            30 => read_prefixed!(Instruction::ListInsertRandom),

            31 => read_prefixed!(Instruction::ListGet),
            32 => read_prefixed!(Instruction::ListGetLast),
            33 => read_prefixed!(Instruction::ListGetRandom),

            34 => read_prefixed!(Instruction::ListAssign),
            35 => read_prefixed!(Instruction::ListAssignLast),
            36 => read_prefixed!(Instruction::ListAssignRandom),

            37 => read_prefixed!(Instruction::ListRemove),
            38 => read_prefixed!(Instruction::ListRemoveLast),
            39 => read_prefixed!(Instruction::ListRemoveAll),

            40 => read_prefixed!(Instruction::ListPopFirstOrElse {} : goto),

            41 => read_prefixed!(Instruction::Eq { negate: false }),
            42 => read_prefixed!(Instruction::Eq { negate: true }),
            43 => read_prefixed!(Instruction::RefEq),

            44 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Add }),
            45 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Sub }),
            46 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Mul }),
            47 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Div }),
            48 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Greater }),
            49 => read_prefixed!(Instruction::BinaryOp { op: BinaryOp::Less }),
            50 => read_prefixed!(Instruction::BinaryOp {} : op),

            51 => read_prefixed!(Instruction::VariadicOp { op: VariadicOp::Add, } : len),
            52 => read_prefixed!(Instruction::VariadicOp { op: VariadicOp::Mul, } : len),
            53 => read_prefixed!(Instruction::VariadicOp { op: VariadicOp::StrCat, } : len),
            54 => read_prefixed!(Instruction::VariadicOp { op: VariadicOp::MakeList, } : len),
            55 => read_prefixed!(Instruction::VariadicOp {} : op, len),

            56 => read_prefixed!(Instruction::UnaryOp { op: UnaryOp::Not }),
            57 => read_prefixed!(Instruction::UnaryOp { op: UnaryOp::Round }),
            58 => read_prefixed!(Instruction::UnaryOp {} : op),

            59 => read_prefixed!(Instruction::DeclareLocal {} : var),
            60 => read_prefixed!(Instruction::Assign {} : var),

            61 => read_prefixed!(Instruction::BinaryOpAssign { op: BinaryOp::Add, } : var),
            62 => read_prefixed!(Instruction::BinaryOpAssign {} : var, op),

            63 => read_prefixed!(Instruction::Jump {} : to),
            64 => read_prefixed!(Instruction::ConditionalJump { when: false, } : to),
            65 => read_prefixed!(Instruction::ConditionalJump { when: true, } : to),

            66 => read_prefixed!(Instruction::MetaPush {} : value),

            67 => read_prefixed!(Instruction::Call {} : pos, params),
            68 => read_prefixed!(Instruction::MakeClosure {} : pos, params, captures),
            69 => read_prefixed!(Instruction::CallClosure {} : args),
            70 => read_prefixed!(Instruction::Return),

            71 => read_prefixed!(Instruction::PushHandler {} : pos, var),
            72 => read_prefixed!(Instruction::PopHandler),
            73 => read_prefixed!(Instruction::Throw),

            74 => read_prefixed!(Instruction::CallRpc {} : service, rpc, args),
            75 => read_prefixed!(Instruction::PushRpcError),

            76 => read_prefixed!(Instruction::Syscall {} : len),
            77 => read_prefixed!(Instruction::PushSyscallError),

            78 => read_prefixed!(Instruction::Broadcast { wait: false }),
            79 => read_prefixed!(Instruction::Broadcast { wait: true }),

            80 => read_prefixed!(Instruction::Print),
            81 => read_prefixed!(Instruction::Ask),
            82 => read_prefixed!(Instruction::PushAnswer),

            83 => read_prefixed!(Instruction::ResetTimer),
            84 => read_prefixed!(Instruction::PushTimer),
            85 => read_prefixed!(Instruction::Sleep),

            86 => read_prefixed!(Instruction::SendNetworkMessage { expect_reply: false, } : msg_type, values),
            87 => read_prefixed!(Instruction::SendNetworkMessage { expect_reply: true, } : msg_type, values),
            88 => read_prefixed!(Instruction::SendNetworkReply),

            89 => read_prefixed!(Instruction::PushProperty {} : prop),
            90 => read_prefixed!(Instruction::SetProperty {} : prop),
            91 => read_prefixed!(Instruction::ChangeProperty {} : prop),

            92 => read_prefixed!(Instruction::PushCostume),
            93 => read_prefixed!(Instruction::PushCostumeNumber),
            94 => read_prefixed!(Instruction::PushCostumeList),
            95 => read_prefixed!(Instruction::SetCostume),
            96 => read_prefixed!(Instruction::NextCostume),

            97 => read_prefixed!(Instruction::ClearEffects),

            98 => read_prefixed!(Instruction::Forward),

            _ => unreachable!(),
        }
    }
}
impl BinaryWrite for Instruction<'_> {
    fn append(val: &Self, code: &mut Vec<u8>, data: &mut BinPool, relocate_info: &mut Vec<RelocateInfo>) {
        macro_rules! append_prefixed {
            ($op:literal $(: $($($vals:ident)+),+)?) => {{
                code.push($op);
                $($( append_prefixed!(@single $($vals)+); )*)?
            }};
            (@single move $val:ident) => {{
                relocate_info.push(RelocateInfo::Code { code_addr: code.len() });
                encode_u64(*$val as u64, code, Some(10));
            }};
            (@single move str $val:ident) => {{
                let pool_index = data.add($val.as_bytes());
                relocate_info.push(RelocateInfo::Data { code_addr: code.len() });
                encode_u64(pool_index as u64, code, Some(10));
                BinaryWrite::append(&$val.len(), code, data, relocate_info);
            }};
            (@single $val:ident) => { BinaryWrite::append($val, code, data, relocate_info) };
        }
        match val {
            Instruction::Yield => append_prefixed!(0),
            Instruction::WarpStart => append_prefixed!(1),
            Instruction::WarpStop => append_prefixed!(2),

            Instruction::PushBool { value: false } => append_prefixed!(3),
            Instruction::PushBool { value: true } => append_prefixed!(4),

            Instruction::PushInt { value } => append_prefixed!(5: value),
            Instruction::PushNumber { value } => append_prefixed!(6: value),

            Instruction::PushString { value: "" } => append_prefixed!(7),
            Instruction::PushString { value } => append_prefixed!(8: move str value),

            Instruction::PushVariable { var } => append_prefixed!(9: move str var),
            Instruction::PopValue => append_prefixed!(10),

            Instruction::DupeValue { top_index } => append_prefixed!(11: top_index),
            Instruction::SwapValues { top_index_1, top_index_2 } => append_prefixed!(12: top_index_1, top_index_2),

            Instruction::ToBool => append_prefixed!(13),
            Instruction::ToNumber => append_prefixed!(14),

            Instruction::ListCons => append_prefixed!(15),
            Instruction::ListCdr => append_prefixed!(16),

            Instruction::ListFind => append_prefixed!(17),
            Instruction::ListContains => append_prefixed!(18),

            Instruction::ListIsEmpty => append_prefixed!(19),
            Instruction::ListLength => append_prefixed!(20),
            Instruction::ListDims => append_prefixed!(21),
            Instruction::ListRank => append_prefixed!(22),

            Instruction::ListRev => append_prefixed!(23),
            Instruction::ListFlatten => append_prefixed!(24),
            Instruction::ListReshape { len } => append_prefixed!(25: len),
            Instruction::ListCartesianProduct { len } => append_prefixed!(26: len),

            Instruction::ListJson => append_prefixed!(27),

            Instruction::ListInsert => append_prefixed!(28),
            Instruction::ListInsertLast => append_prefixed!(29),
            Instruction::ListInsertRandom => append_prefixed!(30),

            Instruction::ListGet => append_prefixed!(31),
            Instruction::ListGetLast => append_prefixed!(32),
            Instruction::ListGetRandom => append_prefixed!(33),

            Instruction::ListAssign => append_prefixed!(34),
            Instruction::ListAssignLast => append_prefixed!(35),
            Instruction::ListAssignRandom => append_prefixed!(36),

            Instruction::ListRemove => append_prefixed!(37),
            Instruction::ListRemoveLast => append_prefixed!(38),
            Instruction::ListRemoveAll => append_prefixed!(39),

            Instruction::ListPopFirstOrElse { goto } => append_prefixed!(40: move goto),

            Instruction::Eq { negate: false } => append_prefixed!(41),
            Instruction::Eq { negate: true } => append_prefixed!(42),
            Instruction::RefEq => append_prefixed!(43),

            Instruction::BinaryOp { op: BinaryOp::Add } => append_prefixed!(44),
            Instruction::BinaryOp { op: BinaryOp::Sub } => append_prefixed!(45),
            Instruction::BinaryOp { op: BinaryOp::Mul } => append_prefixed!(46),
            Instruction::BinaryOp { op: BinaryOp::Div } => append_prefixed!(47),
            Instruction::BinaryOp { op: BinaryOp::Greater } => append_prefixed!(48),
            Instruction::BinaryOp { op: BinaryOp::Less } => append_prefixed!(49),
            Instruction::BinaryOp { op } => append_prefixed!(50: op),

            Instruction::VariadicOp { op: VariadicOp::Add, len } => append_prefixed!(51: len),
            Instruction::VariadicOp { op: VariadicOp::Mul, len } => append_prefixed!(52: len),
            Instruction::VariadicOp { op: VariadicOp::StrCat, len } => append_prefixed!(53: len),
            Instruction::VariadicOp { op: VariadicOp::MakeList, len } => append_prefixed!(54: len),
            Instruction::VariadicOp { op, len } => append_prefixed!(55: op, len),

            Instruction::UnaryOp { op: UnaryOp::Not } => append_prefixed!(56),
            Instruction::UnaryOp { op: UnaryOp::Round } => append_prefixed!(57),
            Instruction::UnaryOp { op } => append_prefixed!(58: op),

            Instruction::DeclareLocal { var } => append_prefixed!(59: move str var),
            Instruction::Assign { var } => append_prefixed!(60: move str var),

            Instruction::BinaryOpAssign { var, op: BinaryOp::Add } => append_prefixed!(61: move str var),
            Instruction::BinaryOpAssign { var, op } => append_prefixed!(62: move str var, op),

            Instruction::Jump { to } => append_prefixed!(63: move to),
            Instruction::ConditionalJump { to, when: false } => append_prefixed!(64: move to),
            Instruction::ConditionalJump { to, when: true } => append_prefixed!(65: move to),

            Instruction::MetaPush { value } => append_prefixed!(66: move str value),

            Instruction::Call { pos, params } => append_prefixed!(67: move pos, params),
            Instruction::MakeClosure { pos, params, captures } => append_prefixed!(68: move pos, params, captures),
            Instruction::CallClosure { args } => append_prefixed!(69: args),
            Instruction::Return => append_prefixed!(70),

            Instruction::PushHandler { pos, var } => append_prefixed!(71: move pos, move str var),
            Instruction::PopHandler => append_prefixed!(72),
            Instruction::Throw => append_prefixed!(73),

            Instruction::CallRpc { service, rpc, args } => append_prefixed!(74: move str service, move str rpc, args),
            Instruction::PushRpcError => append_prefixed!(75),

            Instruction::Syscall { len } => append_prefixed!(76: len),
            Instruction::PushSyscallError => append_prefixed!(77),

            Instruction::Broadcast { wait: false } => append_prefixed!(78),
            Instruction::Broadcast { wait: true } => append_prefixed!(79),

            Instruction::Print => append_prefixed!(80),
            Instruction::Ask => append_prefixed!(81),
            Instruction::PushAnswer => append_prefixed!(82),

            Instruction::ResetTimer => append_prefixed!(83),
            Instruction::PushTimer => append_prefixed!(84),
            Instruction::Sleep => append_prefixed!(85),

            Instruction::SendNetworkMessage { msg_type, values, expect_reply: false } => append_prefixed!(86: move str msg_type, values),
            Instruction::SendNetworkMessage { msg_type, values, expect_reply: true } => append_prefixed!(87: move str msg_type, values),
            Instruction::SendNetworkReply => append_prefixed!(88),

            Instruction::PushProperty { prop } => append_prefixed!(89: prop),
            Instruction::SetProperty { prop } => append_prefixed!(90: prop),
            Instruction::ChangeProperty { prop } => append_prefixed!(91: prop),

            Instruction::PushCostume => append_prefixed!(92),
            Instruction::PushCostumeNumber => append_prefixed!(93),
            Instruction::PushCostumeList => append_prefixed!(94),
            Instruction::SetCostume => append_prefixed!(95),
            Instruction::NextCostume => append_prefixed!(96),

            Instruction::ClearEffects => append_prefixed!(97),

            Instruction::Forward => append_prefixed!(98),
        }
    }
}

/// An interpreter-ready sequence of instructions.
///
/// [`Process`](crate::process::Process) is an execution primitive that can be used to execute generated [`ByteCode`].
///
/// Generated [`ByteCode`] is highly optimized for size and sees frequent breaking changes.
/// Because of this, there is currently no support for touching the actual bytecode itself.
/// If you wish to view the generated bytecode, you may use the [`ByteCode::dump_code`] and [`ByteCode::dump_data`] utilities,
/// a wrapper for which is included in the standard `netsblox-vm` [`cli`](crate::cli).
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ByteCode {
    #[allow(dead_code)] tag: MustBeU128<FINGERPRINT>,

    pub(crate) code: Box<[u8]>,
    pub(crate) data: Box<[u8]>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub(crate) enum InitValue {
    Bool(bool),
    Number(Number),
    Ref(usize),
}
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub(crate) enum RefValue {
    List(Vec<InitValue>),
    Image(Vec<u8>),
    String(String),
}
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub(crate) struct EntityInitInfo {
    pub(crate) name: String,
    pub(crate) fields: Vec<(String, InitValue)>,
    pub(crate) costumes: Vec<(String, InitValue)>,
    pub(crate) scripts: Vec<(Event, usize)>,

    pub(crate) visible: bool,
    pub(crate) active_costume: Option<usize>,
    pub(crate) size: Number,
    pub(crate) color: (u8, u8, u8, u8),
    pub(crate) pos: (Number, Number),
    pub(crate) heading: Number,
}
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct InitInfo {
    #[allow(dead_code)] tag: MustBeU128<FINGERPRINT>,

    pub(crate) proj_name: String,
    pub(crate) ref_values: Vec<RefValue>,
    pub(crate) globals: Vec<(String, InitValue)>,
    pub(crate) entities: Vec<EntityInitInfo>,
}

/// Location info in a [`ByteCode`] object for a particular entity.
pub struct EntityScriptInfo<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub scripts: Vec<(&'a ast::Script, usize)>,
}
/// Location info in a [`ByteCode`] object.
pub struct ScriptInfo<'a> {
    pub funcs: Vec<(&'a ast::Function, usize)>,
    pub entities: Vec<(&'a ast::Entity, EntityScriptInfo<'a>)>,
}

/// Location lookup table from bytecode address to original AST location.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Locations {
    #[allow(dead_code)] tag: MustBeU128<FINGERPRINT>,

    prefix: String,
    base_token: usize,
    token_data: Vec<u8>,
    locs: Vec<(usize, usize)>,
}
impl Locations {
    fn condense<'a>(orig_locs: BTreeMap<usize, &'a str>) -> Result<Self, CompileError<'a>> {
        if orig_locs.is_empty() {
            return Ok(Self {
                tag: Default::default(),
                prefix: String::new(),
                base_token: 0,
                token_data: Default::default(),
                locs: Default::default(),
            });
        }

        let prefix = {
            let loc = *orig_locs.values().next().unwrap();
            match loc.find('_') {
                Some(x) => loc[..x].to_owned(),
                None => return Err(CompileError::InvalidLocation { loc }),
            }
        };

        let mut token_map = Vec::with_capacity(orig_locs.len());
        for (&pos, &loc) in orig_locs.iter() {
            if !loc.starts_with(&prefix) { return Err(CompileError::InvalidLocation { loc }) }
            debug_assert!(loc[prefix.len()..].starts_with('_'));

            let mut tokens = vec![];
            for token in loc[prefix.len() + 1..].split('_') {
                let v: usize = match token.parse() {
                    Ok(x) => x,
                    Err(_) => return Err(CompileError::InvalidLocation { loc }),
                };
                if v.to_string() != token {
                    return Err(CompileError::InvalidLocation { loc });
                }
                tokens.push(v);
            }
            token_map.push((pos, tokens));
        }

        let base_token = token_map.iter().flat_map(|x| &x.1).copied().min().unwrap_or(0);

        let mut token_data = Vec::with_capacity(token_map.len());
        let mut locs = Vec::with_capacity(token_map.len());
        for (pos, toks) in token_map {
            locs.push((pos, token_data.len()));
            for tok in toks {
                encode_u64((tok - base_token + 1) as u64, &mut token_data, None);
            }
            encode_u64(0, &mut token_data, None); // null terminator
        }

        let res = Self { tag: Default::default(), prefix, base_token, token_data, locs };

        #[cfg(test)]
        {
            for pos in 0..orig_locs.iter().last().unwrap().0 + 16 {
                let expected = orig_locs.range(pos + 1..).next().map(|x| *x.1);
                let actual = res.lookup(pos);
                assert_eq!(expected, actual.as_deref());
            }
        }

        Ok(res)
    }

    /// Looks up a bytecode position and returns the most local block location provided by the ast.
    /// If the ast came from a standard NetsBlox XML file, this is the collab id of the looked up bytecode address.
    /// In other cases, this could be some other localization mechanism for error reporting (e.g., line number and column).
    ///
    /// Note that it is possible for blocks to not have location information,
    /// hence returning the most local location that was provided in the ast.
    pub fn lookup(&self, bytecode_pos: usize) -> Option<String> {
        let mut start = {
            let p = self.locs.lower_bound_by_key(&(bytecode_pos + 1), |x| x.0);
            debug_assert!(p <= self.locs.len());
            self.locs.get(p)?.1
        };

        let mut res = self.prefix.clone();
        loop {
            let (v, aft) = decode_u64(&self.token_data, start);
            if v == 0 { return Some(res) }

            start = aft;
            res.push('_');
            res.push_str(&(v as usize - 1 + self.base_token).to_string());
        }
    }
}

#[derive(Default)]
struct ByteCodeBuilder<'a> {
    ins: Vec<InternalInstruction<'a>>,
    call_holes: Vec<(usize, &'a ast::FnRef, Option<&'a ast::Entity>)>, // (hole pos, function, entity)
    closure_holes: VecDeque<(usize, &'a [ast::VariableDef], &'a [ast::VariableRef], &'a [ast::Stmt], Option<&'a ast::Entity>)>, // (hole pos, params, captures, stmts, entity)
    ins_locations: BTreeMap<usize, &'a str>,
}
impl<'a> ByteCodeBuilder<'a> {
    fn append_simple_ins(&mut self, entity: Option<&'a ast::Entity>, values: &[&'a ast::Expr], op: Instruction<'a>) -> Result<(), CompileError<'a>> {
        for value in values {
            self.append_expr(value, entity)?;
        }
        self.ins.push(op.into());
        Ok(())
    }
    fn append_variadic_op(&mut self, entity: Option<&'a ast::Entity>, varargs: &'a ast::VariadicInput, op: VariadicOp) -> Result<(), CompileError<'a>> {
        Ok(match varargs {
            ast::VariadicInput::Fixed(values) => {
                for value in values {
                    self.append_expr(value, entity)?;
                }
                self.ins.push(Instruction::VariadicOp { op, len: VariadicLen::Fixed(values.len()) }.into());
            }
            ast::VariadicInput::VarArgs(values) => {
                self.append_expr(values, entity)?;
                self.ins.push(Instruction::VariadicOp { op, len: VariadicLen::Dynamic }.into());
            }
        })
    }
    fn append_variadic(&mut self, src: &'a ast::VariadicInput, entity: Option<&'a ast::Entity>) -> Result<VariadicLen, CompileError<'a>> {
        Ok(match src {
            ast::VariadicInput::Fixed(values) => {
                for value in values {
                    self.append_expr(value, entity)?;
                }
                VariadicLen::Fixed(values.len())
            }
            ast::VariadicInput::VarArgs(list) => {
                self.append_expr(list, entity)?;
                VariadicLen::Dynamic
            }
        })
    }
    fn append_expr(&mut self, expr: &'a ast::Expr, entity: Option<&'a ast::Entity>) -> Result<(), CompileError<'a>> {
        match &expr.kind {
            ast::ExprKind::Value(v) => self.ins.push(match v {
                ast::Value::Number(v) => Instruction::PushNumber { value: *v },
                ast::Value::String(v) => Instruction::PushString { value: v },
                ast::Value::Constant(v) => Instruction::PushNumber {
                    value: match v {
                        ast::Constant::Pi => std::f64::consts::PI,
                        ast::Constant::E => std::f64::consts::E,
                    }
                },
                ast::Value::Bool(v) => Instruction::PushBool { value: *v },
                ast::Value::Image(_) => unreachable!(), // Snap! doesn't have image literals
                ast::Value::List(_, _) => unreachable!(), // Snap! doesn't have list literals
                ast::Value::Ref(_) => unreachable!(), // Snap! doesn't have reference literals
            }.into()),
            ast::ExprKind::Variable { var } => self.ins.push(Instruction::PushVariable { var: &var.trans_name }.into()),
            ast::ExprKind::Atan2 { y, x } => self.append_simple_ins(entity, &[y, x], BinaryOp::Atan2.into())?,
            ast::ExprKind::Sub { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::Sub.into())?,
            ast::ExprKind::Div { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::Div.into())?,
            ast::ExprKind::Pow { base, power } => self.append_simple_ins(entity, &[base, power], BinaryOp::Pow.into())?,
            ast::ExprKind::Greater { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::Greater.into())?,
            ast::ExprKind::GreaterEq { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::GreaterEq.into())?,
            ast::ExprKind::Less { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::Less.into())?,
            ast::ExprKind::LessEq { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::LessEq.into())?,
            ast::ExprKind::Mod { left, right } => self.append_simple_ins(entity, &[left, right], BinaryOp::Mod.into())?,
            ast::ExprKind::Log { base, value } => self.append_simple_ins(entity, &[base, value], BinaryOp::Log.into())?,
            ast::ExprKind::Neg { value } => self.append_simple_ins(entity, &[value], UnaryOp::Neg.into())?,
            ast::ExprKind::Abs { value } => self.append_simple_ins(entity, &[value], UnaryOp::Abs.into())?,
            ast::ExprKind::Sqrt { value } => self.append_simple_ins(entity, &[value], UnaryOp::Sqrt.into())?,
            ast::ExprKind::Sin { value } => self.append_simple_ins(entity, &[value], UnaryOp::Sin.into())?,
            ast::ExprKind::Cos { value } => self.append_simple_ins(entity, &[value], UnaryOp::Cos.into())?,
            ast::ExprKind::Tan { value } => self.append_simple_ins(entity, &[value], UnaryOp::Tan.into())?,
            ast::ExprKind::Asin { value } => self.append_simple_ins(entity, &[value], UnaryOp::Asin.into())?,
            ast::ExprKind::Acos { value } => self.append_simple_ins(entity, &[value], UnaryOp::Acos.into())?,
            ast::ExprKind::Atan { value } => self.append_simple_ins(entity, &[value], UnaryOp::Atan.into())?,
            ast::ExprKind::Round { value } => self.append_simple_ins(entity, &[value], UnaryOp::Round.into())?,
            ast::ExprKind::Floor { value } => self.append_simple_ins(entity, &[value], UnaryOp::Floor.into())?,
            ast::ExprKind::Ceil { value } => self.append_simple_ins(entity, &[value], UnaryOp::Ceil.into())?,
            ast::ExprKind::Not { value } => self.append_simple_ins(entity, &[value], UnaryOp::Not.into())?,
            ast::ExprKind::StrLen { value } => self.append_simple_ins(entity, &[value], UnaryOp::StrLen.into())?,
            ast::ExprKind::UnicodeToChar { value } => self.append_simple_ins(entity, &[value], UnaryOp::UnicodeToChar.into())?,
            ast::ExprKind::CharToUnicode { value } => self.append_simple_ins(entity, &[value], UnaryOp::CharToUnicode.into())?,
            ast::ExprKind::Eq { left, right } => self.append_simple_ins(entity, &[left, right], Instruction::Eq { negate: false })?,
            ast::ExprKind::Neq { left, right } => self.append_simple_ins(entity, &[left, right], Instruction::Eq { negate: true })?,
            ast::ExprKind::Identical { left, right } => self.append_simple_ins(entity, &[left, right], Instruction::RefEq)?,
            ast::ExprKind::ListGet { list, index } => self.append_simple_ins(entity, &[index, list], Instruction::ListGet)?,
            ast::ExprKind::ListGetLast { list } => self.append_simple_ins(entity, &[list], Instruction::ListGetLast)?,
            ast::ExprKind::ListGetRandom { list } => self.append_simple_ins(entity, &[list], Instruction::ListGetRandom)?,
            ast::ExprKind::ListLength { value } => self.append_simple_ins(entity, &[value], Instruction::ListLength)?,
            ast::ExprKind::ListDims { value } => self.append_simple_ins(entity, &[value], Instruction::ListDims)?,
            ast::ExprKind::ListRank { value } => self.append_simple_ins(entity, &[value], Instruction::ListRank)?,
            ast::ExprKind::ListRev { value } => self.append_simple_ins(entity, &[value], Instruction::ListRev)?,
            ast::ExprKind::ListFlatten { value } => self.append_simple_ins(entity, &[value], Instruction::ListFlatten)?,
            ast::ExprKind::ListIsEmpty { value } => self.append_simple_ins(entity, &[value], Instruction::ListIsEmpty)?,
            ast::ExprKind::ListCons { item, list } => self.append_simple_ins(entity, &[item, list], Instruction::ListCons)?,
            ast::ExprKind::ListCdr { value } => self.append_simple_ins(entity, &[value], Instruction::ListCdr)?,
            ast::ExprKind::ListFind { list, value } => self.append_simple_ins(entity, &[value, list], Instruction::ListFind)?,
            ast::ExprKind::ListContains { list, value } => self.append_simple_ins(entity, &[list, value], Instruction::ListContains)?,
            ast::ExprKind::Range { start, stop } => self.append_simple_ins(entity, &[start, stop], BinaryOp::Range.into())?,
            ast::ExprKind::Random { a, b } => self.append_simple_ins(entity, &[a, b], BinaryOp::Random.into())?,
            ast::ExprKind::ListJson { value } => self.append_simple_ins(entity, &[value], Instruction::ListJson)?,
            ast::ExprKind::StrGet { string, index } => self.append_simple_ins(entity, &[index, string], BinaryOp::StrGet.into())?,
            ast::ExprKind::StrGetLast { string } => self.append_simple_ins(entity, &[string], UnaryOp::StrGetLast.into())?,
            ast::ExprKind::StrGetRandom { string } => self.append_simple_ins(entity, &[string], UnaryOp::StrGetRandom.into())?,
            ast::ExprKind::SyscallError => self.append_simple_ins(entity, &[], Instruction::PushSyscallError)?,
            ast::ExprKind::Effect { kind } => self.append_simple_ins(entity, &[], Instruction::PushProperty { prop: Property::from_effect(kind) })?,
            ast::ExprKind::Heading => self.ins.push(Instruction::PushProperty { prop: Property::Heading }.into()),
            ast::ExprKind::RpcError => self.ins.push(Instruction::PushRpcError.into()),
            ast::ExprKind::Answer => self.ins.push(Instruction::PushAnswer.into()),
            ast::ExprKind::Timer => self.ins.push(Instruction::PushTimer.into()),
            ast::ExprKind::XPos => self.ins.push(Instruction::PushProperty { prop: Property::XPos }.into()),
            ast::ExprKind::YPos => self.ins.push(Instruction::PushProperty { prop: Property::YPos }.into()),
            ast::ExprKind::Costume => self.ins.push(Instruction::PushCostume.into()),
            ast::ExprKind::CostumeNumber => self.ins.push(Instruction::PushCostumeNumber.into()),
            ast::ExprKind::CostumeList => self.ins.push(Instruction::PushCostumeList.into()),
            ast::ExprKind::Add { values } => self.append_variadic_op(entity, values, VariadicOp::Add)?,
            ast::ExprKind::Mul { values } => self.append_variadic_op(entity, values, VariadicOp::Mul)?,
            ast::ExprKind::Min { values } => self.append_variadic_op(entity, values, VariadicOp::Min)?,
            ast::ExprKind::Max { values } => self.append_variadic_op(entity, values, VariadicOp::Max)?,
            ast::ExprKind::StrCat { values } => self.append_variadic_op(entity, values, VariadicOp::StrCat)?,
            ast::ExprKind::MakeList { values } => self.append_variadic_op(entity, values, VariadicOp::MakeList)?,
            ast::ExprKind::ListCat { lists } => self.append_variadic_op(entity, lists, VariadicOp::ListCat)?,
            ast::ExprKind::ListReshape { value, dims } => {
                self.append_expr(value, entity)?;
                let len = self.append_variadic(dims, entity)?;
                self.ins.push(Instruction::ListReshape { len }.into());
            }
            ast::ExprKind::ListCombinations { sources } => {
                let len = self.append_variadic(sources, entity)?;
                self.ins.push(Instruction::ListCartesianProduct { len }.into());
            }
            ast::ExprKind::Conditional { condition, then, otherwise } => {
                self.append_expr(condition, entity)?;
                let test_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.append_expr(then, entity)?;
                let jump_aft_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                let test_false_pos = self.ins.len();
                self.append_expr(otherwise, entity)?;
                let aft_pos = self.ins.len();

                self.ins[test_pos] = Instruction::ConditionalJump { to: test_false_pos, when: false }.into();
                self.ins[jump_aft_pos] = Instruction::Jump { to: aft_pos }.into();
            }
            ast::ExprKind::Or { left, right } => {
                self.append_expr(left, entity)?;
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());
                self.append_expr(right, entity)?;
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();

                self.ins.push(Instruction::ToBool.into());
            }
            ast::ExprKind::And { left, right } => {
                self.append_expr(left, entity)?;
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());
                self.append_expr(right, entity)?;
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: aft, when: false }.into();

                self.ins.push(Instruction::ToBool.into());
            }
            ast::ExprKind::CallFn { function, args } => {
                for arg in args {
                    self.append_expr(arg, entity)?;
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.call_holes.push((call_hole_pos, function, entity));
            }
            ast::ExprKind::CallClosure { closure, args } => {
                for arg in args {
                    self.append_expr(arg, entity)?;
                }
                self.append_expr(closure, entity)?;
                self.ins.push(Instruction::CallClosure { args: args.len() }.into());
            }
            ast::ExprKind::CallRpc { service, rpc, args } => {
                for (arg_name, arg) in args {
                    self.ins.push(Instruction::MetaPush { value: arg_name }.into());
                    self.append_expr(arg, entity)?;
                }
                self.ins.push(Instruction::CallRpc { service, rpc, args: args.len() }.into());
            }
            ast::ExprKind::Syscall { name, args } => {
                self.append_expr(name, entity)?;
                let len = self.append_variadic(args, entity)?;
                self.ins.push(Instruction::Syscall { len }.into());
            }
            ast::ExprKind::NetworkMessageReply { target, msg_type, values } => {
                for (field, value) in values {
                    self.append_expr(value, entity)?;
                    self.ins.push(Instruction::MetaPush { value: field }.into());
                }
                self.append_expr(target, entity)?;
                self.ins.push(Instruction::SendNetworkMessage { msg_type, values: values.len(), expect_reply: true }.into());
            }
            ast::ExprKind::Closure { params, captures, stmts } => {
                let closure_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.closure_holes.push_back((closure_hole_pos, params, captures, stmts, entity));
            }
            ast::ExprKind::TextSplit { text, mode } => {
                self.append_expr(text, entity)?;
                let ins: Instruction = match mode {
                    ast::TextSplitMode::Letter => UnaryOp::SplitLetter.into(),
                    ast::TextSplitMode::Word => UnaryOp::SplitWord.into(),
                    ast::TextSplitMode::Tab => UnaryOp::SplitTab.into(),
                    ast::TextSplitMode::CR => UnaryOp::SplitCR.into(),
                    ast::TextSplitMode::LF => UnaryOp::SplitLF.into(),
                    ast::TextSplitMode::Csv => UnaryOp::SplitCsv.into(),
                    ast::TextSplitMode::Json => UnaryOp::SplitJson.into(),
                    ast::TextSplitMode::Custom(pattern) => {
                        self.append_expr(pattern, entity)?;
                        BinaryOp::SplitBy.into()
                    }
                };
                self.ins.push(ins.into());
            }
            ast::ExprKind::Map { f, list } => {
                self.append_expr(f, entity)?;
                self.append_expr(list, entity)?;
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Dynamic }.into()); // shallow copy the input list
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Fixed(0) }.into()); // push an empty list

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::DupeValue { top_index: 3 }.into());
                self.ins.push(Instruction::CallClosure { args: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::ListInsertLast.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ListPopFirstOrElse { goto: aft }.into();

                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::PopValue.into());
            }
            ast::ExprKind::Keep { f, list } => {
                self.append_expr(f, entity)?;
                self.append_expr(list, entity)?;
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Dynamic }.into()); // shallow copy the input list
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Fixed(0) }.into()); // push an empty list

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 4 }.into());
                self.ins.push(Instruction::CallClosure { args: 1 }.into());
                let skip_append_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::ListInsertLast.into());
                let kept_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                let pop_cont = self.ins.len();
                self.ins.push(Instruction::PopValue.into());
                let cont = self.ins.len();
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ListPopFirstOrElse { goto: aft }.into();
                self.ins[skip_append_pos] = Instruction::ConditionalJump { to: pop_cont, when: false }.into();
                self.ins[kept_jump_pos] = Instruction::Jump { to: cont }.into();

                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::PopValue.into());
            }
            ast::ExprKind::FindFirst { f, list } => {
                self.append_expr(f, entity)?;
                self.append_expr(list, entity)?;
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Dynamic }.into()); // shallow copy the input list

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 3 }.into());
                self.ins.push(Instruction::CallClosure { args: 1 }.into());
                let skip_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());

                let aft_loop = self.ins.len();
                self.ins.push(Instruction::PushString { value: "" }.into());
                let ret = self.ins.len();
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::PopValue.into());

                self.ins[exit_jump_pos] = Instruction::ListPopFirstOrElse { goto: aft_loop }.into();
                self.ins[skip_jump_pos] = Instruction::ConditionalJump { to: ret, when: true }.into();
            }
            ast::ExprKind::Combine { f, list } => {
                self.append_expr(list, entity)?;
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Dynamic }.into()); // shallow copy the input list
                self.append_expr(f, entity)?;

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                let first_check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 2 }.into());
                let loop_done_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::DupeValue { top_index: 2 }.into());
                self.ins.push(Instruction::CallClosure { args: 2 }.into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());

                let empty_list = self.ins.len();
                self.ins.push(Instruction::PushInt { value: 0 }.into());
                let ret = self.ins.len();
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::PopValue.into());
                self.ins.push(Instruction::PopValue.into());

                self.ins[first_check_pos] = Instruction::ListPopFirstOrElse { goto: empty_list }.into();
                self.ins[loop_done_pos] = Instruction::ListPopFirstOrElse { goto: ret }.into();
            }
            kind => return Err(CompileError::UnsupportedExpr { kind }),
        }

        if let Some(location) = expr.info.location.as_deref() {
            self.ins_locations.insert(self.ins.len(), location);
        }

        Ok(())
    }
    fn append_stmt(&mut self, stmt: &'a ast::Stmt, entity: Option<&'a ast::Entity>) -> Result<(), CompileError<'a>> {
        match &stmt.kind {
            ast::StmtKind::Assign { var, value } => self.append_simple_ins(entity, &[value], Instruction::Assign { var: &var.trans_name })?,
            ast::StmtKind::AddAssign { var, value } => self.append_simple_ins(entity, &[value], Instruction::BinaryOpAssign { var: &var.trans_name, op: BinaryOp::Add })?,
            ast::StmtKind::ListInsert { list, value, index } => self.append_simple_ins(entity, &[value, index, list], Instruction::ListInsert)?,
            ast::StmtKind::ListInsertLast { list, value } => self.append_simple_ins(entity, &[value, list], Instruction::ListInsertLast)?,
            ast::StmtKind::ListInsertRandom { list, value } => self.append_simple_ins(entity, &[value, list], Instruction::ListInsertRandom)?,
            ast::StmtKind::ListRemove { list, index } => self.append_simple_ins(entity, &[index, list], Instruction::ListRemove)?,
            ast::StmtKind::ListRemoveLast { list } => self.append_simple_ins(entity, &[list], Instruction::ListRemoveLast)?,
            ast::StmtKind::ListRemoveAll { list } => self.append_simple_ins(entity, &[list], Instruction::ListRemoveAll)?,
            ast::StmtKind::ListAssign { list, index, value } => self.append_simple_ins(entity, &[index, list, value], Instruction::ListAssign)?,
            ast::StmtKind::ListAssignLast { list, value } => self.append_simple_ins(entity, &[list, value], Instruction::ListAssignLast)?,
            ast::StmtKind::ListAssignRandom { list, value } => self.append_simple_ins(entity, &[list, value], Instruction::ListAssignRandom)?,
            ast::StmtKind::Return { value } => self.append_simple_ins(entity, &[value], Instruction::Return)?,
            ast::StmtKind::Throw { error } => self.append_simple_ins(entity, &[error], Instruction::Throw)?,
            ast::StmtKind::Ask { prompt } => self.append_simple_ins(entity, &[prompt], Instruction::Ask)?,
            ast::StmtKind::Sleep { seconds } => self.append_simple_ins(entity, &[seconds], Instruction::Sleep)?,
            ast::StmtKind::SendNetworkReply { value } => self.append_simple_ins(entity, &[value], Instruction::SendNetworkReply)?,
            ast::StmtKind::SetEffect { kind, value } => self.append_simple_ins(entity, &[value], Instruction::SetProperty { prop: Property::from_effect(kind) })?,
            ast::StmtKind::ChangeEffect { kind, delta } => self.append_simple_ins(entity, &[delta], Instruction::ChangeProperty { prop: Property::from_effect(kind) })?,
            ast::StmtKind::ClearEffects => self.ins.push(Instruction::ClearEffects.into()),
            ast::StmtKind::Forward { distance } => self.append_simple_ins(entity, &[distance], Instruction::Forward)?,
            ast::StmtKind::ResetTimer => self.ins.push(Instruction::ResetTimer.into()),
            ast::StmtKind::TurnRight { angle } => self.append_simple_ins(entity, &[angle], Instruction::ChangeProperty { prop: Property::Heading })?,
            ast::StmtKind::NextCostume => self.ins.push(Instruction::NextCostume.into()),
            ast::StmtKind::SetCostume { costume } => match costume {
                Some(x) => self.append_simple_ins(entity, &[x], Instruction::SetCostume)?,
                None => {
                    self.ins.push(Instruction::PushString { value: "" }.into());
                    self.ins.push(Instruction::SetCostume.into());
                }
            }
            ast::StmtKind::TurnLeft { angle } => {
                self.append_expr(angle, entity)?;
                self.ins.push(Instruction::from(UnaryOp::Neg).into());
                self.ins.push(Instruction::ChangeProperty { prop: Property::Heading }.into());
            }
            ast::StmtKind::Say { content, duration } | ast::StmtKind::Think { content, duration } => {
                self.append_simple_ins(entity, &[content], Instruction::Print)?;
                if let Some(t) = duration {
                    self.append_simple_ins(entity, &[t], Instruction::Sleep)?;
                    self.ins.push(Instruction::PushString { value: "" }.into());
                    self.ins.push(Instruction::Print.into());
                }
            }
            ast::StmtKind::DeclareLocals { vars } => {
                for var in vars {
                    self.ins.push(Instruction::DeclareLocal { var: &var.trans_name }.into());
                }
            }
            ast::StmtKind::RunFn { function, args } => {
                for arg in args {
                    self.append_expr(arg, entity)?;
                }
                let call_hole_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::PopValue.into());

                self.call_holes.push((call_hole_pos, function, entity));
            }
            ast::StmtKind::RunClosure { closure, args } => {
                for arg in args {
                    self.append_expr(arg, entity)?;
                }
                self.append_expr(closure, entity)?;
                self.ins.push(Instruction::CallClosure { args: args.len() }.into());
                self.ins.push(Instruction::PopValue.into());
            }
            ast::StmtKind::Warp { stmts } => {
                self.ins.push(Instruction::WarpStart.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }
                self.ins.push(Instruction::WarpStop.into());
            }
            ast::StmtKind::InfLoop { stmts } => {
                let top = self.ins.len();
                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
            }
            ast::StmtKind::WaitUntil { condition } => {
                let top = self.ins.len();
                self.append_expr(condition, entity)?;
                let jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[jump_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();
            }
            ast::StmtKind::UntilLoop { condition, stmts } => {
                let top = self.ins.len();
                self.append_expr(condition, entity)?;
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ConditionalJump { to: aft, when: true }.into();
            }
            ast::StmtKind::Repeat { times, stmts } => {
                self.append_expr(times, entity)?;

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::PushInt { value: 0 }.into());
                self.ins.push(Instruction::from(BinaryOp::Greater).into());
                let aft_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }

                self.ins.push(Instruction::PushInt { value: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Sub).into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[aft_jump_pos] = Instruction::ConditionalJump { to: aft, when: false }.into();

                self.ins.push(Instruction::PopValue.into());
            }
            ast::StmtKind::ForLoop { var, start, stop, stmts } => {
                self.append_expr(start, entity)?;
                self.ins.push(Instruction::ToNumber.into());
                self.append_expr(stop, entity)?;
                self.ins.push(Instruction::ToNumber.into());

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Greater).into());
                let delta_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::PushInt { value: 1 }.into());
                let positive_delta_end = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                let negative_delta_pos = self.ins.len();
                self.ins.push(Instruction::PushInt { value: -1 }.into());
                let aft_delta = self.ins.len();

                self.ins[delta_jump_pos] = Instruction::ConditionalJump { to: negative_delta_pos, when: true }.into();
                self.ins[positive_delta_end] = Instruction::Jump { to: aft_delta }.into();

                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 2 }.into());
                self.ins.push(Instruction::SwapValues { top_index_1: 0, top_index_2: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Sub).into());
                self.ins.push(Instruction::from(UnaryOp::Abs).into());

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::PushInt { value: 0 }.into());
                self.ins.push(Instruction::from(BinaryOp::Less).into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }

                self.ins.push(Instruction::PushInt { value: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Sub).into());
                self.ins.push(Instruction::DupeValue { top_index: 1 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 3 }.into());
                self.ins.push(Instruction::from(BinaryOp::Add).into());
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
            ast::StmtKind::ForeachLoop { var, items, stmts } => {
                self.append_expr(items, entity)?;
                self.ins.push(Instruction::VariadicOp { op: VariadicOp::MakeList, len: VariadicLen::Dynamic }.into()); // shallow copy the input list

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity)?;
                }
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[exit_jump_pos] = Instruction::ListPopFirstOrElse { goto: aft }.into();

                self.ins.push(Instruction::PopValue.into());
            }
            ast::StmtKind::If { condition, then } => {
                self.append_expr(condition, entity)?;
                let patch_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity)?;
                }
                let else_pos = self.ins.len();

                self.ins[patch_pos] = Instruction::ConditionalJump { to: else_pos, when: false }.into();
            }
            ast::StmtKind::IfElse { condition, then, otherwise } => {
                self.append_expr(condition, entity)?;
                let check_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                for stmt in then {
                    self.append_stmt(stmt, entity)?;
                }
                let jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);
                let else_pos = self.ins.len();
                for stmt in otherwise {
                    self.append_stmt(stmt, entity)?;
                }
                let aft = self.ins.len();

                self.ins[check_pos] = Instruction::ConditionalJump { to: else_pos, when: false }.into();
                self.ins[jump_pos] = Instruction::Jump { to: aft }.into();
            }
            ast::StmtKind::TryCatch { code, var, handler } => {
                let push_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in code {
                    self.append_stmt(stmt, entity)?;
                }
                self.ins.push(Instruction::PopHandler.into());
                let success_end_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                let error_handler_pos = self.ins.len();
                self.ins.push(Instruction::PopHandler.into());
                for stmt in handler {
                    self.append_stmt(stmt, entity)?;
                }
                let aft = self.ins.len();

                self.ins[push_pos] = Instruction::PushHandler { pos: error_handler_pos, var: &var.trans_name }.into();
                self.ins[success_end_pos] = Instruction::Jump { to: aft }.into();
            }
            ast::StmtKind::SendLocalMessage { target, msg_type, wait } => match target {
                Some(_) => unimplemented!(),
                None => self.append_simple_ins(entity, &[msg_type], Instruction::Broadcast { wait: *wait })?,
            }
            ast::StmtKind::RunRpc { service, rpc, args } => {
                for (arg_name, arg) in args {
                    self.ins.push(Instruction::MetaPush { value: arg_name }.into());
                    self.append_expr(arg, entity)?;
                }
                self.ins.push(Instruction::CallRpc { service, rpc, args: args.len() }.into());
                self.ins.push(Instruction::PopValue.into());
            }
            ast::StmtKind::SendNetworkMessage { target, msg_type, values } => {
                for (field, value) in values {
                    self.append_expr(value, entity)?;
                    self.ins.push(Instruction::MetaPush { value: field }.into());
                }
                self.append_expr(target, entity)?;
                self.ins.push(Instruction::SendNetworkMessage { msg_type, values: values.len(), expect_reply: false }.into());
            }
            ast::StmtKind::Syscall { name, args } => {
                self.append_expr(name, entity)?;
                let len = self.append_variadic(args, entity)?;
                self.ins.push(Instruction::Syscall { len }.into());
                self.ins.push(Instruction::PopValue.into());
            }
            kind => return Err(CompileError::UnsupportedStmt { kind }),
        }

        if let Some(location) = stmt.info.location.as_deref() {
            self.ins_locations.insert(self.ins.len(), location);
        }

        Ok(())
    }
    fn append_stmts_ret(&mut self, stmts: &'a [ast::Stmt], entity: Option<&'a ast::Entity>) -> Result<(), CompileError<'a>> {
        for stmt in stmts {
            self.append_stmt(stmt, entity)?;
        }
        self.ins.push(Instruction::PushString { value: "" }.into());
        self.ins.push(Instruction::Return.into());
        Ok(())
    }
    fn link(mut self, funcs: Vec<(&'a ast::Function, usize)>, entities: Vec<(&'a ast::Entity, EntityScriptInfo<'a>)>) -> Result<(ByteCode, ScriptInfo<'a>, Locations), CompileError<'a>> {
        assert!(self.closure_holes.is_empty());

        let global_fn_to_info = {
            let mut res = BTreeMap::new();
            for (func, pos) in funcs.iter() {
                res.insert(&*func.trans_name, (*pos, &*func.params));
            }
            res
        };
        let entity_fn_to_info = {
            let mut res = BTreeMap::new();
            for (entity, entity_locs) in entities.iter() {
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

        self.finalize(funcs, entities)
    }
    fn finalize(self, funcs: Vec<(&'a ast::Function, usize)>, entities: Vec<(&'a ast::Entity, EntityScriptInfo<'a>)>) -> Result<(ByteCode, ScriptInfo<'a>, Locations), CompileError<'a>> {
        let mut code = Vec::with_capacity(self.ins.len() * 4);
        let mut data = BinPool::new();
        let mut relocate_info = Vec::with_capacity(64);

        let mut final_ins_pos = Vec::with_capacity(self.ins.len());
        for ins in self.ins.iter() {
            final_ins_pos.push(code.len());
            match ins {
                InternalInstruction::Illegal => unreachable!(),
                InternalInstruction::Packed(vals) => for val in vals {
                    BinaryWrite::append(val, &mut code, &mut data, &mut relocate_info);
                }
                InternalInstruction::Valid(val) => BinaryWrite::append(val, &mut code, &mut data, &mut relocate_info),
            }
        }

        let data_backing = data.into_backing();
        let (data, data_backing_pos) = {
            let mut data = Vec::with_capacity(data_backing.0.iter().map(Vec::len).sum::<usize>());
            let mut data_backing_pos = Vec::with_capacity(data_backing.0.len());
            for backing in data_backing.0.iter() {
                data_backing_pos.push(data.len());
                data.extend_from_slice(backing);
            }
            (data, data_backing_pos)
        };

        fn apply_shrinking_plan(plan: &[(usize, usize, usize)], final_relocates: &mut [usize], code: &mut Vec<u8>, final_ins_pos: &mut [usize]) -> usize {
            let old_pos_to_ins: BTreeMap<usize, usize> = final_ins_pos.iter().copied().enumerate().map(|(a, b)| (b, a)).collect();
            let orig_code_size = code.len();

            let mut final_ins_pos_update_iter = final_ins_pos.iter_mut().fuse().peekable();
            let mut old_hole_pos_to_new_pos = BTreeMap::default();
            let (mut dest_pos, mut src_pos, mut total_shift) = (0, 0, 0);
            for (code_addr, prev_size, new_size) in plan.iter().copied() {
                debug_assert!(prev_size >= new_size);
                debug_assert!(code_addr >= src_pos);

                while let Some(old) = final_ins_pos_update_iter.peek() {
                    if **old > code_addr { break }
                    *final_ins_pos_update_iter.next().unwrap() -= total_shift;
                }

                code.copy_within(src_pos..code_addr + new_size, dest_pos);
                dest_pos += code_addr + new_size - src_pos;
                src_pos = code_addr + prev_size;
                old_hole_pos_to_new_pos.insert(code_addr, dest_pos - new_size);
                total_shift += prev_size - new_size;
            }
            for old in final_ins_pos_update_iter { *old -= total_shift; }
            code.copy_within(src_pos..src_pos + (orig_code_size - total_shift - dest_pos), dest_pos);
            code.truncate(orig_code_size - total_shift);

            let mut buf = Vec::with_capacity(10);
            for code_addr in final_relocates.iter_mut() {
                *code_addr = old_hole_pos_to_new_pos[code_addr];
                let old_pos = <usize as BinaryRead>::read(code, &[], *code_addr);
                buf.clear();
                encode_u64(final_ins_pos[old_pos_to_ins[&old_pos.0]] as u64, &mut buf, Some(old_pos.1 - *code_addr));
                debug_assert_eq!(buf.len(), old_pos.1 - *code_addr);
                code[*code_addr..old_pos.1].copy_from_slice(&buf);
            }

            total_shift
        }

        let mut fmt_buf = Vec::with_capacity(10);
        let mut shrinking_plan = vec![];
        let mut final_relocates = vec![];
        for info in relocate_info {
            fmt_buf.clear();
            let (code_addr, prev_size) = match info {
                RelocateInfo::Code { code_addr } => {
                    final_relocates.push(code_addr);
                    let pos = <usize as BinaryRead>::read(&code, &data, code_addr);
                    encode_u64(final_ins_pos[pos.0] as u64, &mut fmt_buf, None);
                    (code_addr, pos.1 - code_addr)
                }
                RelocateInfo::Data { code_addr } => {
                    let pool_index = <usize as BinaryRead>::read(&code, &data, code_addr);
                    let slice = &data_backing.1[pool_index.0];
                    encode_u64((data_backing_pos[slice.src] + slice.start) as u64, &mut fmt_buf, None);
                    (code_addr, pool_index.1 - code_addr)
                }
            };
            debug_assert!(prev_size >= fmt_buf.len());
            shrinking_plan.push((code_addr, prev_size, fmt_buf.len()));
            code[code_addr..code_addr + fmt_buf.len()].copy_from_slice(&fmt_buf);
        }

        apply_shrinking_plan(&shrinking_plan, &mut final_relocates, &mut code, &mut final_ins_pos);

        for _ in 0..SHRINK_CYCLES {
            shrinking_plan.clear();
            for code_addr in final_relocates.iter().copied() {
                let val = <usize as BinaryRead>::read(&code, &data, code_addr);
                fmt_buf.clear();
                encode_u64(val.0 as u64, &mut fmt_buf, None);
                debug_assert!(fmt_buf.len() <= val.1 - code_addr);
                code[code_addr..code_addr + fmt_buf.len()].copy_from_slice(&fmt_buf);
                shrinking_plan.push((code_addr, val.1 - code_addr, fmt_buf.len()));
            }
            let delta = apply_shrinking_plan(&shrinking_plan, &mut final_relocates, &mut code, &mut final_ins_pos);
            if delta == 0 { break }
        }

        let (mut funcs, mut entities) = (funcs, entities);

        for func in funcs.iter_mut() { func.1 = final_ins_pos[func.1]; }
        for entity in entities.iter_mut() {
            for func in entity.1.funcs.iter_mut() { func.1 = final_ins_pos[func.1]; }
            for script in entity.1.scripts.iter_mut() { script.1 = final_ins_pos[script.1]; }
        }
        let locations = Locations::condense(self.ins_locations.iter().map(|(p, v)| (final_ins_pos[*p], *v)).collect())?;

        Ok((ByteCode { tag: Default::default(), code: code.into_boxed_slice(), data: data.into_boxed_slice() }, ScriptInfo { funcs, entities }, locations))
    }
}

impl ByteCode {
    /// Compiles a single project role into an executable form.
    /// Also emits a locations object that includes a symbol table of functions and scripts,
    /// (needed to execute a specific segment of code), as well as a lookup table of bytecode index
    /// to code location (e.g., the block `collabId` from project xml), which is needed to
    /// provide human-readable error locations.
    pub fn compile<'a>(role: &'a ast::Role) -> Result<(ByteCode, InitInfo, ScriptInfo<'a>, Locations), CompileError<'a>> {
        let mut code = ByteCodeBuilder::default();

        let mut funcs = Vec::with_capacity(role.funcs.len());
        for func in role.funcs.iter() {
            funcs.push((func, code.ins.len()));
            code.append_stmts_ret(&func.stmts, None)?;
        }

        let mut entities = Vec::with_capacity(role.entities.len());
        for entity in role.entities.iter() {
            let mut funcs = Vec::with_capacity(entity.funcs.len());
            for func in entity.funcs.iter() {
                funcs.push((func, code.ins.len()));
                code.append_stmts_ret(&func.stmts, Some(entity))?;
            }

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for script in entity.scripts.iter() {
                scripts.push((script, code.ins.len()));
                code.append_stmts_ret(&script.stmts, Some(entity))?;
            }

            entities.push((entity, EntityScriptInfo { funcs, scripts }));
        }

        while let Some((hole_pos, params, captures, stmts, entity)) = code.closure_holes.pop_front() {
            let pos = code.ins.len();
            code.append_stmts_ret(stmts, entity)?;

            let mut ins_pack = Vec::with_capacity(params.len() + captures.len() + 1);
            for param in params {
                ins_pack.push(Instruction::MetaPush { value: &param.trans_name });
            }
            for param in captures {
                ins_pack.push(Instruction::MetaPush { value: &param.trans_name });
            }
            ins_pack.push(Instruction::MakeClosure { pos, params: params.len(), captures: captures.len() });

            code.ins[hole_pos] = InternalInstruction::Packed(ins_pack);
        }

        let (bytecode, script_info, locations) = code.link(funcs, entities)?;
        let init_info = Self::extract_init_info(role, &script_info)?;

        Ok((bytecode, init_info, script_info, locations))
    }
    fn extract_init_info<'a>(role: &'a ast::Role, script_info: &ScriptInfo<'a>) -> Result<InitInfo, CompileError<'a>> {
        let mut ref_values = vec![];

        let mut refs = BTreeMap::new();
        let mut string_refs = BTreeMap::new();
        let mut image_refs = BTreeMap::new();

        fn register_ref_values<'a>(val: &'a ast::Value, ref_values: &mut Vec<Option<RefValue>>, refs: &mut BTreeMap<usize, usize>, string_refs: &mut BTreeMap<&'a str, usize>, image_refs: &mut BTreeMap<*const Vec<u8>, usize>) {
            match val {
                ast::Value::Ref(_) | ast::Value::Bool(_) | ast::Value::Number(_) | ast::Value::Constant(_) => (),
                ast::Value::String(x) => {
                    string_refs.entry(x).or_insert_with(|| {
                        ref_values.push(Some(RefValue::String(x.clone()))); // we already have the value to store
                        ref_values.len() - 1
                    });
                }
                ast::Value::Image(x) => {
                    image_refs.entry(Rc::as_ptr(x)).or_insert_with(|| {
                        ref_values.push(Some(RefValue::Image((**x).clone()))); // we already have the value to store
                        ref_values.len() - 1
                    });
                }
                ast::Value::List(_, ref_id) => if let Some(ref_id) = ref_id {
                    refs.entry(ref_id.0).or_insert_with(|| {
                        ref_values.push(None); // we don't have the value yet (might contain undefined refs, so can't be handled yet)
                        ref_values.len() - 1
                    });
                }
            }
        }

        for global in role.globals.iter() {
            register_ref_values(&global.init, &mut ref_values, &mut refs, &mut string_refs, &mut image_refs);
        }
        for entity in role.entities.iter() {
            for field in entity.fields.iter() {
                register_ref_values(&field.init, &mut ref_values, &mut refs, &mut string_refs, &mut image_refs);
            }
            for costume in entity.costumes.iter() {
                register_ref_values(&costume.init, &mut ref_values, &mut refs, &mut string_refs, &mut image_refs);
            }
        }

        fn get_value<'a>(val: &'a ast::Value, ref_values: &mut Vec<Option<RefValue>>, refs: &BTreeMap<usize, usize>, string_refs: &BTreeMap<&'a str, usize>, image_refs: &BTreeMap<*const Vec<u8>, usize>) -> Result<InitValue, CompileError<'a>> {
            Ok(match val {
                ast::Value::Bool(x) => InitValue::Bool(*x),
                ast::Value::Number(x) => InitValue::Number(Number::new(*x)?),
                ast::Value::Constant(x) => match x {
                    ast::Constant::E => InitValue::Number(Number::new(std::f64::consts::E)?),
                    ast::Constant::Pi => InitValue::Number(Number::new(std::f64::consts::PI)?),
                }
                ast::Value::Ref(x) => {
                    let idx = *refs.get(&x.0).ok_or_else(|| CompileError::UndefinedRef)?;
                    InitValue::Ref(idx)
                }
                ast::Value::String(x) => {
                    let idx = *string_refs.get(x.as_str()).ok_or_else(|| CompileError::UndefinedRef)?;
                    InitValue::Ref(idx)
                }
                ast::Value::Image(x) => {
                    let idx = *image_refs.get(&Rc::as_ptr(x)).ok_or_else(|| CompileError::UndefinedRef)?;
                    InitValue::Ref(idx)
                }
                ast::Value::List(values, ref_id) => {
                    let res = RefValue::List(values.iter().map(|x| get_value(x, ref_values, refs, string_refs, image_refs)).collect::<Result<_,_>>()?);
                    match ref_id {
                        Some(ref_id) => {
                            let idx = *refs.get(&ref_id.0).ok_or_else(|| CompileError::UndefinedRef)?;
                            let target = &mut ref_values[idx];
                            debug_assert!(target.is_none());
                            *target = Some(res);
                            InitValue::Ref(idx)
                        }
                        None => {
                            ref_values.push(Some(res));
                            InitValue::Ref(ref_values.len() - 1)
                        }
                    }
                }
            })
        }

        // -------------------------------------------------------------------

        let proj_name = role.name.clone();
        let mut globals = vec![];
        let mut entities = vec![];

        for global in role.globals.iter() {
            globals.push((global.def.name.clone(), get_value(&global.init, &mut ref_values, &refs, &string_refs, &image_refs)?));
        }

        for (entity, entity_info) in script_info.entities.iter() {
            let name = entity.name.clone();
            let mut fields = vec![];
            let mut scripts = vec![];
            let mut costumes = vec![];

            let visible = entity.visible;
            let active_costume = entity.active_costume.clone();
            let color = entity.color;
            let size = Number::new(entity.scale * 100.0)?;
            let pos = (Number::new(entity.pos.0)?, Number::new(entity.pos.1)?);
            let heading = Number::new(entity.heading.rem_euclid(360.0))?;

            for field in entity.fields.iter() {
                fields.push((field.def.name.clone(), get_value(&field.init, &mut ref_values, &refs, &string_refs, &image_refs)?));
            }

            for costume in entity.costumes.iter() {
                costumes.push((costume.def.name.clone(), get_value(&costume.init, &mut ref_values, &refs, &string_refs, &image_refs)?));
            }

            for (script, pos) in entity_info.scripts.iter().copied() {
                let hat = match script.hat.as_ref() {
                    Some(x) => x,
                    None => continue,
                };
                let event = match &hat.kind {
                    ast::HatKind::OnFlag => Event::OnFlag,
                    ast::HatKind::LocalMessage { msg_type } => Event::LocalMessage { msg_type: msg_type.clone() },
                    ast::HatKind::NetworkMessage { msg_type, fields } => Event::NetworkMessage { msg_type: msg_type.clone(), fields: fields.iter().map(|x| x.trans_name.clone()).collect() },
                    ast::HatKind::OnKey { key } => Event::OnKey {
                        key_filter: match key.as_str() {
                            "any key" => None,
                            "up arrow" => Some(KeyCode::Up),
                            "down arrow" => Some(KeyCode::Down),
                            "left arrow" => Some(KeyCode::Left),
                            "right arrow" => Some(KeyCode::Right),
                            "enter" => Some(KeyCode::Enter),
                            "space" => Some(KeyCode::Char(' ')),
                            _ => {
                                let mut chars = key.chars();
                                let res = chars.next().map(|x| KeyCode::Char(x.to_ascii_lowercase()));
                                if res.is_none() || chars.next().is_some() { return Err(CompileError::BadKeycode { key }); }
                                Some(res.unwrap())
                            }
                        }
                    },
                    kind => return Err(CompileError::UnsupportedEvent { kind }),
                };
                scripts.push((event, pos));
            }

            entities.push(EntityInitInfo { name, fields, costumes, scripts, active_costume, pos, heading, size, visible, color });
        }

        let ref_values = ref_values.into_iter().map(|x| x.ok_or_else(|| CompileError::UndefinedRef)).collect::<Result<_,_>>()?;

        Ok(InitInfo { tag: Default::default(), proj_name, ref_values, globals, entities })
    }
    /// Generates a hex dump of the stored code, including instructions and addresses.
    #[cfg(feature = "std")]
    pub fn dump_code(&self, f: &mut dyn Write) -> io::Result<()> {
        let mut pos = 0;
        while pos < self.code.len() {
            let (ins, aft) = Instruction::read(&self.code, &self.data, pos);
            for (i, bytes) in self.code[pos..aft].chunks(BYTES_PER_LINE).enumerate() {
                if i == 0 {
                    write!(f, "{pos:08}   ")?;
                } else {
                    write!(f, "           ")?;
                }

                for &b in bytes {
                    write!(f, " {b:02x}")?;
                }
                for _ in bytes.len()..BYTES_PER_LINE {
                    write!(f, "   ")?;
                }

                if i == 0 {
                    write!(f, "    {ins:?}")?;
                }
                writeln!(f)?;
            }
            pos = aft;
        }
        Ok(())
    }
    /// Generate a hex dump of the stored program data, including string literals and meta values.
    #[cfg(feature = "std")]
    pub fn dump_data(&self, f: &mut dyn Write) -> io::Result<()> {
        for (i, bytes) in self.data.chunks(BYTES_PER_LINE).enumerate() {
            write!(f, "{:08}   ", i * BYTES_PER_LINE)?;
            for &b in bytes {
                write!(f, " {b:02x}")?;
            }
            for _ in bytes.len()..BYTES_PER_LINE {
                write!(f, "   ")?;
            }
            write!(f, "    ")?;
            for &b in bytes {
                write!(f, "{}", if (0x21..=0x7e).contains(&b) { b as char } else { '.' })?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
    /// Returns the total size of the [`ByteCode`] object (in bytes).
    pub fn total_size(&self) -> usize {
        self.code.len() + self.data.len()
    }
}
