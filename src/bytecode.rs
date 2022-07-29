//! Tools for generating executable [`ByteCode`] from a project's abstract syntax tree.

use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};
use std::io::{self, Write};
use std::mem;

use num_traits::FromPrimitive;
use bin_pool::BinPool;

use crate::*;
use crate::gc::*;

/// Number of bytes to display on each line of a hex dump
const BYTES_PER_LINE: usize = 12;

/// Max number of shrinking cycles to apply to variable width encoded values in an output binary
const SHRINK_CYCLES: usize = 3;

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
    ToBool, ToNumber,
    Not,
    Abs, Neg,
    Sqrt,
    Round, Floor, Ceil,
    Sin, Cos, Tan,
    Asin, Acos, Atan,
    SplitLetter, SplitWord, SplitTab, SplitCR, SplitLF, SplitCsv, SplitJson,
    Strlen,
    UnicodeToChar, CharToUnicode,
}

impl From<BinaryOp> for Instruction<'_> { fn from(op: BinaryOp) -> Self { Self::BinaryOp { op } } }
impl From<UnaryOp> for Instruction<'_> { fn from(op: UnaryOp) -> Self { Self::UnaryOp { op } } }

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
    /// Consumes one value, `list`, from the value stack and deletes a random item from it.
    ListRemoveRandom,
    /// Consumes one value, `list`, from the value stack and deletes all elements from it.
    ListRemoveAll,

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

    /// Consumes 1 value from the value stack, `msg_type`, and broadcasts a message to all scripts.
    /// The `wait` flag can be set to denote that the broadcasting script should wait until all receiving scripts have terminated.
    Broadcast { wait: bool },

    /// Consumes 1 value `msg` from the value stack and prints it to the stored printer.
    Print,
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

fn encode_u64(mut val: u64, out: &mut Vec<u8>, bytes: Option<usize>) {
    let mut blocks = ((64 - val.leading_zeros() as usize + 6) / 7).max(1);
    if let Some(bytes) = bytes {
        debug_assert!(bytes >= blocks);
        blocks = bytes;
    }

    debug_assert!(blocks >= 1 && blocks <= 10);
    for _ in 1..blocks {
        out.push((val as u8 & 0x7f) | 0x80);
        val >>= 7;
    }
    debug_assert!(val <= 0x7f);
    out.push(val as u8);
}

// encodes values as a sequence of bytes of form [1: next][7: bits] in little-endian order.
// if `relocate_info` is provided to `append`, expanded mode is used, which encodes the value with the maximum of 10 bytes.
impl BinaryRead<'_> for u64 {
    fn read(code: &[u8], _: &[u8], start: usize) -> (Self, usize) {
        let (mut val, mut aft) = (0, start);
        for &b in &code[start..] {
            aft += 1;
            if b & 0x80 == 0 { break }
        }
        for &b in code[start..aft].iter().rev() {
            val = (val << 7) | (b & 0x7f) as u64;
        }
        (val, aft)
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
        (&std::str::from_utf8(&data[data_pos..data_pos + data_len]).unwrap(), aft)
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
            7 => read_prefixed!(Instruction::PushString {} : value),
            8 => read_prefixed!(Instruction::PushVariable {} : var),
            9 => read_prefixed!(Instruction::PopValue),

            10 => read_prefixed!(Instruction::DupeValue {} : top_index),
            11 => read_prefixed!(Instruction::SwapValues {} : top_index_1, top_index_2),
            12 => read_prefixed!(Instruction::ShallowCopy),

            13 => read_prefixed!(Instruction::MakeList {} : len),
            14 => read_prefixed!(Instruction::MakeListRange),

            15 => read_prefixed!(Instruction::ListLen),
            16 => read_prefixed!(Instruction::ListIsEmpty),

            17 => read_prefixed!(Instruction::ListInsert),
            18 => read_prefixed!(Instruction::ListInsertLast),
            19 => read_prefixed!(Instruction::ListInsertRandom),

            20 => read_prefixed!(Instruction::ListGet),
            21 => read_prefixed!(Instruction::ListGetLast),
            22 => read_prefixed!(Instruction::ListGetRandom),

            23 => read_prefixed!(Instruction::ListAssign),
            24 => read_prefixed!(Instruction::ListAssignLast),
            25 => read_prefixed!(Instruction::ListAssignRandom),

            26 => read_prefixed!(Instruction::ListRemove),
            27 => read_prefixed!(Instruction::ListRemoveLast),
            28 => read_prefixed!(Instruction::ListRemoveRandom),
            29 => read_prefixed!(Instruction::ListRemoveAll),

            30 => read_prefixed!(Instruction::Strcat {} : args),

            31 => read_prefixed!(Instruction::BinaryOp {} : op),
            32 => read_prefixed!(Instruction::Eq),
            33 => read_prefixed!(Instruction::UnaryOp {} : op),

            34 => read_prefixed!(Instruction::DeclareLocal {} : var),
            35 => read_prefixed!(Instruction::Assign {} : var),
            36 => read_prefixed!(Instruction::BinaryOpAssign {} : var, op),

            37 => read_prefixed!(Instruction::Jump {} : to),
            38 => read_prefixed!(Instruction::ConditionalJump { when: false, } : to),
            39 => read_prefixed!(Instruction::ConditionalJump { when: true, } : to),

            40 => read_prefixed!(Instruction::MetaPush {} : value),

            41 => read_prefixed!(Instruction::Call {} : pos, params),
            42 => read_prefixed!(Instruction::MakeClosure {} : pos, params, captures),
            43 => read_prefixed!(Instruction::CallClosure {} : args),
            44 => read_prefixed!(Instruction::CallRpc {} : service, rpc, args),
            45 => read_prefixed!(Instruction::Return),

            46 => read_prefixed!(Instruction::Broadcast { wait: false }),
            47 => read_prefixed!(Instruction::Broadcast { wait: true }),

            48 => read_prefixed!(Instruction::Print),

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
            Instruction::PushString { value } => append_prefixed!(7: move str value),
            Instruction::PushVariable { var } => append_prefixed!(8: move str var),
            Instruction::PopValue => append_prefixed!(9),

            Instruction::DupeValue { top_index } => append_prefixed!(10: top_index),
            Instruction::SwapValues { top_index_1, top_index_2 } => append_prefixed!(11: top_index_1, top_index_2),
            Instruction::ShallowCopy => append_prefixed!(12),

            Instruction::MakeList { len } => append_prefixed!(13: len),
            Instruction::MakeListRange => append_prefixed!(14),

            Instruction::ListLen => append_prefixed!(15),
            Instruction::ListIsEmpty => append_prefixed!(16),

            Instruction::ListInsert => append_prefixed!(17),
            Instruction::ListInsertLast => append_prefixed!(18),
            Instruction::ListInsertRandom => append_prefixed!(19),

            Instruction::ListGet => append_prefixed!(20),
            Instruction::ListGetLast => append_prefixed!(21),
            Instruction::ListGetRandom => append_prefixed!(22),

            Instruction::ListAssign => append_prefixed!(23),
            Instruction::ListAssignLast => append_prefixed!(24),
            Instruction::ListAssignRandom => append_prefixed!(25),

            Instruction::ListRemove => append_prefixed!(26),
            Instruction::ListRemoveLast => append_prefixed!(27),
            Instruction::ListRemoveRandom => append_prefixed!(28),
            Instruction::ListRemoveAll => append_prefixed!(29),

            Instruction::Strcat { args } => append_prefixed!(30: args),

            Instruction::BinaryOp { op } => append_prefixed!(31: op),
            Instruction::Eq => append_prefixed!(32),
            Instruction::UnaryOp { op } => append_prefixed!(33: op),

            Instruction::DeclareLocal { var } => append_prefixed!(34: move str var),
            Instruction::Assign { var } => append_prefixed!(35: move str var),
            Instruction::BinaryOpAssign { var, op } => append_prefixed!(36: move str var, op),

            Instruction::Jump { to } => append_prefixed!(37: move to),
            Instruction::ConditionalJump { to, when: false } => append_prefixed!(38: move to),
            Instruction::ConditionalJump { to, when: true } => append_prefixed!(39: move to),

            Instruction::MetaPush { value } => append_prefixed!(40: move str value),

            Instruction::Call { pos, params } => append_prefixed!(41: move pos, params),
            Instruction::MakeClosure { pos, params, captures } => append_prefixed!(42: move pos, params, captures),
            Instruction::CallClosure { args } => append_prefixed!(43: args),
            Instruction::CallRpc { service, rpc, args } => append_prefixed!(44: move str service, move str rpc, args),
            Instruction::Return => append_prefixed!(45),

            Instruction::Broadcast { wait: false } => append_prefixed!(46),
            Instruction::Broadcast { wait: true } => append_prefixed!(47),

            Instruction::Print => append_prefixed!(48),
        }
    }
}

/// An interpreter-ready sequence of instructions.
/// 
/// [`Process`](crate::runtime::Process) is an execution primitive that can be used to execute generated [`ByteCode`].
#[derive(Debug, Collect)]
#[collect(require_static)]
pub struct ByteCode {
    pub(crate) code: Box<[u8]>,
    pub(crate) data: Box<[u8]>,
}
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
    fn append_simple_ins(&mut self, entity: Option<&'a ast::Entity>, values: &[&'a ast::Expr], op: Instruction<'a>) {
        for value in values {
            self.append_expr(value, entity);
        }
        self.ins.push(op.into());
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
            ast::Expr::Add { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Add.into()),
            ast::Expr::Sub { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Sub.into()),
            ast::Expr::Mul { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Mul.into()),
            ast::Expr::Div { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Div.into()),
            ast::Expr::Pow { base, power, .. } => self.append_simple_ins(entity, &[base, power], BinaryOp::Pow.into()),
            ast::Expr::Greater { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Greater.into()),
            ast::Expr::Less { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Less.into()),
            ast::Expr::Mod { left, right, .. } => self.append_simple_ins(entity, &[left, right], BinaryOp::Mod.into()),
            ast::Expr::Log { base, value, .. } => self.append_simple_ins(entity, &[base, value], BinaryOp::Log.into()),
            ast::Expr::Neg { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Neg.into()),
            ast::Expr::Abs { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Abs.into()),
            ast::Expr::Sqrt { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Sqrt.into()),
            ast::Expr::Sin { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Sin.into()),
            ast::Expr::Cos { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Cos.into()),
            ast::Expr::Tan { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Tan.into()),
            ast::Expr::Asin { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Asin.into()),
            ast::Expr::Acos { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Acos.into()),
            ast::Expr::Atan { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Atan.into()),
            ast::Expr::Round { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Round.into()),
            ast::Expr::Floor { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Floor.into()),
            ast::Expr::Ceil { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Ceil.into()),
            ast::Expr::Not { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Not.into()),
            ast::Expr::Strlen { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::Strlen.into()),
            ast::Expr::UnicodeToChar { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::UnicodeToChar.into()),
            ast::Expr::CharToUnicode { value, .. } => self.append_simple_ins(entity, &[value], UnaryOp::CharToUnicode.into()),
            ast::Expr::Eq { left, right, .. } => self.append_simple_ins(entity, &[left, right], Instruction::Eq),
            ast::Expr::ListIndex { list, index, .. } => self.append_simple_ins(entity, &[index, list], Instruction::ListGet),
            ast::Expr::ListLastIndex { list, .. } => self.append_simple_ins(entity, &[list], Instruction::ListGetLast),
            ast::Expr::ListRandIndex { list, .. } => self.append_simple_ins(entity, &[list], Instruction::ListGetRandom),
            ast::Expr::Listlen { value, .. } => self.append_simple_ins(entity, &[value], Instruction::ListLen),
            ast::Expr::ListIsEmpty { value, .. } => self.append_simple_ins(entity, &[value], Instruction::ListIsEmpty),
            ast::Expr::RangeInclusive { start, stop, .. } => self.append_simple_ins(entity, &[start, stop], Instruction::MakeListRange),
            ast::Expr::MakeList { values, .. } => {
                for value in values {
                    self.append_expr(value, entity);
                }
                self.ins.push(Instruction::MakeList { len: values.len() }.into());
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

                self.ins.push(Instruction::from(UnaryOp::ToBool).into());
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

                self.ins.push(Instruction::from(UnaryOp::ToBool).into());
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
                let ins: Instruction = match mode {
                    ast::TextSplitMode::Letter => UnaryOp::SplitLetter.into(),
                    ast::TextSplitMode::Word => UnaryOp::SplitWord.into(),
                    ast::TextSplitMode::Tab => UnaryOp::SplitTab.into(),
                    ast::TextSplitMode::CR => UnaryOp::SplitCR.into(),
                    ast::TextSplitMode::LF => UnaryOp::SplitLF.into(),
                    ast::TextSplitMode::Csv => UnaryOp::SplitCsv.into(),
                    ast::TextSplitMode::Json => UnaryOp::SplitJson.into(),
                    ast::TextSplitMode::Custom(pattern) => {
                        self.append_expr(pattern, entity);
                        BinaryOp::SplitCustom.into()
                    }
                };
                self.ins.push(ins.into());
            }
            x => unimplemented!("{:?}", x),
        }
    }
    fn append_stmt(&mut self, stmt: &'a ast::Stmt, entity: Option<&'a ast::Entity>) {
        match stmt {
            ast::Stmt::Assign { var, value, .. } => self.append_simple_ins(entity, &[value], Instruction::Assign { var: &var.trans_name }),
            ast::Stmt::AddAssign { var, value, .. } => self.append_simple_ins(entity, &[value], Instruction::BinaryOpAssign { var: &var.trans_name, op: BinaryOp::Add }),
            ast::Stmt::InsertAt { list, value, index, .. } => self.append_simple_ins(entity, &[value, index, list], Instruction::ListInsert),
            ast::Stmt::Push { list, value, .. } => self.append_simple_ins(entity, &[value, list], Instruction::ListInsertLast),
            ast::Stmt::InsertAtRand { list, value, .. } => self.append_simple_ins(entity, &[value, list], Instruction::ListInsertRandom),
            ast::Stmt::RemoveAt { list, index, .. } => self.append_simple_ins(entity, &[index, list], Instruction::ListRemove),
            ast::Stmt::Pop { list, .. } => self.append_simple_ins(entity, &[list], Instruction::ListRemoveLast),
            ast::Stmt::RemoveAll { list, .. } => self.append_simple_ins(entity, &[list], Instruction::ListRemoveAll),
            ast::Stmt::IndexAssign { list, index, value, .. } => self.append_simple_ins(entity, &[index, list, value], Instruction::ListAssign),
            ast::Stmt::LastIndexAssign { list, value, .. } => self.append_simple_ins(entity, &[list, value], Instruction::ListAssignLast),
            ast::Stmt::RandIndexAssign { list, value, .. } => self.append_simple_ins(entity, &[list, value], Instruction::ListAssignRandom),
            ast::Stmt::Return { value, .. } => self.append_simple_ins(entity, &[value], Instruction::Return),
            ast::Stmt::Say { content, duration, .. } | ast::Stmt::Think { content, duration, .. } => match duration {
                Some(_) => unimplemented!(),
                None => self.append_simple_ins(entity, &[content], Instruction::Print),
            }
            ast::Stmt::VarDecl { vars, .. } => {
                for var in vars {
                    self.ins.push(Instruction::DeclareLocal { var: &var.trans_name }.into());
                }
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
                self.ins.push(Instruction::PushInt { value: 0 }.into());
                self.ins.push(Instruction::from(BinaryOp::Greater).into());
                let aft_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }

                self.ins.push(Instruction::PushInt { value: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Sub).into());
                self.ins.push(Instruction::Yield.into());
                self.ins.push(Instruction::Jump { to: top }.into());
                let aft = self.ins.len();

                self.ins[aft_jump_pos] = Instruction::ConditionalJump { to: aft, when: false }.into();

                self.ins.push(Instruction::PopValue.into());
            }
            ast::Stmt::ForLoop { var, start, stop, stmts, .. } => {
                self.append_expr(start, entity);
                self.ins.push(Instruction::from(UnaryOp::ToNumber).into());
                self.append_expr(stop, entity);
                self.ins.push(Instruction::from(UnaryOp::ToNumber).into());

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
                    self.append_stmt(stmt, entity);
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
            ast::Stmt::ForeachLoop { var, items, stmts, .. } => {
                self.append_expr(items, entity);
                self.ins.push(Instruction::ShallowCopy.into());
                self.ins.push(Instruction::PushInt { value: 1 }.into());

                let top = self.ins.len();
                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 2 }.into());
                self.ins.push(Instruction::ListLen.into());
                self.ins.push(Instruction::from(BinaryOp::Greater).into());
                let exit_jump_pos = self.ins.len();
                self.ins.push(InternalInstruction::Illegal);

                self.ins.push(Instruction::DupeValue { top_index: 0 }.into());
                self.ins.push(Instruction::DupeValue { top_index: 2 }.into());
                self.ins.push(Instruction::ListGet.into());
                self.ins.push(Instruction::Assign { var: &var.trans_name }.into());
                for stmt in stmts {
                    self.append_stmt(stmt, entity);
                }
                self.ins.push(Instruction::PushInt { value: 1 }.into());
                self.ins.push(Instruction::from(BinaryOp::Add).into());
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

        fn update_locations<F: Fn(usize) -> usize>(locations: &mut Locations, f: F) {
            for func in locations.funcs.iter_mut() { func.1 = f(func.1); }
            for entity in locations.entities.iter_mut() {
                for func in entity.1.funcs.iter_mut() { func.1 = f(func.1); }
                for script in entity.1.scripts.iter_mut() { script.1 = f(script.1); }
            }
        }
        update_locations(&mut locations, |x| final_ins_pos[x]);

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

        fn apply_shrinking_plan(plan: &[(usize, usize, usize)], final_relocates: &mut [usize], code: &mut Vec<u8>, final_ins_pos: &mut [usize], locations: &mut Locations) -> usize {
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

            update_locations(locations, |x| final_ins_pos[old_pos_to_ins[&x]]);

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

        apply_shrinking_plan(&shrinking_plan, &mut final_relocates, &mut code, &mut final_ins_pos, &mut locations);

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
            let delta = apply_shrinking_plan(&shrinking_plan, &mut final_relocates, &mut code, &mut final_ins_pos, &mut locations);
            if delta == 0 { break }
        }

        (ByteCode { code: code.into_boxed_slice(), data: data.into_boxed_slice() }, locations)
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
    /// Generates a hex dump of the stored code, including instructions and addresses.
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
