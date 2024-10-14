use alloc::rc::Rc;
use alloc::vec::Vec;

use core::iter;

use crate::runtime::*;
use crate::process::*;
use crate::std_system::*;
use crate::std_util::*;
use crate::gc::*;
use compact_str::*;

mod process;
mod project;

const BASE_URL: &'static str = "https://cloud.netsblox.org";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeType {}

#[derive(Debug)]
enum NativeValue {}
impl GetType for NativeValue {
    type Output = NativeType;
    fn get_type(&self) -> Self::Output {
        unreachable!()
    }
}

struct EntityState {
    props: Properties,
}
impl From<EntityKind<'_, '_, C, StdSystem<C>>> for EntityState {
    fn from(kind: EntityKind<'_, '_, C, StdSystem<C>>) -> Self {
        match kind {
            EntityKind::Stage { props } | EntityKind::Sprite { props } => EntityState { props },
            EntityKind::Clone { parent } => EntityState { props: parent.state.props },
        }
    }
}

struct ProcessState {
    tokens: Vec<Text>,
}
impl From<ProcessKind<'_, '_, C, StdSystem<C>>> for ProcessState {
    fn from(_: ProcessKind<'_, '_, C, StdSystem<C>>) -> Self {
        Self {
            tokens: vec![],
        }
    }
}
impl Unwindable for ProcessState {
    type UnwindPoint = usize;
    fn get_unwind_point(&self) -> Self::UnwindPoint {
        self.tokens.len()
    }
    fn unwind_to(&mut self, unwind_point: &Self::UnwindPoint) {
        self.tokens.drain(*unwind_point..);
    }
}

fn default_properties_config() -> Config<C, StdSystem<C>> {
    Config {
        request: Some(Rc::new(|_, key, request, proc| {
            let entity = proc.get_call_stack().last().unwrap().entity.borrow();
            match request {
                Request::Property { prop } => entity.state.props.perform_get_property(key, prop),
                _ => RequestStatus::UseDefault { key, request },
            }
        })),
        command: Some(Rc::new(|mc, key, command, proc| {
            let mut entity = proc.get_call_stack().last().unwrap().entity.borrow_mut(mc);
            match command {
                Command::SetProperty { prop, value } => entity.state.props.perform_set_property(key, prop, value),
                Command::ChangeProperty { prop, delta } => entity.state.props.perform_change_property(key, prop, delta),
                Command::ClearEffects => entity.state.props.perform_clear_effects(key),
                Command::GotoXY { x, y } => entity.state.props.perform_goto_xy(key, x, y),
                Command::PointTowardsXY { x, y } => entity.state.props.perform_point_towards_xy(key, x, y),
                Command::Forward { distance } => entity.state.props.perform_forward(key, distance),
                _ => CommandStatus::UseDefault { key, command },
            }
        })),
    }
}

struct C;
impl CustomTypes<StdSystem<C>> for C {
    type NativeValue = NativeValue;
    type Intermediate = SimpleValue;

    type EntityState = EntityState;
    type ProcessState = ProcessState;

    fn from_intermediate<'gc>(mc: &Mutation<'gc>, value: Self::Intermediate) -> Value<'gc, C, StdSystem<C>> {
        Value::from_simple(mc, value)
    }
}

fn assert_values_eq<'gc>(got: &Value<'gc, C, StdSystem<C>>, expected: &Value<'gc, C, StdSystem<C>>, epsilon: f64, path: &str) {
    if got.get_type() != expected.get_type() {
        panic!("{} - type error - got {:?} expected {:?} - {:?}", path, got.get_type(), expected.get_type(), got);
    }
    match (got, expected) {
        (Value::Bool(got), Value::Bool(expected)) => {
            if got != expected { panic!("{} - bool error - got {} expected {}", path, got, expected) }
        }
        (Value::Number(got), Value::Number(expected)) => {
            let (got, expected) = (got.get(), expected.get());
            let good = match epsilon <= 0.0 {
                true => got.to_bits() == expected.to_bits(),
                false => if got.is_finite() && expected.is_finite() { (got - expected).abs() <= epsilon } else { got == expected },
            };
            if !good { panic!("{} - number error - got {} expected {}", path, got, expected) }
        }
        (Value::Text(got), Value::Text(expected)) => {
            if got.as_str() != expected.as_str() { panic!("{} - string error - got {:?} expected {:?}", path, got.as_str(), expected.as_str()) }
        }
        (Value::List(got), Value::List(expected)) => {
            let got = got.borrow();
            let expected = expected.borrow();

            if got.len() != expected.len() { panic!("{} - list len error - got {} expected {}\ngot:      {:?}\nexpected: {:?}", path, got.len(), expected.len(), got, expected) }

            for (i, (got, expected)) in iter::zip(got.iter(), expected.iter()).enumerate() {
                assert_values_eq(got, expected, epsilon, &format!("{}[{}]", path, i));
            }
        }
        (x, y) => unimplemented!("types: {:?} {:?}", x.get_type(), y.get_type()),
    }
}

#[test]
fn test_sizes() {
    macro_rules! match_pointer_size {
        ($($size:literal => $val:expr),*$(,)?) => {{
            $(#[cfg(target_pointer_width = $size)] { $val })*
        }};
    }

    if core::mem::size_of::<Value<C, StdSystem<C>>>() != match_pointer_size!("64" => 16, "32" => 12) {
        panic!("values wrong size: {}", core::mem::size_of::<Value<C, StdSystem<C>>>());
    }
    if core::mem::size_of::<Option<Value<C, StdSystem<C>>>>() != match_pointer_size!("64" => 16, "32" => 12) {
        panic!("optional values wrong size: {}", core::mem::size_of::<Option<Value<C, StdSystem<C>>>>());
    }
    if core::mem::size_of::<Shared<'static, Value<'static, C, StdSystem<C>>>>() != match_pointer_size!("64" => 16, "32" => 12) {
        panic!("shared values wrong size: {}", core::mem::size_of::<Shared<'static, Value<'static, C, StdSystem<C>>>>());
    }
}

#[test]
fn test_send() {
    fn assert_send<T: Send>() {}
    assert_send::<Number>();
    assert_send::<Color>();
    assert_send::<Note>();
    assert_send::<Image>();
    assert_send::<Audio>();
    assert_send::<SimpleValue>();
    assert_send::<OutgoingMessage>();
    assert_send::<IncomingMessage>();
    assert_send::<AsyncResult<SimpleValue>>();
    assert_send::<SysTime>();

    #[cfg(feature = "std")]
    {
        assert_send::<NetsBloxContext>();
        assert_send::<RpcRequest<C, StdSystem<C>>>();
        assert_send::<ReplyEntry>();
        assert_send::<Clock>();
        assert_send::<AsyncKey<SimpleValue>>();
    }
}

#[test]
fn test_note() {
    for i in 0..=127 {
        assert_eq!(Note::from_midi(i, false).unwrap().get_midi().0, i);
    }
    for i in 128..=255 {
        assert!(Note::from_midi(i, false).is_none());
    }

    assert!((Note::from_midi(0, false).unwrap().get_frequency().get() - 8.18).abs() < 0.01);
    assert!((Note::from_midi(1, false).unwrap().get_frequency().get() - 8.66).abs() < 0.01);
    assert!((Note::from_midi(2, false).unwrap().get_frequency().get() - 9.18).abs() < 0.01);
    assert!((Note::from_midi(127, false).unwrap().get_frequency().get() - 12543.85).abs() < 0.01);
    assert!((Note::from_midi(126, false).unwrap().get_frequency().get() - 11839.82).abs() < 0.01);
    assert!((Note::from_midi(125, false).unwrap().get_frequency().get() - 11175.30).abs() < 0.01);
    assert!((Note::from_midi(80, false).unwrap().get_frequency().get() - 830.61).abs() < 0.01);
    assert!((Note::from_midi(52, false).unwrap().get_frequency().get() - 164.81).abs() < 0.01);

    assert_eq!(Note::from_midi(127, false).unwrap().get_name(true), "G9");
    assert_eq!(Note::from_midi(126, false).unwrap().get_name(true), "F#9");
    assert_eq!(Note::from_midi(125, false).unwrap().get_name(true), "F9");
    assert_eq!(Note::from_midi(124, false).unwrap().get_name(true), "E9");
    assert_eq!(Note::from_midi(123, false).unwrap().get_name(true), "D#9");
    assert_eq!(Note::from_midi(122, false).unwrap().get_name(true), "D9");
    assert_eq!(Note::from_midi(121, false).unwrap().get_name(true), "C#9");
    assert_eq!(Note::from_midi(120, false).unwrap().get_name(true), "C9");
    assert_eq!(Note::from_midi(119, false).unwrap().get_name(true), "B8");
    assert_eq!(Note::from_midi(118, false).unwrap().get_name(true), "A#8");
    assert_eq!(Note::from_midi(117, false).unwrap().get_name(true), "A8");
    assert_eq!(Note::from_midi(116, false).unwrap().get_name(true), "G#8");
    assert_eq!(Note::from_midi(115, false).unwrap().get_name(true), "G8");
    assert_eq!(Note::from_midi(114, false).unwrap().get_name(true), "F#8");
    assert_eq!(Note::from_midi(113, false).unwrap().get_name(true), "F8");
    assert_eq!(Note::from_midi(112, false).unwrap().get_name(true), "E8");
    assert_eq!(Note::from_midi(111, false).unwrap().get_name(true), "D#8");
    assert_eq!(Note::from_midi(110, false).unwrap().get_name(true), "D8");
    assert_eq!(Note::from_midi(109, false).unwrap().get_name(true), "C#8");
    assert_eq!(Note::from_midi(108, false).unwrap().get_name(true), "C8");
    assert_eq!(Note::from_midi(107, false).unwrap().get_name(true), "B7");
    assert_eq!(Note::from_midi(106, false).unwrap().get_name(true), "A#7");
    assert_eq!(Note::from_midi(105, false).unwrap().get_name(true), "A7");
    assert_eq!(Note::from_midi(104, false).unwrap().get_name(true), "G#7");
    assert_eq!(Note::from_midi(103, false).unwrap().get_name(true), "G7");
    assert_eq!(Note::from_midi(102, false).unwrap().get_name(true), "F#7");
    assert_eq!(Note::from_midi(101, false).unwrap().get_name(true), "F7");
    assert_eq!(Note::from_midi(100, false).unwrap().get_name(true), "E7");
    assert_eq!(Note::from_midi(99, false).unwrap().get_name(true), "D#7");
    assert_eq!(Note::from_midi(98, false).unwrap().get_name(true), "D7");
    assert_eq!(Note::from_midi(97, false).unwrap().get_name(true), "C#7");
    assert_eq!(Note::from_midi(96, false).unwrap().get_name(true), "C7");
    assert_eq!(Note::from_midi(95, false).unwrap().get_name(true), "B6");
    assert_eq!(Note::from_midi(94, false).unwrap().get_name(true), "A#6");
    assert_eq!(Note::from_midi(93, false).unwrap().get_name(true), "A6");
    assert_eq!(Note::from_midi(92, false).unwrap().get_name(true), "G#6");
    assert_eq!(Note::from_midi(91, false).unwrap().get_name(true), "G6");
    assert_eq!(Note::from_midi(90, false).unwrap().get_name(true), "F#6");
    assert_eq!(Note::from_midi(89, false).unwrap().get_name(true), "F6");
    assert_eq!(Note::from_midi(88, false).unwrap().get_name(true), "E6");
    assert_eq!(Note::from_midi(87, false).unwrap().get_name(true), "D#6");
    assert_eq!(Note::from_midi(86, false).unwrap().get_name(true), "D6");
    assert_eq!(Note::from_midi(85, false).unwrap().get_name(true), "C#6");
    assert_eq!(Note::from_midi(84, false).unwrap().get_name(true), "C6");
    assert_eq!(Note::from_midi(83, false).unwrap().get_name(true), "B5");
    assert_eq!(Note::from_midi(82, false).unwrap().get_name(true), "A#5");
    assert_eq!(Note::from_midi(81, false).unwrap().get_name(true), "A5");
    assert_eq!(Note::from_midi(80, false).unwrap().get_name(true), "G#5");
    assert_eq!(Note::from_midi(79, false).unwrap().get_name(true), "G5");
    assert_eq!(Note::from_midi(78, false).unwrap().get_name(true), "F#5");
    assert_eq!(Note::from_midi(77, false).unwrap().get_name(true), "F5");
    assert_eq!(Note::from_midi(76, false).unwrap().get_name(true), "E5");
    assert_eq!(Note::from_midi(75, false).unwrap().get_name(true), "D#5");
    assert_eq!(Note::from_midi(74, false).unwrap().get_name(true), "D5");
    assert_eq!(Note::from_midi(73, false).unwrap().get_name(true), "C#5");
    assert_eq!(Note::from_midi(72, false).unwrap().get_name(true), "C5");
    assert_eq!(Note::from_midi(71, false).unwrap().get_name(true), "B4");
    assert_eq!(Note::from_midi(70, false).unwrap().get_name(true), "A#4");
    assert_eq!(Note::from_midi(69, false).unwrap().get_name(true), "A4");
    assert_eq!(Note::from_midi(68, false).unwrap().get_name(true), "G#4");
    assert_eq!(Note::from_midi(67, false).unwrap().get_name(true), "G4");
    assert_eq!(Note::from_midi(66, false).unwrap().get_name(true), "F#4");
    assert_eq!(Note::from_midi(65, false).unwrap().get_name(true), "F4");
    assert_eq!(Note::from_midi(64, false).unwrap().get_name(true), "E4");
    assert_eq!(Note::from_midi(63, false).unwrap().get_name(true), "D#4");
    assert_eq!(Note::from_midi(62, false).unwrap().get_name(true), "D4");
    assert_eq!(Note::from_midi(61, false).unwrap().get_name(true), "C#4");
    assert_eq!(Note::from_midi(60, false).unwrap().get_name(true), "C4");
    assert_eq!(Note::from_midi(59, false).unwrap().get_name(true), "B3");
    assert_eq!(Note::from_midi(58, false).unwrap().get_name(true), "A#3");
    assert_eq!(Note::from_midi(57, false).unwrap().get_name(true), "A3");
    assert_eq!(Note::from_midi(56, false).unwrap().get_name(true), "G#3");
    assert_eq!(Note::from_midi(55, false).unwrap().get_name(true), "G3");
    assert_eq!(Note::from_midi(54, false).unwrap().get_name(true), "F#3");
    assert_eq!(Note::from_midi(53, false).unwrap().get_name(true), "F3");
    assert_eq!(Note::from_midi(52, false).unwrap().get_name(true), "E3");
    assert_eq!(Note::from_midi(51, false).unwrap().get_name(true), "D#3");
    assert_eq!(Note::from_midi(50, false).unwrap().get_name(true), "D3");
    assert_eq!(Note::from_midi(49, false).unwrap().get_name(true), "C#3");
    assert_eq!(Note::from_midi(48, false).unwrap().get_name(true), "C3");
    assert_eq!(Note::from_midi(47, false).unwrap().get_name(true), "B2");
    assert_eq!(Note::from_midi(46, false).unwrap().get_name(true), "A#2");
    assert_eq!(Note::from_midi(45, false).unwrap().get_name(true), "A2");
    assert_eq!(Note::from_midi(44, false).unwrap().get_name(true), "G#2");
    assert_eq!(Note::from_midi(43, false).unwrap().get_name(true), "G2");
    assert_eq!(Note::from_midi(42, false).unwrap().get_name(true), "F#2");
    assert_eq!(Note::from_midi(41, false).unwrap().get_name(true), "F2");
    assert_eq!(Note::from_midi(40, false).unwrap().get_name(true), "E2");
    assert_eq!(Note::from_midi(39, false).unwrap().get_name(true), "D#2");
    assert_eq!(Note::from_midi(38, false).unwrap().get_name(true), "D2");
    assert_eq!(Note::from_midi(37, false).unwrap().get_name(true), "C#2");
    assert_eq!(Note::from_midi(36, false).unwrap().get_name(true), "C2");
    assert_eq!(Note::from_midi(35, false).unwrap().get_name(true), "B1");
    assert_eq!(Note::from_midi(34, false).unwrap().get_name(true), "A#1");
    assert_eq!(Note::from_midi(33, false).unwrap().get_name(true), "A1");
    assert_eq!(Note::from_midi(32, false).unwrap().get_name(true), "G#1");
    assert_eq!(Note::from_midi(31, false).unwrap().get_name(true), "G1");
    assert_eq!(Note::from_midi(30, false).unwrap().get_name(true), "F#1");
    assert_eq!(Note::from_midi(29, false).unwrap().get_name(true), "F1");
    assert_eq!(Note::from_midi(28, false).unwrap().get_name(true), "E1");
    assert_eq!(Note::from_midi(27, false).unwrap().get_name(true), "D#1");
    assert_eq!(Note::from_midi(26, false).unwrap().get_name(true), "D1");
    assert_eq!(Note::from_midi(25, false).unwrap().get_name(true), "C#1");
    assert_eq!(Note::from_midi(24, false).unwrap().get_name(true), "C1");
    assert_eq!(Note::from_midi(23, false).unwrap().get_name(true), "B0");
    assert_eq!(Note::from_midi(22, false).unwrap().get_name(true), "A#0");
    assert_eq!(Note::from_midi(21, false).unwrap().get_name(true), "A0");
    assert_eq!(Note::from_midi(20, false).unwrap().get_name(true), "G#0");
    assert_eq!(Note::from_midi(19, false).unwrap().get_name(true), "G0");
    assert_eq!(Note::from_midi(18, false).unwrap().get_name(true), "F#0");
    assert_eq!(Note::from_midi(17, false).unwrap().get_name(true), "F0");
    assert_eq!(Note::from_midi(16, false).unwrap().get_name(true), "E0");
    assert_eq!(Note::from_midi(15, false).unwrap().get_name(true), "D#0");
    assert_eq!(Note::from_midi(14, false).unwrap().get_name(true), "D0");
    assert_eq!(Note::from_midi(13, false).unwrap().get_name(true), "C#0");
    assert_eq!(Note::from_midi(12, false).unwrap().get_name(true), "C0");
    assert_eq!(Note::from_midi(11, false).unwrap().get_name(true), "B-1");
    assert_eq!(Note::from_midi(10, false).unwrap().get_name(true), "A#-1");
    assert_eq!(Note::from_midi(9, false).unwrap().get_name(true), "A-1");
    assert_eq!(Note::from_midi(8, false).unwrap().get_name(true), "G#-1");
    assert_eq!(Note::from_midi(7, false).unwrap().get_name(true), "G-1");
    assert_eq!(Note::from_midi(6, false).unwrap().get_name(true), "F#-1");
    assert_eq!(Note::from_midi(5, false).unwrap().get_name(true), "F-1");
    assert_eq!(Note::from_midi(4, false).unwrap().get_name(true), "E-1");
    assert_eq!(Note::from_midi(3, false).unwrap().get_name(true), "D#-1");
    assert_eq!(Note::from_midi(2, false).unwrap().get_name(true), "D-1");
    assert_eq!(Note::from_midi(1, false).unwrap().get_name(true), "C#-1");
    assert_eq!(Note::from_midi(0, false).unwrap().get_name(true), "C-1");

    assert_eq!(Note::from_midi(127, false).unwrap().get_name(false), "G9");
    assert_eq!(Note::from_midi(126, false).unwrap().get_name(false), "Gb9");
    assert_eq!(Note::from_midi(125, false).unwrap().get_name(false), "F9");
    assert_eq!(Note::from_midi(124, false).unwrap().get_name(false), "E9");
    assert_eq!(Note::from_midi(123, false).unwrap().get_name(false), "Eb9");
    assert_eq!(Note::from_midi(122, false).unwrap().get_name(false), "D9");
    assert_eq!(Note::from_midi(121, false).unwrap().get_name(false), "Db9");
    assert_eq!(Note::from_midi(120, false).unwrap().get_name(false), "C9");
    assert_eq!(Note::from_midi(119, false).unwrap().get_name(false), "B8");
    assert_eq!(Note::from_midi(118, false).unwrap().get_name(false), "Bb8");
    assert_eq!(Note::from_midi(117, false).unwrap().get_name(false), "A8");
    assert_eq!(Note::from_midi(116, false).unwrap().get_name(false), "Ab8");
    assert_eq!(Note::from_midi(115, false).unwrap().get_name(false), "G8");
    assert_eq!(Note::from_midi(114, false).unwrap().get_name(false), "Gb8");
    assert_eq!(Note::from_midi(113, false).unwrap().get_name(false), "F8");
    assert_eq!(Note::from_midi(112, false).unwrap().get_name(false), "E8");
    assert_eq!(Note::from_midi(111, false).unwrap().get_name(false), "Eb8");
    assert_eq!(Note::from_midi(110, false).unwrap().get_name(false), "D8");
    assert_eq!(Note::from_midi(109, false).unwrap().get_name(false), "Db8");
    assert_eq!(Note::from_midi(108, false).unwrap().get_name(false), "C8");
    assert_eq!(Note::from_midi(107, false).unwrap().get_name(false), "B7");
    assert_eq!(Note::from_midi(106, false).unwrap().get_name(false), "Bb7");
    assert_eq!(Note::from_midi(105, false).unwrap().get_name(false), "A7");
    assert_eq!(Note::from_midi(104, false).unwrap().get_name(false), "Ab7");
    assert_eq!(Note::from_midi(103, false).unwrap().get_name(false), "G7");
    assert_eq!(Note::from_midi(102, false).unwrap().get_name(false), "Gb7");
    assert_eq!(Note::from_midi(101, false).unwrap().get_name(false), "F7");
    assert_eq!(Note::from_midi(100, false).unwrap().get_name(false), "E7");
    assert_eq!(Note::from_midi(99, false).unwrap().get_name(false), "Eb7");
    assert_eq!(Note::from_midi(98, false).unwrap().get_name(false), "D7");
    assert_eq!(Note::from_midi(97, false).unwrap().get_name(false), "Db7");
    assert_eq!(Note::from_midi(96, false).unwrap().get_name(false), "C7");
    assert_eq!(Note::from_midi(95, false).unwrap().get_name(false), "B6");
    assert_eq!(Note::from_midi(94, false).unwrap().get_name(false), "Bb6");
    assert_eq!(Note::from_midi(93, false).unwrap().get_name(false), "A6");
    assert_eq!(Note::from_midi(92, false).unwrap().get_name(false), "Ab6");
    assert_eq!(Note::from_midi(91, false).unwrap().get_name(false), "G6");
    assert_eq!(Note::from_midi(90, false).unwrap().get_name(false), "Gb6");
    assert_eq!(Note::from_midi(89, false).unwrap().get_name(false), "F6");
    assert_eq!(Note::from_midi(88, false).unwrap().get_name(false), "E6");
    assert_eq!(Note::from_midi(87, false).unwrap().get_name(false), "Eb6");
    assert_eq!(Note::from_midi(86, false).unwrap().get_name(false), "D6");
    assert_eq!(Note::from_midi(85, false).unwrap().get_name(false), "Db6");
    assert_eq!(Note::from_midi(84, false).unwrap().get_name(false), "C6");
    assert_eq!(Note::from_midi(83, false).unwrap().get_name(false), "B5");
    assert_eq!(Note::from_midi(82, false).unwrap().get_name(false), "Bb5");
    assert_eq!(Note::from_midi(81, false).unwrap().get_name(false), "A5");
    assert_eq!(Note::from_midi(80, false).unwrap().get_name(false), "Ab5");
    assert_eq!(Note::from_midi(79, false).unwrap().get_name(false), "G5");
    assert_eq!(Note::from_midi(78, false).unwrap().get_name(false), "Gb5");
    assert_eq!(Note::from_midi(77, false).unwrap().get_name(false), "F5");
    assert_eq!(Note::from_midi(76, false).unwrap().get_name(false), "E5");
    assert_eq!(Note::from_midi(75, false).unwrap().get_name(false), "Eb5");
    assert_eq!(Note::from_midi(74, false).unwrap().get_name(false), "D5");
    assert_eq!(Note::from_midi(73, false).unwrap().get_name(false), "Db5");
    assert_eq!(Note::from_midi(72, false).unwrap().get_name(false), "C5");
    assert_eq!(Note::from_midi(71, false).unwrap().get_name(false), "B4");
    assert_eq!(Note::from_midi(70, false).unwrap().get_name(false), "Bb4");
    assert_eq!(Note::from_midi(69, false).unwrap().get_name(false), "A4");
    assert_eq!(Note::from_midi(68, false).unwrap().get_name(false), "Ab4");
    assert_eq!(Note::from_midi(67, false).unwrap().get_name(false), "G4");
    assert_eq!(Note::from_midi(66, false).unwrap().get_name(false), "Gb4");
    assert_eq!(Note::from_midi(65, false).unwrap().get_name(false), "F4");
    assert_eq!(Note::from_midi(64, false).unwrap().get_name(false), "E4");
    assert_eq!(Note::from_midi(63, false).unwrap().get_name(false), "Eb4");
    assert_eq!(Note::from_midi(62, false).unwrap().get_name(false), "D4");
    assert_eq!(Note::from_midi(61, false).unwrap().get_name(false), "Db4");
    assert_eq!(Note::from_midi(60, false).unwrap().get_name(false), "C4");
    assert_eq!(Note::from_midi(59, false).unwrap().get_name(false), "B3");
    assert_eq!(Note::from_midi(58, false).unwrap().get_name(false), "Bb3");
    assert_eq!(Note::from_midi(57, false).unwrap().get_name(false), "A3");
    assert_eq!(Note::from_midi(56, false).unwrap().get_name(false), "Ab3");
    assert_eq!(Note::from_midi(55, false).unwrap().get_name(false), "G3");
    assert_eq!(Note::from_midi(54, false).unwrap().get_name(false), "Gb3");
    assert_eq!(Note::from_midi(53, false).unwrap().get_name(false), "F3");
    assert_eq!(Note::from_midi(52, false).unwrap().get_name(false), "E3");
    assert_eq!(Note::from_midi(51, false).unwrap().get_name(false), "Eb3");
    assert_eq!(Note::from_midi(50, false).unwrap().get_name(false), "D3");
    assert_eq!(Note::from_midi(49, false).unwrap().get_name(false), "Db3");
    assert_eq!(Note::from_midi(48, false).unwrap().get_name(false), "C3");
    assert_eq!(Note::from_midi(47, false).unwrap().get_name(false), "B2");
    assert_eq!(Note::from_midi(46, false).unwrap().get_name(false), "Bb2");
    assert_eq!(Note::from_midi(45, false).unwrap().get_name(false), "A2");
    assert_eq!(Note::from_midi(44, false).unwrap().get_name(false), "Ab2");
    assert_eq!(Note::from_midi(43, false).unwrap().get_name(false), "G2");
    assert_eq!(Note::from_midi(42, false).unwrap().get_name(false), "Gb2");
    assert_eq!(Note::from_midi(41, false).unwrap().get_name(false), "F2");
    assert_eq!(Note::from_midi(40, false).unwrap().get_name(false), "E2");
    assert_eq!(Note::from_midi(39, false).unwrap().get_name(false), "Eb2");
    assert_eq!(Note::from_midi(38, false).unwrap().get_name(false), "D2");
    assert_eq!(Note::from_midi(37, false).unwrap().get_name(false), "Db2");
    assert_eq!(Note::from_midi(36, false).unwrap().get_name(false), "C2");
    assert_eq!(Note::from_midi(35, false).unwrap().get_name(false), "B1");
    assert_eq!(Note::from_midi(34, false).unwrap().get_name(false), "Bb1");
    assert_eq!(Note::from_midi(33, false).unwrap().get_name(false), "A1");
    assert_eq!(Note::from_midi(32, false).unwrap().get_name(false), "Ab1");
    assert_eq!(Note::from_midi(31, false).unwrap().get_name(false), "G1");
    assert_eq!(Note::from_midi(30, false).unwrap().get_name(false), "Gb1");
    assert_eq!(Note::from_midi(29, false).unwrap().get_name(false), "F1");
    assert_eq!(Note::from_midi(28, false).unwrap().get_name(false), "E1");
    assert_eq!(Note::from_midi(27, false).unwrap().get_name(false), "Eb1");
    assert_eq!(Note::from_midi(26, false).unwrap().get_name(false), "D1");
    assert_eq!(Note::from_midi(25, false).unwrap().get_name(false), "Db1");
    assert_eq!(Note::from_midi(24, false).unwrap().get_name(false), "C1");
    assert_eq!(Note::from_midi(23, false).unwrap().get_name(false), "B0");
    assert_eq!(Note::from_midi(22, false).unwrap().get_name(false), "Bb0");
    assert_eq!(Note::from_midi(21, false).unwrap().get_name(false), "A0");
    assert_eq!(Note::from_midi(20, false).unwrap().get_name(false), "Ab0");
    assert_eq!(Note::from_midi(19, false).unwrap().get_name(false), "G0");
    assert_eq!(Note::from_midi(18, false).unwrap().get_name(false), "Gb0");
    assert_eq!(Note::from_midi(17, false).unwrap().get_name(false), "F0");
    assert_eq!(Note::from_midi(16, false).unwrap().get_name(false), "E0");
    assert_eq!(Note::from_midi(15, false).unwrap().get_name(false), "Eb0");
    assert_eq!(Note::from_midi(14, false).unwrap().get_name(false), "D0");
    assert_eq!(Note::from_midi(13, false).unwrap().get_name(false), "Db0");
    assert_eq!(Note::from_midi(12, false).unwrap().get_name(false), "C0");
    assert_eq!(Note::from_midi(11, false).unwrap().get_name(false), "B-1");
    assert_eq!(Note::from_midi(10, false).unwrap().get_name(false), "Bb-1");
    assert_eq!(Note::from_midi(9, false).unwrap().get_name(false), "A-1");
    assert_eq!(Note::from_midi(8, false).unwrap().get_name(false), "Ab-1");
    assert_eq!(Note::from_midi(7, false).unwrap().get_name(false), "G-1");
    assert_eq!(Note::from_midi(6, false).unwrap().get_name(false), "Gb-1");
    assert_eq!(Note::from_midi(5, false).unwrap().get_name(false), "F-1");
    assert_eq!(Note::from_midi(4, false).unwrap().get_name(false), "E-1");
    assert_eq!(Note::from_midi(3, false).unwrap().get_name(false), "Eb-1");
    assert_eq!(Note::from_midi(2, false).unwrap().get_name(false), "D-1");
    assert_eq!(Note::from_midi(1, false).unwrap().get_name(false), "Db-1");
    assert_eq!(Note::from_midi(0, false).unwrap().get_name(false), "C-1");

    assert_eq!(Note::from_name("A-1").unwrap().get_midi(), (9, false));
    assert_eq!(Note::from_name("A#-1").unwrap().get_midi(), (10, true));
    assert_eq!(Note::from_name("A#0").unwrap().get_midi(), (22, true));
    assert_eq!(Note::from_name("A#1").unwrap().get_midi(), (34, true));
    assert_eq!(Note::from_name("A#2").unwrap().get_midi(), (46, true));
    assert_eq!(Note::from_name("A#3").unwrap().get_midi(), (58, true));
    assert_eq!(Note::from_name("A#4").unwrap().get_midi(), (70, true));
    assert_eq!(Note::from_name("A#5").unwrap().get_midi(), (82, true));
    assert_eq!(Note::from_name("A#6").unwrap().get_midi(), (94, true));
    assert_eq!(Note::from_name("A#7").unwrap().get_midi(), (106, true));
    assert_eq!(Note::from_name("A#8").unwrap().get_midi(), (118, true));
    assert_eq!(Note::from_name("A0").unwrap().get_midi(), (21, false));
    assert_eq!(Note::from_name("A1").unwrap().get_midi(), (33, false));
    assert_eq!(Note::from_name("A2").unwrap().get_midi(), (45, false));
    assert_eq!(Note::from_name("A3").unwrap().get_midi(), (57, false));
    assert_eq!(Note::from_name("A4").unwrap().get_midi(), (69, false));
    assert_eq!(Note::from_name("A5").unwrap().get_midi(), (81, false));
    assert_eq!(Note::from_name("A6").unwrap().get_midi(), (93, false));
    assert_eq!(Note::from_name("A7").unwrap().get_midi(), (105, false));
    assert_eq!(Note::from_name("A8").unwrap().get_midi(), (117, false));
    assert_eq!(Note::from_name("Ab-1").unwrap().get_midi(), (8, true));
    assert_eq!(Note::from_name("Ab0").unwrap().get_midi(), (20, true));
    assert_eq!(Note::from_name("Ab1").unwrap().get_midi(), (32, true));
    assert_eq!(Note::from_name("Ab2").unwrap().get_midi(), (44, true));
    assert_eq!(Note::from_name("Ab3").unwrap().get_midi(), (56, true));
    assert_eq!(Note::from_name("Ab4").unwrap().get_midi(), (68, true));
    assert_eq!(Note::from_name("Ab5").unwrap().get_midi(), (80, true));
    assert_eq!(Note::from_name("Ab6").unwrap().get_midi(), (92, true));
    assert_eq!(Note::from_name("Ab7").unwrap().get_midi(), (104, true));
    assert_eq!(Note::from_name("Ab8").unwrap().get_midi(), (116, true));
    assert_eq!(Note::from_name("B-1").unwrap().get_midi(), (11, false));
    assert_eq!(Note::from_name("B0").unwrap().get_midi(), (23, false));
    assert_eq!(Note::from_name("B1").unwrap().get_midi(), (35, false));
    assert_eq!(Note::from_name("B2").unwrap().get_midi(), (47, false));
    assert_eq!(Note::from_name("B3").unwrap().get_midi(), (59, false));
    assert_eq!(Note::from_name("B4").unwrap().get_midi(), (71, false));
    assert_eq!(Note::from_name("B5").unwrap().get_midi(), (83, false));
    assert_eq!(Note::from_name("B6").unwrap().get_midi(), (95, false));
    assert_eq!(Note::from_name("B7").unwrap().get_midi(), (107, false));
    assert_eq!(Note::from_name("B8").unwrap().get_midi(), (119, false));
    assert_eq!(Note::from_name("Bb-1").unwrap().get_midi(), (10, true));
    assert_eq!(Note::from_name("Bb0").unwrap().get_midi(), (22, true));
    assert_eq!(Note::from_name("Bb1").unwrap().get_midi(), (34, true));
    assert_eq!(Note::from_name("Bb2").unwrap().get_midi(), (46, true));
    assert_eq!(Note::from_name("Bb3").unwrap().get_midi(), (58, true));
    assert_eq!(Note::from_name("Bb4").unwrap().get_midi(), (70, true));
    assert_eq!(Note::from_name("Bb5").unwrap().get_midi(), (82, true));
    assert_eq!(Note::from_name("Bb6").unwrap().get_midi(), (94, true));
    assert_eq!(Note::from_name("Bb7").unwrap().get_midi(), (106, true));
    assert_eq!(Note::from_name("Bb8").unwrap().get_midi(), (118, true));
    assert_eq!(Note::from_name("C-1").unwrap().get_midi(), (0, false));
    assert_eq!(Note::from_name("C#-1").unwrap().get_midi(), (1, true));
    assert_eq!(Note::from_name("C#0").unwrap().get_midi(), (13, true));
    assert_eq!(Note::from_name("C#1").unwrap().get_midi(), (25, true));
    assert_eq!(Note::from_name("C#2").unwrap().get_midi(), (37, true));
    assert_eq!(Note::from_name("C#3").unwrap().get_midi(), (49, true));
    assert_eq!(Note::from_name("C#4").unwrap().get_midi(), (61, true));
    assert_eq!(Note::from_name("C#5").unwrap().get_midi(), (73, true));
    assert_eq!(Note::from_name("C#6").unwrap().get_midi(), (85, true));
    assert_eq!(Note::from_name("C#7").unwrap().get_midi(), (97, true));
    assert_eq!(Note::from_name("C#8").unwrap().get_midi(), (109, true));
    assert_eq!(Note::from_name("C#9").unwrap().get_midi(), (121, true));
    assert_eq!(Note::from_name("C0").unwrap().get_midi(), (12, false));
    assert_eq!(Note::from_name("C1").unwrap().get_midi(), (24, false));
    assert_eq!(Note::from_name("C2").unwrap().get_midi(), (36, false));
    assert_eq!(Note::from_name("C3").unwrap().get_midi(), (48, false));
    assert_eq!(Note::from_name("C4").unwrap().get_midi(), (60, false));
    assert_eq!(Note::from_name("C5").unwrap().get_midi(), (72, false));
    assert_eq!(Note::from_name("C6").unwrap().get_midi(), (84, false));
    assert_eq!(Note::from_name("C7").unwrap().get_midi(), (96, false));
    assert_eq!(Note::from_name("C8").unwrap().get_midi(), (108, false));
    assert_eq!(Note::from_name("C9").unwrap().get_midi(), (120, false));
    assert_eq!(Note::from_name("D-1").unwrap().get_midi(), (2, false));
    assert_eq!(Note::from_name("D#-1").unwrap().get_midi(), (3, true));
    assert_eq!(Note::from_name("D#0").unwrap().get_midi(), (15, true));
    assert_eq!(Note::from_name("D#1").unwrap().get_midi(), (27, true));
    assert_eq!(Note::from_name("D#2").unwrap().get_midi(), (39, true));
    assert_eq!(Note::from_name("D#3").unwrap().get_midi(), (51, true));
    assert_eq!(Note::from_name("D#4").unwrap().get_midi(), (63, true));
    assert_eq!(Note::from_name("D#5").unwrap().get_midi(), (75, true));
    assert_eq!(Note::from_name("D#6").unwrap().get_midi(), (87, true));
    assert_eq!(Note::from_name("D#7").unwrap().get_midi(), (99, true));
    assert_eq!(Note::from_name("D#8").unwrap().get_midi(), (111, true));
    assert_eq!(Note::from_name("D#9").unwrap().get_midi(), (123, true));
    assert_eq!(Note::from_name("D0").unwrap().get_midi(), (14, false));
    assert_eq!(Note::from_name("D1").unwrap().get_midi(), (26, false));
    assert_eq!(Note::from_name("D2").unwrap().get_midi(), (38, false));
    assert_eq!(Note::from_name("D3").unwrap().get_midi(), (50, false));
    assert_eq!(Note::from_name("D4").unwrap().get_midi(), (62, false));
    assert_eq!(Note::from_name("D5").unwrap().get_midi(), (74, false));
    assert_eq!(Note::from_name("D6").unwrap().get_midi(), (86, false));
    assert_eq!(Note::from_name("D7").unwrap().get_midi(), (98, false));
    assert_eq!(Note::from_name("D8").unwrap().get_midi(), (110, false));
    assert_eq!(Note::from_name("D9").unwrap().get_midi(), (122, false));
    assert_eq!(Note::from_name("Db-1").unwrap().get_midi(), (1, true));
    assert_eq!(Note::from_name("Db0").unwrap().get_midi(), (13, true));
    assert_eq!(Note::from_name("Db1").unwrap().get_midi(), (25, true));
    assert_eq!(Note::from_name("Db2").unwrap().get_midi(), (37, true));
    assert_eq!(Note::from_name("Db3").unwrap().get_midi(), (49, true));
    assert_eq!(Note::from_name("Db4").unwrap().get_midi(), (61, true));
    assert_eq!(Note::from_name("Db5").unwrap().get_midi(), (73, true));
    assert_eq!(Note::from_name("Db6").unwrap().get_midi(), (85, true));
    assert_eq!(Note::from_name("Db7").unwrap().get_midi(), (97, true));
    assert_eq!(Note::from_name("Db8").unwrap().get_midi(), (109, true));
    assert_eq!(Note::from_name("Db9").unwrap().get_midi(), (121, true));
    assert_eq!(Note::from_name("E-1").unwrap().get_midi(), (4, false));
    assert_eq!(Note::from_name("E0").unwrap().get_midi(), (16, false));
    assert_eq!(Note::from_name("E1").unwrap().get_midi(), (28, false));
    assert_eq!(Note::from_name("E2").unwrap().get_midi(), (40, false));
    assert_eq!(Note::from_name("E3").unwrap().get_midi(), (52, false));
    assert_eq!(Note::from_name("E4").unwrap().get_midi(), (64, false));
    assert_eq!(Note::from_name("E5").unwrap().get_midi(), (76, false));
    assert_eq!(Note::from_name("E6").unwrap().get_midi(), (88, false));
    assert_eq!(Note::from_name("E7").unwrap().get_midi(), (100, false));
    assert_eq!(Note::from_name("E8").unwrap().get_midi(), (112, false));
    assert_eq!(Note::from_name("E9").unwrap().get_midi(), (124, false));
    assert_eq!(Note::from_name("Eb-1").unwrap().get_midi(), (3, true));
    assert_eq!(Note::from_name("Eb0").unwrap().get_midi(), (15, true));
    assert_eq!(Note::from_name("Eb1").unwrap().get_midi(), (27, true));
    assert_eq!(Note::from_name("Eb2").unwrap().get_midi(), (39, true));
    assert_eq!(Note::from_name("Eb3").unwrap().get_midi(), (51, true));
    assert_eq!(Note::from_name("Eb4").unwrap().get_midi(), (63, true));
    assert_eq!(Note::from_name("Eb5").unwrap().get_midi(), (75, true));
    assert_eq!(Note::from_name("Eb6").unwrap().get_midi(), (87, true));
    assert_eq!(Note::from_name("Eb7").unwrap().get_midi(), (99, true));
    assert_eq!(Note::from_name("Eb8").unwrap().get_midi(), (111, true));
    assert_eq!(Note::from_name("Eb9").unwrap().get_midi(), (123, true));
    assert_eq!(Note::from_name("F-1").unwrap().get_midi(), (5, false));
    assert_eq!(Note::from_name("F#-1").unwrap().get_midi(), (6, true));
    assert_eq!(Note::from_name("F#0").unwrap().get_midi(), (18, true));
    assert_eq!(Note::from_name("F#1").unwrap().get_midi(), (30, true));
    assert_eq!(Note::from_name("F#2").unwrap().get_midi(), (42, true));
    assert_eq!(Note::from_name("F#3").unwrap().get_midi(), (54, true));
    assert_eq!(Note::from_name("F#4").unwrap().get_midi(), (66, true));
    assert_eq!(Note::from_name("F#5").unwrap().get_midi(), (78, true));
    assert_eq!(Note::from_name("F#6").unwrap().get_midi(), (90, true));
    assert_eq!(Note::from_name("F#7").unwrap().get_midi(), (102, true));
    assert_eq!(Note::from_name("F#8").unwrap().get_midi(), (114, true));
    assert_eq!(Note::from_name("F#9").unwrap().get_midi(), (126, true));
    assert_eq!(Note::from_name("F0").unwrap().get_midi(), (17, false));
    assert_eq!(Note::from_name("F1").unwrap().get_midi(), (29, false));
    assert_eq!(Note::from_name("F2").unwrap().get_midi(), (41, false));
    assert_eq!(Note::from_name("F3").unwrap().get_midi(), (53, false));
    assert_eq!(Note::from_name("F4").unwrap().get_midi(), (65, false));
    assert_eq!(Note::from_name("F5").unwrap().get_midi(), (77, false));
    assert_eq!(Note::from_name("F6").unwrap().get_midi(), (89, false));
    assert_eq!(Note::from_name("F7").unwrap().get_midi(), (101, false));
    assert_eq!(Note::from_name("F8").unwrap().get_midi(), (113, false));
    assert_eq!(Note::from_name("F9").unwrap().get_midi(), (125, false));
    assert_eq!(Note::from_name("G-1").unwrap().get_midi(), (7, false));
    assert_eq!(Note::from_name("G#-1").unwrap().get_midi(), (8, true));
    assert_eq!(Note::from_name("G#0").unwrap().get_midi(), (20, true));
    assert_eq!(Note::from_name("G#1").unwrap().get_midi(), (32, true));
    assert_eq!(Note::from_name("G#2").unwrap().get_midi(), (44, true));
    assert_eq!(Note::from_name("G#3").unwrap().get_midi(), (56, true));
    assert_eq!(Note::from_name("G#4").unwrap().get_midi(), (68, true));
    assert_eq!(Note::from_name("G#5").unwrap().get_midi(), (80, true));
    assert_eq!(Note::from_name("G#6").unwrap().get_midi(), (92, true));
    assert_eq!(Note::from_name("G#7").unwrap().get_midi(), (104, true));
    assert_eq!(Note::from_name("G#8").unwrap().get_midi(), (116, true));
    assert_eq!(Note::from_name("G0").unwrap().get_midi(), (19, false));
    assert_eq!(Note::from_name("G1").unwrap().get_midi(), (31, false));
    assert_eq!(Note::from_name("G2").unwrap().get_midi(), (43, false));
    assert_eq!(Note::from_name("G3").unwrap().get_midi(), (55, false));
    assert_eq!(Note::from_name("G4").unwrap().get_midi(), (67, false));
    assert_eq!(Note::from_name("G5").unwrap().get_midi(), (79, false));
    assert_eq!(Note::from_name("G6").unwrap().get_midi(), (91, false));
    assert_eq!(Note::from_name("G7").unwrap().get_midi(), (103, false));
    assert_eq!(Note::from_name("G8").unwrap().get_midi(), (115, false));
    assert_eq!(Note::from_name("G9").unwrap().get_midi(), (127, false));
    assert_eq!(Note::from_name("Gb-1").unwrap().get_midi(), (6, true));
    assert_eq!(Note::from_name("Gb0").unwrap().get_midi(), (18, true));
    assert_eq!(Note::from_name("Gb1").unwrap().get_midi(), (30, true));
    assert_eq!(Note::from_name("Gb2").unwrap().get_midi(), (42, true));
    assert_eq!(Note::from_name("Gb3").unwrap().get_midi(), (54, true));
    assert_eq!(Note::from_name("Gb4").unwrap().get_midi(), (66, true));
    assert_eq!(Note::from_name("Gb5").unwrap().get_midi(), (78, true));
    assert_eq!(Note::from_name("Gb6").unwrap().get_midi(), (90, true));
    assert_eq!(Note::from_name("Gb7").unwrap().get_midi(), (102, true));
    assert_eq!(Note::from_name("Gb8").unwrap().get_midi(), (114, true));
    assert_eq!(Note::from_name("Gb9").unwrap().get_midi(), (126, true));

    assert_eq!(Note::from_name("G#9"), None);
    assert_eq!(Note::from_name("G##9"), None);
    assert_eq!(Note::from_name("g##9"), None);
    assert_eq!(Note::from_name("Cb-1"), None);
    assert_eq!(Note::from_name("G3n").unwrap().get_midi(), (55, true));
    assert_eq!(Note::from_name("Gn3").unwrap().get_midi(), (55, true));
    assert_eq!(Note::from_name("Gn3n").unwrap().get_midi(), (55, true));
    assert_eq!(Note::from_name("Gn3nnnnnn").unwrap().get_midi(), (55, true));
    assert_eq!(Note::from_name("G10bbbbbbbbbbbb").unwrap().get_midi(), (127, true));
    assert_eq!(Note::from_name("g10bbbbbbbbbbbbb").unwrap().get_midi(), (126, true));
    assert_eq!(Note::from_name("Gb10bbbbbbbbbbbbb").unwrap().get_midi(), (125, true));
    assert_eq!(Note::from_name("gbb10bb♭bbb♭♭♭bb♭b").unwrap().get_midi(), (124, true));
    assert_eq!(Note::from_name("G♭bb10bbbbbbbbbbbbb").unwrap().get_midi(), (123, true));
    assert_eq!(Note::from_name("Gbbb+10bbbbbbbbbbbbb").unwrap().get_midi(), (123, true));
    assert_eq!(Note::from_name("C######-2######").unwrap().get_midi(), (0, true));
    assert_eq!(Note::from_name("c######-2#######").unwrap().get_midi(), (1, true));
    assert_eq!(Note::from_name("C#♯♯ss#-2#♯##♯#s#").unwrap().get_midi(), (2, true));
    assert_eq!(Note::from_name(" C#♯♯ss#-2#♯##♯#s#").unwrap().get_midi(), (2, true));
    assert_eq!(Note::from_name("  \t  C#♯♯ss#-2#♯##♯#s#    ").unwrap().get_midi(), (2, true));
    assert_eq!(Note::from_name("  \t  C#♯♯ss#-2#♯##♯#s#  \n\t\r  ").unwrap().get_midi(), (2, true));
}
