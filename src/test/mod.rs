use std::prelude::v1::*;
use std::rc::Rc;
use std::iter;

use crate::runtime::*;
use crate::process::*;
use crate::std_system::*;
use crate::json::*;
use crate::gc::*;

mod process;
mod project;

const BASE_URL: &'static str = "https://editor.netsblox.org";

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

fn default_properties_config() -> Config<C, StdSystem<C>> {
    Config {
        request: Some(Rc::new(|_, _, key, request, entity| match request {
            Request::Property { prop } => entity.state.props.perform_get_property(key, prop),
            _ => RequestStatus::UseDefault { key, request },
        })),
        command: Some(Rc::new(|_, _, key, command, entity| match command {
            Command::SetProperty { prop, value } => entity.state.props.perform_set_property(key, prop, value),
            Command::ChangeProperty { prop, delta } => entity.state.props.perform_change_property(key, prop, delta),
            Command::ClearEffects => entity.state.props.perform_clear_effects(key),
            Command::GotoXY { x, y } => entity.state.props.perform_goto_xy(key, x, y),
            Command::PointTowardsXY { x, y } => entity.state.props.perform_point_towards_xy(key, x, y),
            Command::Forward { distance } => entity.state.props.perform_forward(key, distance),
            _ => CommandStatus::UseDefault { key, command },
        })),
    }
}

enum Intermediate {
    Json(Json),
    Image(Vec<u8>),
    Audio(Vec<u8>),
}
impl IntermediateType for Intermediate {
    fn from_json(json: Json) -> Self {
        Self::Json(json)
    }
    fn from_image(img: Vec<u8>) -> Self {
        Self::Image(img)
    }
    fn from_audio(audio: Vec<u8>) -> Self {
        Self::Audio(audio)
    }
}

struct C;
impl CustomTypes<StdSystem<C>> for C {
    type NativeValue = NativeValue;
    type Intermediate = Intermediate;

    type EntityState = EntityState;

    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, C, StdSystem<C>>, ErrorCause<C, StdSystem<C>>> {
        Ok(match value {
            Intermediate::Json(x) => Value::from_json(mc, x)?,
            Intermediate::Image(x) => Value::Image(Rc::new(x)),
            Intermediate::Audio(x) => Value::Audio(Rc::new(x)),
        })
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
            let good = if got.is_finite() && expected.is_finite() { (got - expected).abs() <= epsilon } else { got == expected };
            if !good { panic!("{} - number error - got {} expected {}", path, got, expected) }
        }
        (Value::String(got), Value::String(expected)) => {
            if got.as_str() != expected.as_str() { panic!("{} - string error - got {:?} expected {:?}", path, got.as_str(), expected.as_str()) }
        }
        (Value::List(got), Value::List(expected)) => {
            let got = got.read();
            let expected = expected.read();

            if got.len() != expected.len() { panic!("{} - list len error - got {} expected {}\ngot:      {:?}\nexpected: {:?}", path, got.len(), expected.len(), got, expected) }

            for (i, (got, expected)) in iter::zip(got.iter(), expected.iter()).enumerate() {
                assert_values_eq(got, expected, epsilon, &format!("{}[{}]", path, i));
            }
        }
        (x, y) => unimplemented!("types: {:?} {:?}", x.get_type(), y.get_type()),
    }
}
