use netsblox_vm::cli::{run, Mode};
use netsblox_vm::runtime::{GetType, Value, ErrorCause, EntityKind, System};
use netsblox_vm::std_system::{Config, CustomTypes, StdSystem};
use netsblox_vm::gc::MutationContext;
use netsblox_vm::json::Json;
use clap::Parser;

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

struct EntityState;
impl<S: System> From<EntityKind<'_, '_, S>> for EntityState {
    fn from(_: EntityKind<'_, '_, S>) -> Self {
        EntityState
    }
}

struct C;
impl CustomTypes for C {
    type NativeValue = NativeValue;
    type Intermediate = Json;

    type EntityState = EntityState;

    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, StdSystem<Self>>, ErrorCause<StdSystem<Self>>> {
        Ok(Value::from_json(mc, value)?)
    }
    fn to_intermediate(value: Value<'_, StdSystem<Self>>) -> Result<Self::Intermediate, ErrorCause<StdSystem<Self>>> {
        Ok(value.to_json()?)
    }
}

fn main() {
    run::<C>(Mode::parse(), Config::default(), &[]);
}
