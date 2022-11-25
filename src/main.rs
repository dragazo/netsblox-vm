use netsblox_vm::cli::{run, Mode};
use netsblox_vm::runtime::{StdSystemConfig, CustomTypes, GetType, Value, StdSystem, ErrorCause};
use netsblox_vm::gc::MutationContext;
use netsblox_vm::json::Json;
use clap::Parser;

#[derive(Debug)]
enum NativeValue {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeType {}

impl GetType for NativeValue {
    type Output = NativeType;
    fn get_type(&self) -> Self::Output {
        unreachable!()
    }
}

struct C;
impl CustomTypes for C {
    type NativeValue = NativeValue;
    type Intermediate = Json;

    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, StdSystem<Self>>, ErrorCause<StdSystem<Self>>> {
        Ok(Value::from_json(mc, value)?)
    }
    fn to_intermediate<'gc>(value: Value<'gc, StdSystem<Self>>) -> Result<Self::Intermediate, ErrorCause<StdSystem<Self>>> {
        Ok(value.to_json()?)
    }
}

fn main() {
    run::<C>(Mode::parse(), StdSystemConfig::default(), &[]);
}
