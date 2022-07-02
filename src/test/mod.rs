use std::prelude::v1::*;
use std::iter;

use crate::runtime::*;
use crate::process::*;

mod process;
mod project;

fn assert_values_eq<'gc>(got: &Value<'gc>, expected: &Value<'gc>, epsilon: f64, path: &str) {
    if got.get_type() != expected.get_type() {
        panic!("{} - type error - got {:?} expected {:?} - {:?}", path, got.get_type(), expected.get_type(), got);
    }
    match (got, expected) {
        (Value::Bool(got), Value::Bool(expected)) => {
            if got != expected { panic!("{} - bool error - got {} expected {}", path, got, expected) }
        }
        (Value::Number(got), Value::Number(expected)) => {
            let good = if got.is_finite() && expected.is_finite() { (got - expected).abs() <= epsilon } else { got == expected };
            if !good { panic!("{} - number error - got {} expected {}", path, got, expected) }
        }
        (Value::String(got), Value::String(expected)) => {
            if got.as_str() != expected.as_str() { panic!("{} - string error - got {:?} expected {:?}", path, got, expected) }
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
