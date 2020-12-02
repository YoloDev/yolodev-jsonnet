mod expr;
mod fun;
mod helpers;
mod lazy;
mod runtime;
mod val;

pub use runtime::{Loader, Resolver, Runtime, RuntimeBuilder};
pub use val::{StringValue, Value};

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_5() {
    let runtime = Runtime::default();
    let v = runtime.run("5 + 3", "test.jsonnet".as_ref()).unwrap();
    match v {
      Value::Double(v) => assert_eq!(v, 8.0),
      _ => assert!(false, "Value was wrong: {:?}", v),
    }
  }
}
