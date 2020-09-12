use crate::*;
use lang::*;
use std::{collections::HashMap, num::NonZeroU32, rc::Rc};

trait IntoExpr {
  fn into_expr(
    self,
    self_value: Option<GcValue>,
    super_value: Option<GcValue>,
    locals: &mut HashMap<NonZeroU32, GcValue>,
  ) -> Gc<dyn Expr>;
}

impl<E: Expr + 'static> IntoExpr for E {
  #[inline]
  fn into_expr(
    self,
    _self_value: Option<GcValue>,
    _super_value: Option<GcValue>,
    _locals: &mut HashMap<NonZeroU32, GcValue>,
  ) -> Gc<dyn Expr> {
    Gc::new(self)
  }
}

#[derive(Debug, Trace)]
struct ConstValue(GcValue);

#[derive(Debug, Trace)]
struct ErrorValue(String);

#[derive(Debug)]
enum LiteralExpr {
  Null,
  True,
  False,
  String(Rc<str>),
  Number(f64),
}

unsafe impl Trace for LiteralExpr {
  gc::unsafe_empty_trace! {}
}

impl Expr for LiteralExpr {
  fn eval(&self) -> Value {
    match self {
      LiteralExpr::Null => Value::Null,
      LiteralExpr::True => Value::Bool(true),
      LiteralExpr::False => Value::Bool(false),
      LiteralExpr::String(s) => Value::String(s.clone()),
      LiteralExpr::Number(s) => Value::Double(*s),
    }
  }
}

impl IntoExpr for LiteralCoreExpr {
  fn into_expr(
    self,
    self_value: Option<GcValue>,
    super_value: Option<GcValue>,
    locals: &mut HashMap<NonZeroU32, GcValue>,
  ) -> Gc<dyn Expr> {
    match self.value() {
      CoreLiteral::Null => LiteralExpr::Null,
      CoreLiteral::Bool(true) => LiteralExpr::True,
      CoreLiteral::Bool(false) => LiteralExpr::False,
      CoreLiteral::String(s) => LiteralExpr::String(s.into()),
      CoreLiteral::Number(n) => LiteralExpr::Number(n),
    }
    .into_expr(self_value, super_value, locals)
  }
}
