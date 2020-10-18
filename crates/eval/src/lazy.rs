use std::{
  collections::HashMap,
  fmt::{self, Debug},
  num::NonZeroU32,
};

use gc::{Gc, GcCell, Trace};
use jsonnet_core_lang::TextRange;

use crate::{val::PartialValue, Value};

#[derive(Debug, Clone, Copy)]
pub struct Location(Option<TextRange>);

impl From<Option<TextRange>> for Location {
  #[inline]
  fn from(l: Option<TextRange>) -> Self {
    Location(l)
  }
}

impl From<TextRange> for Location {
  #[inline]
  fn from(l: TextRange) -> Self {
    Location(Some(l))
  }
}

unsafe impl Trace for Location {
  gc::custom_trace! {this, { }}
}

pub(crate) trait Expression: Trace + Debug {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError>;

  fn is_computed(&self) -> bool {
    false
  }
}

#[derive(Trace)]
struct ConstExpr(Gc<Value>);

impl Debug for ConstExpr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl Expression for ConstExpr {
  #[inline]
  fn eval(&self, _: &LazyValue) -> Result<Gc<Value>, EvalError> {
    Ok(self.0.clone())
  }

  #[inline]
  fn is_computed(&self) -> bool {
    true
  }
}

#[derive(Trace, Debug, Clone)]
pub(crate) struct LazyValue(Gc<GcCell<Gc<dyn Expression>>>);

impl LazyValue {
  pub(crate) fn new(expr: impl Expression + 'static) -> Self {
    LazyValue(Gc::new(GcCell::new(Gc::new(expr))))
  }

  pub(crate) fn force(&self) -> Result<Gc<Value>, EvalError> {
    let expr = self.0.borrow().clone();

    expr.eval(self)
  }

  pub(crate) fn is_computed(&self) -> bool {
    self.0.borrow().is_computed()
  }

  pub(crate) fn update(&self, value: Gc<Value>) -> Gc<Value> {
    *self.0.borrow_mut() = Gc::new(ConstExpr(value.clone()));
    value
  }
}

impl From<Value> for LazyValue {
  #[inline]
  fn from(value: Value) -> Self {
    LazyValue::new(ConstExpr(Gc::new(value)))
  }
}

impl From<bool> for LazyValue {
  #[inline]
  fn from(value: bool) -> Self {
    Value::Bool(value).into()
  }
}

#[derive(Trace, Clone)]
pub(crate) struct EvalContext {
  pub(crate) super_value: Option<LazyValue>,
  pub(crate) args: HashMap<NonZeroU32, LazyValue>,
}

impl EvalContext {
  pub(crate) fn with_super(&self, value: LazyValue) -> Self {
    EvalContext {
      super_value: Some(value),
      args: self.args.clone(),
    }
  }

  pub(crate) fn get_arg(&self, id: &NonZeroU32) -> Result<LazyValue, EvalError> {
    self
      .args
      .get(id)
      .map(Clone::clone)
      .ok_or_else(|| EvalError::new("Failed to get argument", None))
  }
}

pub struct EvalError {
  message: Box<str>,
  location: Location,
}

impl EvalError {
  #[inline]
  pub(crate) fn new(message: impl Into<Box<str>>, location: impl Into<Location>) -> Self {
    EvalError {
      message: message.into(),
      location: location.into(),
    }
  }
}

pub(crate) trait LateBound: Trace + Debug {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError>;

  fn into_partial(self) -> PartialValue;
}

#[derive(Trace, Debug, Clone)]
pub(crate) struct LateBoundValue(Gc<dyn LateBound>);

impl LateBoundValue {
  #[inline]
  pub(crate) fn from_latebound(value: impl LateBound + 'static) -> Self {
    Self(Gc::new(value))
  }

  #[inline]
  pub(crate) fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    self.0.eval(ctx)
  }
}
