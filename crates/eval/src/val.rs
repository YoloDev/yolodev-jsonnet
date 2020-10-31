use std::{
  borrow::Borrow,
  fmt::{self, Debug},
  ops::Deref,
  rc::Rc,
};

use gc::{Gc, GcCell, GcCellRef, Trace};

use crate::lazy::{EvalContext, EvalError, LateBound, LateBoundValue, LazyValue};

#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone)]
pub struct StringValue(pub(crate) Rc<str>);

impl Debug for StringValue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl AsRef<str> for StringValue {
  #[inline]
  fn as_ref(&self) -> &str {
    &self.0
  }
}

impl Borrow<str> for StringValue {
  #[inline]
  fn borrow(&self) -> &str {
    &self.0
  }
}

impl Deref for StringValue {
  type Target = str;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

unsafe impl Trace for StringValue {
  gc::custom_trace! {this, {}}
}

impl From<&str> for StringValue {
  #[inline]
  fn from(v: &str) -> Self {
    StringValue(v.into())
  }
}

pub enum ValueKind {
  Null,
  Bool,
  String,
  Number,
  Object,
  Array,
  Function,
}

#[derive(Debug)]
pub enum Value {
  Null,
  Bool(bool),
  String(StringValue),
  Double(f64),
  Object(Object),
  Array(Array),
  Function(Function),
}

impl Value {
  pub fn as_bool(&self) -> Option<bool> {
    match self {
      Self::Bool(v) => Some(*v),
      _ => None,
    }
  }

  pub fn as_string(&self) -> Option<&StringValue> {
    match self {
      Self::String(v) => Some(v),
      _ => None,
    }
  }

  pub fn as_double(&self) -> Option<f64> {
    match self {
      Self::Double(v) => Some(*v),
      _ => None,
    }
  }

  pub fn as_object(&self) -> Option<&Object> {
    match self {
      Self::Object(v) => Some(v),
      _ => None,
    }
  }

  pub fn as_array(&self) -> Option<&Array> {
    match self {
      Self::Array(v) => Some(v),
      _ => None,
    }
  }

  pub fn as_function(&self) -> Option<&Function> {
    match self {
      Self::Function(v) => Some(v),
      _ => None,
    }
  }

  pub fn is_truthy(&self) -> bool {
    match self {
      Value::Null => false,
      Value::Bool(v) => *v,
      Value::String(v) => v.len() > 0,
      Value::Double(v) => *v != 0.0,
      Value::Object(_) => true,
      Value::Array(_) => true,
      Value::Function(_) => true,
    }
  }
}

impl From<Object> for Value {
  #[inline]
  fn from(v: Object) -> Self {
    Value::Object(v)
  }
}

impl From<Array> for Value {
  #[inline]
  fn from(v: Array) -> Self {
    Value::Array(v)
  }
}

impl From<Function> for Value {
  #[inline]
  fn from(v: Function) -> Self {
    Value::Function(v)
  }
}

impl From<StringValue> for Value {
  #[inline]
  fn from(v: StringValue) -> Self {
    Value::String(v)
  }
}

impl Value {
  pub fn kind(&self) -> ValueKind {
    match self {
      Self::Null => ValueKind::Null,
      Self::Bool(_) => ValueKind::Bool,
      Self::String(_) => ValueKind::String,
      Self::Double(_) => ValueKind::Number,
      Self::Object(_) => ValueKind::Object,
      Self::Array(_) => ValueKind::Array,
      Self::Function(_) => ValueKind::Function,
    }
  }
}

unsafe impl Trace for Value {
  gc::custom_trace! {this, {
    match this {
      Value::Object(o) => mark(o),
      Value::Array(a) => mark(a),
      Value::Function(f) => mark(f),
      _ => (),
    }
  }}
}

#[derive(Debug, Trace)]
pub struct ObjectProperty {
  pub(crate) name: LazyValue,
  pub(crate) value: LazyValue,
  pub(crate) visible: bool,
}

#[derive(Debug, Trace)]
pub struct Object {
  pub properties: Gc<Vec<ObjectProperty>>,
}

impl Object {
  pub fn get(&self, name: &StringValue) -> Result<Option<&ObjectProperty>, EvalError> {
    // first, check the ones where the name is already evaluated
    for prop in self.properties.iter().filter(|p| p.name.is_computed()) {
      let name_val = prop.name.force()?;
      if name_val.as_string() == Some(name) {
        return Ok(Some(prop));
      }
    }

    // next, go through and force the values
    for prop in self.properties.iter() {
      let name_val = prop.name.force()?;
      let field_name = name_val
        .as_string()
        .ok_or_else(|| EvalError::new("Object field names must be strings", None))?;

      if field_name == name {
        return Ok(Some(prop));
      }
    }

    Ok(None)
  }
}

#[derive(Debug, Trace)]
pub struct Array {
  pub(crate) items: Gc<Vec<LazyValue>>,
}

#[derive(Debug, Trace)]
pub struct Function;

#[derive(Trace, Debug, Clone)]
pub(crate) enum PartialValueInner {
  Value(LazyValue),
  Partial(LateBoundValue),
}

#[derive(Trace, Debug, Clone)]
pub(crate) struct PartialValue(Gc<GcCell<PartialValueInner>>);

impl From<Value> for PartialValue {
  #[inline]
  fn from(v: Value) -> Self {
    PartialValueInner::Value(v.into()).into()
  }
}

impl From<LazyValue> for PartialValue {
  #[inline]
  fn from(v: LazyValue) -> Self {
    PartialValueInner::Value(v).into()
  }
}

impl From<LateBoundValue> for PartialValue {
  #[inline]
  fn from(v: LateBoundValue) -> Self {
    PartialValueInner::Partial(v).into()
  }
}

impl From<PartialValueInner> for PartialValue {
  fn from(inner: PartialValueInner) -> Self {
    Self(Gc::new(GcCell::new(inner)))
  }
}

impl PartialValue {
  #[inline]
  pub(crate) fn borrow(&self) -> GcCellRef<PartialValueInner> {
    self.0.deref().borrow()
  }

  pub(crate) fn assign(self, value: impl LateBound + 'static) -> PartialValue {
    *self.0.deref().borrow_mut() = PartialValueInner::Partial(LateBoundValue::new(value));

    self
  }

  pub(crate) fn is_bound(&self) -> bool {
    match self.borrow().deref() {
      PartialValueInner::Value(v) => true,
      PartialValueInner::Partial(_) => false,
    }
  }

  pub(crate) fn as_value(&self) -> Option<LazyValue> {
    match self.borrow().deref() {
      PartialValueInner::Value(v) => Some(v.clone()),
      PartialValueInner::Partial(_) => None,
    }
  }

  pub(crate) fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    match self.borrow().deref() {
      PartialValueInner::Value(v) => Ok(v.clone()),
      PartialValueInner::Partial(p) => p.eval(ctx),
    }
  }
}
