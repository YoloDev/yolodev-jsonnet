use std::{collections::HashMap, num::NonZeroU32};

use crate::{
  helpers::ReplaceWithDefault,
  lazy::{EvalContext, EvalError, Expression, LateBound, LateBoundValue, LazyValue, Location},
  val::Array,
  val::Object,
  val::ObjectProperty,
  val::PartialValue,
  StringValue, Value,
};
use gc::{Gc, Trace};
use jsonnet_core_lang::*;

#[derive(Trace, Debug)]
struct UnsetValue;

impl LateBound for UnsetValue {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    panic!("Unset value")
  }

  #[inline]
  fn into_partial(self) -> PartialValue {
    LateBoundValue::new(self).into()
  }
}

pub struct BindingError {
  pub(crate) message: Box<str>,
  pub(crate) location: Location,
}

impl BindingError {
  #[inline]
  pub(crate) fn new(message: impl Into<Box<str>>, location: impl Into<Location>) -> Self {
    BindingError {
      message: message.into(),
      location: location.into(),
    }
  }
}

#[derive(Clone, Trace)]
struct Binder {
  self_value: Option<PartialValue>,
  locals: HashMap<NonZeroU32, PartialValue>,
}

impl Binder {
  fn new() -> Binder {
    Binder {
      self_value: None,
      locals: HashMap::new(),
    }
  }

  fn get(&self, ident: &CoreIdent) -> Result<PartialValue, BindingError> {
    match ident.id() {
      None => Err(BindingError::new("Undefined local", ident.range())),
      Some(id) => match self.locals.get(&id) {
        None => Err(BindingError::new("Local not bound", ident.range())),
        Some(v) => Ok(v.clone()),
      },
    }
  }

  fn define(&mut self, id: NonZeroU32, value: PartialValue) {
    self.locals.insert(id, value);
  }
}

trait ToValue {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError>;
}

impl ToValue for LiteralCoreExpr {
  fn to_value(&self, _: &mut Binder) -> Result<PartialValue, BindingError> {
    Ok(
      match &self.token {
        LiteralToken::Null => Value::Null,
        LiteralToken::True => Value::Bool(true),
        LiteralToken::False => Value::Bool(false),
        LiteralToken::String(s) => Value::String(StringValue::from(s.as_ref())),
        LiteralToken::Number(s) => Value::Double(*s),
      }
      .into(),
    )
  }
}

impl ToValue for SelfCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    binder
      .self_value
      .clone()
      .ok_or_else(|| BindingError::new("Can't use self outside of an object.", self.range()))
  }
}

#[derive(Debug, Trace)]
struct SuperPartial(Location);

impl LateBound for SuperPartial {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    ctx.super_value.clone().ok_or_else(|| {
      EvalError::new(
        "Attempt to use super when there is no super class.",
        self.0.clone(),
      )
    })
  }

  fn into_partial(self) -> PartialValue {
    LateBoundValue::new(self).into()
  }
}

impl ToValue for SuperCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    if binder.self_value.is_none() {
      return Err(BindingError::new(
        "Can't use super outside of an object.",
        self.range(),
      ));
    }

    Ok(SuperPartial(self.range().into()).into_partial())
  }
}

#[derive(Debug, Trace)]
struct ObjectPartialExpr {
  asserts: Vec<PartialValue>,
  fields: Vec<ObjectPartialField>,
}

#[derive(Debug, Trace)]
struct ObjectPartialField {
  name: PartialValue,
  vis: ObjectFieldVisibility,
  value: PartialValue,
}

impl ObjectPartialField {
  fn is_bound(&self) -> bool {
    self.name.is_bound() && self.value.is_bound()
  }

  fn to_value(&self) -> Option<ObjectLazyField> {
    match (self.name.as_value(), self.value.as_value(), &self.vis) {
      (Some(name), Some(value), ObjectFieldVisibility::Hidden) => Some(ObjectLazyField {
        name,
        value,
        visible: LazyValue::from(false),
      }),
      (Some(name), Some(value), ObjectFieldVisibility::Visible) => Some(ObjectLazyField {
        name,
        value,
        visible: LazyValue::from(true),
      }),
      _ => None,
    }
  }
}

#[derive(Debug, Trace, Eq, PartialEq, Clone)]
enum ObjectFieldVisibility {
  Default,
  Visible,
  Hidden,
}

impl From<&CoreObjectFieldOperator> for ObjectFieldVisibility {
  fn from(op: &CoreObjectFieldOperator) -> Self {
    match op {
      CoreObjectFieldOperator::Default(_) => ObjectFieldVisibility::Default,
      CoreObjectFieldOperator::Hidden(_) => ObjectFieldVisibility::Hidden,
      CoreObjectFieldOperator::Visible(_) => ObjectFieldVisibility::Visible,
      CoreObjectFieldOperator::MergeDefault(_) => ObjectFieldVisibility::Default,
      CoreObjectFieldOperator::MergeHidden(_) => ObjectFieldVisibility::Hidden,
      CoreObjectFieldOperator::MergeVisible(_) => ObjectFieldVisibility::Visible,
    }
  }
}

impl Default for ObjectFieldVisibility {
  fn default() -> Self {
    Self::Default
  }
}

#[derive(Debug, Trace)]
struct ObjectLazyExpr {
  asserts: Gc<Vec<LazyValue>>,
  fields: Vec<ObjectLazyField>,
}

#[derive(Debug, Trace)]
struct ObjectLazyField {
  name: LazyValue,
  visible: LazyValue,
  value: LazyValue,
}

impl ObjectPartialField {
  fn eval(&self, ctx: EvalContext) -> Result<ObjectLazyField, EvalError> {
    let name = self.name.eval(ctx.clone())?;
    let value = self.value.eval(ctx.clone())?;
    let visible = match (&ctx.super_value, &self.vis) {
      (_, ObjectFieldVisibility::Hidden) => LazyValue::from(false),
      (_, ObjectFieldVisibility::Visible) => LazyValue::from(true),
      (None, ObjectFieldVisibility::Default) => LazyValue::from(true),
      (Some(s), ObjectFieldVisibility::Default) => LazyValue::new(LazyVisibilityExpr {
        super_object: s.clone(),
        field_name: name.clone(),
      }),
    };

    Ok(ObjectLazyField {
      name,
      value,
      visible,
    })
  }
}

#[derive(Trace, Debug)]
struct LazyVisibilityExpr {
  super_object: LazyValue,
  field_name: LazyValue,
}

impl Expression for LazyVisibilityExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    let super_value = self.super_object.force()?;
    let super_object = super_value
      .as_object()
      .ok_or_else(|| EvalError::new("Super must always be an object", None))?;

    let field_name_value = self.field_name.force()?;
    let field_name = field_name_value.as_string().ok_or_else(|| {
      EvalError::new(
        "Field name is not a string", /* TODO: better error */
        None,
      )
    })?;

    let visible = super_object
      .get(field_name)?
      .map(|f| f.visible)
      .unwrap_or(true);

    Ok(cell.update(Gc::new(Value::Bool(visible))))
  }
}

impl ObjectLazyField {
  fn to_object_property(&self) -> Result<ObjectProperty, EvalError> {
    Ok(ObjectProperty {
      name: self.name.clone(),
      value: self.value.clone(),
      visible: self.visible.force()?.as_bool().unwrap(),
    })
  }
}

impl LateBound for ObjectPartialExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let asserts = self
      .asserts
      .iter()
      .map(|a| a.eval(ctx.clone()))
      .collect::<Result<_, EvalError>>()?;
    let fields = self
      .fields
      .iter()
      .map(|f| f.eval(ctx.clone()))
      .collect::<Result<_, EvalError>>()?;

    let lazy = ObjectLazyExpr {
      asserts: Gc::new(asserts),
      fields,
    };

    Ok(LazyValue::new(lazy))
  }

  fn into_partial(mut self) -> PartialValue {
    if self.asserts.iter().all(|v| v.is_bound()) && self.fields.iter().all(|f| f.is_bound()) {
      let asserts = self
        .asserts
        .replace_with_default()
        .into_iter()
        .map(|a| a.as_value().unwrap())
        .collect();
      let fields = self
        .fields
        .replace_with_default()
        .into_iter()
        .map(|f| f.to_value().unwrap())
        .collect();

      LazyValue::new(ObjectLazyExpr {
        asserts: Gc::new(asserts),
        fields,
      })
      .into()
    } else {
      LateBoundValue::new(self).into()
    }
  }
}

impl Expression for ObjectLazyExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    for assert in self.asserts.iter() {
      todo!("eval asserts")
    }

    // let asserts = self.asserts.iter().map(|v| v.eval()).collect()?;
    // let fields = self.fields.iter().map(|f| f.eval()).collect()?;
    let properties = self
      .fields
      .iter()
      .map(|f| f.to_object_property())
      .collect::<Result<_, EvalError>>()?;
    let object = Object {
      properties: Gc::new(properties),
    };

    Ok(Gc::new(Value::Object(object)))
  }
}

impl ToValue for ObjectCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    fn field_value(
      field: &CoreExpr,
      op: &CoreObjectFieldOperator,
    ) -> Result<PartialValue, BindingError> {
      todo!()
    }

    let self_value = UnsetValue.into_partial();
    let old_self = binder.self_value.replace(self_value.clone());
    let asserts = self
      .asserts()
      .iter()
      .map(|a| a.to_value(binder))
      .collect::<Result<_, BindingError>>()?;
    let fields = self
      .fields()
      .iter()
      .map(|f| {
        Ok(ObjectPartialField {
          name: f.name().to_value(binder)?,
          vis: ObjectFieldVisibility::from(f.op()),
          value: field_value(f.value(), f.op())?,
        })
      })
      .collect::<Result<_, BindingError>>()?;

    binder.self_value = old_self;
    let partial = ObjectPartialExpr { asserts, fields };

    Ok(self_value.assign(partial))
  }
}

#[derive(Trace, Debug)]
struct PartialArrayExpr {
  values: Vec<PartialValue>,
}

#[derive(Trace, Debug)]
struct LazyArrayExpr {
  values: Gc<Vec<LazyValue>>,
}

impl LateBound for PartialArrayExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let item_ctx = ctx.clone();
    let values = self
      .values
      .iter()
      .map(|v| v.eval(item_ctx.clone()))
      .collect::<Result<_, EvalError>>()?;

    Ok(LazyValue::new(LazyArrayExpr {
      values: Gc::new(values),
    }))
  }

  fn into_partial(self) -> PartialValue {
    let values = self.values.iter().map(|v| v.as_value()).collect();
    match values {
      Some(values) => LazyValue::new(LazyArrayExpr {
        values: Gc::new(values),
      })
      .into(),
      None => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyArrayExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    Ok(
      cell.update(Gc::new(
        Array {
          items: self.values.clone(),
        }
        .into(),
      )),
    )
  }
}

impl ToValue for ArrayCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let values = self
      .items()
      .iter()
      .map(|i| i.to_value(binder))
      .collect::<Result<_, BindingError>>()?;

    Ok(PartialArrayExpr { values }.into_partial())
  }
}

#[derive(Trace, Debug)]
struct PartialMemberAccess {
  target: PartialValue,
  field: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyMemberAccess {
  target: LazyValue,
  field: LazyValue,
}

impl LateBound for PartialMemberAccess {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    Ok(LazyValue::new(LazyMemberAccess {
      target: self.target.eval(ctx.clone())?,
      field: self.field.eval(ctx.clone())?,
    }))
  }

  fn into_partial(self) -> PartialValue {
    match (self.target.as_value(), self.field.as_value()) {
      (Some(target), Some(field)) => LazyValue::new(LazyMemberAccess { target, field }).into(),
      _ => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyMemberAccess {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    todo!()
  }
}

impl ToValue for MemberAccessCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let target = self.target().to_value(binder)?;
    let field = self.field_name().to_value(binder)?;

    Ok(PartialMemberAccess { target, field }.into_partial())
  }
}

impl ToValue for IdentCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    binder.get(self.ident())
  }
}

impl ToValue for LocalCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    for bind in self.binds() {
      let ident = bind.ident();
      match ident.id() {
        None => return Err(BindingError::new("Unbound local", bind.range())),
        Some(id) => {
          let value = bind.value().to_value(binder)?;
          binder.define(id, value);
        }
      }
    }

    self.rest().to_value(binder)
  }
}

#[derive(Trace, Debug)]
struct PartialIfExpr {
  cond: PartialValue,
  if_true: PartialValue,
  if_false: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyIfExpr {
  cond: LazyValue,
  if_true: LazyValue,
  if_false: LazyValue,
}

impl LateBound for PartialIfExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let cond = self.cond.eval(ctx.clone())?;
    let if_true = self.if_true.eval(ctx.clone())?;
    let if_false = self.if_false.eval(ctx.clone())?;

    Ok(LazyValue::new(LazyIfExpr {
      cond,
      if_true,
      if_false,
    }))
  }

  fn into_partial(self) -> PartialValue {
    match (
      self.cond.as_value(),
      self.if_true.as_value(),
      self.if_false.as_value(),
    ) {
      (Some(cond), Some(if_true), Some(if_false)) => LazyValue::new(LazyIfExpr {
        cond,
        if_true,
        if_false,
      })
      .into(),
      _ => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyIfExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    let cond_val = self.cond.force()?;
    if cond_val.is_truthy() {
      Ok(cell.update(self.if_true.force()?))
    } else {
      Ok(cell.update(self.if_false.force()?))
    }
  }
}

impl ToValue for IfCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let cond = self.cond().to_value(binder)?;
    let if_true = self.if_true().to_value(binder)?;
    let if_false = self.if_false().to_value(binder)?;

    Ok(
      PartialIfExpr {
        cond,
        if_true,
        if_false,
      }
      .into_partial(),
    )
  }
}

#[derive(Trace, Debug)]
struct PartialBinaryExpr {
  op: BinaryOp,
  lhs: PartialValue,
  rhs: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyBinaryExpr {
  op: BinaryOp,
  lhs: LazyValue,
  rhs: LazyValue,
}

#[derive(Trace, Debug, Eq, PartialEq, Clone)]
pub enum BinaryOp {
  Mult,
  Div,
  Plus,
  Minus,
  ShiftL,
  ShiftR,
  GreaterThan,
  GreaterThanOrEquals,
  LessThan,
  LessThanOrEquals,
  BitAnd,
  BitXor,
  BitOr,
  And,
  Or,
}

impl From<&CoreBinaryOperator> for BinaryOp {
  fn from(op: &CoreBinaryOperator) -> Self {
    match op {
      CoreBinaryOperator::Mult(_) => BinaryOp::Mult,
      CoreBinaryOperator::Div(_) => BinaryOp::Div,
      CoreBinaryOperator::Plus(_) => BinaryOp::Plus,
      CoreBinaryOperator::Minus(_) => BinaryOp::Minus,
      CoreBinaryOperator::ShiftL(_) => BinaryOp::ShiftL,
      CoreBinaryOperator::ShiftR(_) => BinaryOp::ShiftR,
      CoreBinaryOperator::GreaterThan(_) => BinaryOp::GreaterThan,
      CoreBinaryOperator::GreaterThanOrEquals(_) => BinaryOp::GreaterThanOrEquals,
      CoreBinaryOperator::LessThan(_) => BinaryOp::LessThan,
      CoreBinaryOperator::LessThanOrEquals(_) => BinaryOp::LessThanOrEquals,
      CoreBinaryOperator::BitAnd(_) => BinaryOp::BitAnd,
      CoreBinaryOperator::BitXor(_) => BinaryOp::BitXor,
      CoreBinaryOperator::BitOr(_) => BinaryOp::BitOr,
      CoreBinaryOperator::And(_) => BinaryOp::And,
      CoreBinaryOperator::Or(_) => BinaryOp::Or,
    }
  }
}

impl LateBound for PartialBinaryExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let lhs = self.lhs.eval(ctx.clone())?;
    let rhs = match self.op {
      // + is overloaded to also mean "inheritance" in jsonnet
      BinaryOp::Plus => self.rhs.eval(ctx.with_super(lhs.clone()))?,
      _ => self.rhs.eval(ctx)?,
    };

    Ok(LazyValue::new(LazyBinaryExpr {
      lhs,
      rhs,
      op: self.op.clone(),
    }))
  }

  fn into_partial(self) -> PartialValue {
    if self.op != BinaryOp::Plus {
      match (self.lhs.as_value(), self.rhs.as_value()) {
        (Some(lhs), Some(rhs)) => {
          return LazyValue::new(LazyBinaryExpr {
            lhs,
            rhs,
            op: self.op.clone(),
          })
          .into()
        }
        _ => (),
      }
    }

    LateBoundValue::new(self).into()
  }
}

impl Expression for LazyBinaryExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    let lhs = self.lhs.force()?;
    let rhs = self.rhs.force()?;

    match &self.op {
      BinaryOp::Mult => {
        ensure_types_match(lhs, rhs, "binary operator *")?;
        let lhs = lhs.ensure_double()?;
        let rhs = rhs.ensure_double()?;
        let result = lhs * rhs;
        Ok(cell.update(Gc::new(Value::Double(result))))
      }
      BinaryOp::Div => todo!(),
      BinaryOp::Plus => todo!(),
      BinaryOp::Minus => todo!(),
      BinaryOp::ShiftL => todo!(),
      BinaryOp::ShiftR => todo!(),
      BinaryOp::GreaterThan => todo!(),
      BinaryOp::GreaterThanOrEquals => todo!(),
      BinaryOp::LessThan => todo!(),
      BinaryOp::LessThanOrEquals => todo!(),
      BinaryOp::BitAnd => todo!(),
      BinaryOp::BitXor => todo!(),
      BinaryOp::BitOr => todo!(),
      BinaryOp::And => todo!(),
      BinaryOp::Or => todo!(),
    }
  }
}

impl ToValue for BinaryCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let op = BinaryOp::from(self.op());
    let lhs = self.lhs().to_value(binder)?;
    let rhs = self.rhs().to_value(binder)?;

    Ok(PartialBinaryExpr { op, lhs, rhs }.into_partial())
  }
}

#[derive(Trace, Debug)]
struct PartialUnaryExpr {
  op: UnaryOp,
  val: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyUnaryExpr {
  op: UnaryOp,
  val: LazyValue,
}

#[derive(Trace, Debug, Eq, PartialEq, Clone)]
pub enum UnaryOp {
  Plus,
  Minus,
  Not,
  BitNeg,
}

impl From<&CoreUnaryOperator> for UnaryOp {
  fn from(op: &CoreUnaryOperator) -> Self {
    match op {
      CoreUnaryOperator::Plus(_) => UnaryOp::Plus,
      CoreUnaryOperator::Minus(_) => UnaryOp::Minus,
      CoreUnaryOperator::Not(_) => UnaryOp::Not,
      CoreUnaryOperator::BitNeg(_) => UnaryOp::BitNeg,
    }
  }
}

impl LateBound for PartialUnaryExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let val = self.val.eval(ctx.clone())?;

    Ok(LazyValue::new(LazyUnaryExpr {
      val,
      op: self.op.clone(),
    }))
  }

  fn into_partial(self) -> PartialValue {
    match self.val.as_value() {
      Some(val) => LazyValue::new(LazyUnaryExpr {
        val,
        op: self.op.clone(),
      })
      .into(),
      _ => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyUnaryExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    todo!()
  }
}

impl ToValue for UnaryCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let op = UnaryOp::from(self.op());
    let val = self.expr().to_value(binder)?;

    Ok(PartialUnaryExpr { op, val }.into_partial())
  }
}

#[derive(Trace, Debug)]
struct PartialFunctionExpr {
  params: Vec<PartialFunctionParam>,
  body: PartialValue,
}

#[derive(Trace, Debug)]
struct PartialFunctionParam {
  name: StringValue,
  id: NonZeroU32,
  default_value: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyFunctionExpr {
  params: Vec<LazyFunctionParam>,
  body: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyFunctionParam {
  name: StringValue,
  id: NonZeroU32,
  default_value: LazyValue,
}

#[derive(Trace, Debug)]
struct FunctionArgument(NonZeroU32);

impl LateBound for FunctionArgument {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    ctx.get_arg(&self.0)
  }

  fn into_partial(self) -> PartialValue {
    LateBoundValue::new(self).into()
  }
}

impl PartialFunctionParam {
  fn as_value(&self) -> Option<LazyFunctionParam> {
    match self.default_value.as_value() {
      Some(default_value) => Some(LazyFunctionParam {
        name: self.name.clone(),
        id: self.id,
        default_value,
      }),
      None => None,
    }
  }

  fn eval(&self, ctx: EvalContext) -> Result<LazyFunctionParam, EvalError> {
    let default_value = self.default_value.eval(ctx)?;

    Ok(LazyFunctionParam {
      name: self.name.clone(),
      id: self.id,
      default_value,
    })
  }

  fn bind(
    core: &CoreFunctionParam,
    binder: &mut Binder,
  ) -> Result<PartialFunctionParam, BindingError> {
    let default_value = core.default_value().to_value(binder)?;
    let name = core.name();

    match name.id() {
      None => Err(BindingError::new(
        "Function param has no name",
        core.range(),
      )),
      Some(id) => {
        let name = name.name();
        binder.define(id, LateBoundValue::new(FunctionArgument(id)).into());
        Ok(PartialFunctionParam {
          name: name.into(),
          id,
          default_value,
        })
      }
    }
  }
}

impl LateBound for PartialFunctionExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let params = self
      .params
      .iter()
      .map(|p| p.eval(ctx.clone()))
      .collect::<Result<_, EvalError>>()?;

    Ok(LazyValue::new(LazyFunctionExpr {
      params,
      body: self.body.clone(),
    }))
  }

  fn into_partial(self) -> PartialValue {
    match self.params.iter().map(|p| p.as_value()).collect() {
      Some(params) => LazyValue::new(LazyFunctionExpr {
        params,
        body: self.body.clone(),
      })
      .into(),
      None => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyFunctionExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    todo!()
  }
}

impl ToValue for FunctionCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let params = self
      .params()
      .iter()
      .map(|p| PartialFunctionParam::bind(p, binder))
      .collect::<Result<_, BindingError>>()?;
    let body = self.expr().to_value(binder)?;

    Ok(PartialFunctionExpr { params, body }.into_partial())
  }
}

#[derive(Trace, Debug)]
struct PartialApplyExpr {
  target: PartialValue,
  positionals: Vec<PartialValue>,
  named: Vec<(StringValue, PartialValue)>,
}

#[derive(Trace, Debug)]
struct LazyApplyExpr {
  target: LazyValue,
  positionals: Vec<LazyValue>,
  named: Vec<(StringValue, LazyValue)>,
}

#[derive(Trace, Debug)]
struct PartialTailStrictApplyExpr(PartialApplyExpr);

#[derive(Trace, Debug)]
struct LazyTailStrictApplyExpr(LazyApplyExpr);

impl PartialApplyExpr {
  fn as_lazy(&self) -> Option<LazyApplyExpr> {
    let target = self.target.as_value();
    let positionals = self.positionals.iter().map(|p| p.as_value()).collect();
    let named = self
      .named
      .iter()
      .map(|(n, p)| p.as_value().map(|v| (n.clone(), v)))
      .collect();

    match (target, positionals, named) {
      (Some(target), Some(positionals), Some(named)) => Some(LazyApplyExpr {
        target,
        positionals,
        named,
      }),
      _ => None,
    }
  }

  fn eval_lazy(&self, ctx: EvalContext) -> Result<LazyApplyExpr, EvalError> {
    let target = self.target.eval(ctx.clone())?;
    let positionals = self
      .positionals
      .iter()
      .map(|p| p.eval(ctx.clone()))
      .collect::<Result<_, EvalError>>()?;
    let named = self
      .named
      .iter()
      .map(|(n, p)| p.eval(ctx.clone()).map(|v| (n.clone(), v)))
      .collect::<Result<_, EvalError>>()?;

    Ok(LazyApplyExpr {
      target,
      positionals,
      named,
    })
  }
}

impl LateBound for PartialApplyExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    Ok(LazyValue::new(self.eval_lazy(ctx)?))
  }

  fn into_partial(self) -> PartialValue {
    match self.as_lazy() {
      Some(lazy) => LazyValue::new(lazy).into(),
      _ => LateBoundValue::new(self).into(),
    }
  }
}

impl LateBound for PartialTailStrictApplyExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    Ok(LazyValue::new(LazyTailStrictApplyExpr(
      self.0.eval_lazy(ctx)?,
    )))
  }

  fn into_partial(self) -> PartialValue {
    match self.0.as_lazy() {
      Some(lazy) => LazyValue::new(LazyTailStrictApplyExpr(lazy)).into(),
      _ => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyApplyExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    todo!()
  }
}

impl Expression for LazyTailStrictApplyExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    todo!()
  }
}

impl ToValue for ApplyCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let target = self.target().to_value(binder)?;
    let positionals = self
      .positionals()
      .iter()
      .map(|p| p.to_value(binder))
      .collect::<Result<_, BindingError>>()?;
    let named = self
      .named()
      .iter()
      .map(|p| {
        p.value()
          .to_value(binder)
          .map(|v| (StringValue::from(p.name()), v))
      })
      .collect::<Result<_, BindingError>>()?;
    let expr = PartialApplyExpr {
      target,
      positionals,
      named,
    };

    if self.is_tailstrict() {
      Ok(PartialTailStrictApplyExpr(expr).into_partial())
    } else {
      Ok(expr.into_partial())
    }
  }
}

#[derive(Trace, Debug)]
struct PartialErrorExpr {
  value: PartialValue,
}

#[derive(Trace, Debug)]
struct LazyErrorExpr {
  value: LazyValue,
}

impl LateBound for PartialErrorExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let value = self.value.eval(ctx)?;

    Ok(LazyValue::new(LazyErrorExpr { value }))
  }

  fn into_partial(self) -> PartialValue {
    match self.value.as_value() {
      Some(value) => LazyValue::new(LazyErrorExpr { value }).into(),
      None => LateBoundValue::new(self).into(),
    }
  }
}

impl Expression for LazyErrorExpr {
  fn eval(&self, cell: &LazyValue) -> Result<Gc<Value>, EvalError> {
    let value = self.value.force()?;
    todo!()
  }
}

impl ToValue for ErrorCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    let value = self.expr().to_value(binder)?;

    Ok(PartialErrorExpr { value }.into_partial())
  }
}

#[derive(Trace, Debug)]
struct PartialImportExpr {
  file: StringValue,
  kind: ImportKind,
}
#[derive(Trace, Debug, Clone)]
pub enum ImportKind {
  /// Import file as jsonnet file (and evaluate it)
  Jsonnet,

  /// Import file as string (same as a string literal)
  String,
}

impl From<&CoreImportKind> for ImportKind {
  fn from(v: &CoreImportKind) -> Self {
    match v {
      CoreImportKind::Jsonnet => ImportKind::Jsonnet,
      CoreImportKind::String => ImportKind::String,
    }
  }
}

impl LateBound for PartialImportExpr {
  fn eval(&self, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let file = ctx
      .engine
      .import(self.file.as_ref().as_ref(), &ctx.source)?;

    match &self.kind {
      ImportKind::String => Ok(Value::String(StringValue::from(file.content.as_ref())).into()),
      ImportKind::Jsonnet => ctx.engine.eval_file(file, ctx.clone()),
    }
  }

  #[inline]
  fn into_partial(self) -> PartialValue {
    LateBoundValue::new(self).into()
  }
}

impl ToValue for ImportCoreExpr {
  fn to_value(&self, _: &mut Binder) -> Result<PartialValue, BindingError> {
    let file = StringValue::from(self.file());
    let kind = ImportKind::from(self.kind());
    Ok(LateBoundValue::new(PartialImportExpr { file, kind }).into())
  }
}

impl ToValue for ObjectCompCoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    todo!()
  }
}

impl ToValue for CoreExpr {
  fn to_value(&self, binder: &mut Binder) -> Result<PartialValue, BindingError> {
    match self {
      CoreExpr::Literal(e) => e.to_value(binder),
      CoreExpr::SelfValue(e) => e.to_value(binder),
      CoreExpr::Super(e) => e.to_value(binder),
      CoreExpr::Object(e) => e.to_value(binder),
      CoreExpr::ObjectComp(e) => e.to_value(binder),
      CoreExpr::Array(e) => e.to_value(binder),
      CoreExpr::MemberAccess(e) => e.to_value(binder),
      CoreExpr::Ident(e) => e.to_value(binder),
      CoreExpr::Local(e) => e.to_value(binder),
      CoreExpr::If(e) => e.to_value(binder),
      CoreExpr::Binary(e) => e.to_value(binder),
      CoreExpr::Unary(e) => e.to_value(binder),
      CoreExpr::Function(e) => e.to_value(binder),
      CoreExpr::Apply(e) => e.to_value(binder),
      CoreExpr::Error(e) => e.to_value(binder),
      CoreExpr::Import(e) => e.to_value(binder),
    }
  }
}

pub(crate) fn bind_expr(expr: &CoreExpr) -> Result<PartialValue, BindingError> {
  let mut binder = Binder::new();
  expr.to_value(&mut binder)
}
