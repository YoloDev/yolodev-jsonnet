use crate::{
  ast::core as core_ast,
  core::*,
  parse::error::{Error, Result},
  utils::intern::StringId,
};
use core::num::NonZeroU32;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(NonZeroU32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Binding(StringId, BindingId, Span);

impl Binding {
  #[inline]
  pub(crate) fn id(&self) -> BindingId {
    self.1
  }

  #[inline]
  pub(crate) fn name(&self) -> StringId {
    self.0
  }
}

struct Binder {
  next: u32,
  locals: Vec<Binding>,
  frames: Vec<usize>,
}

impl Binder {
  fn new() -> Self {
    Binder {
      next: 1,
      locals: Vec::new(),
      frames: Vec::new(),
    }
  }

  fn push_frame(&mut self) -> BinderFrame {
    let len = self.locals.len();
    self.frames.push(len);

    BinderFrame {
      binder: self,
      #[cfg(debug_assertions)]
      start: len,
    }
  }

  fn pop_frame(&mut self, #[cfg(debug_assertions)] frame_start: usize) {
    match self.frames.pop() {
      None => panic!("stack inbalance, frame pop called multiple times?"),
      Some(len) => {
        #[cfg(debug_assertions)]
        debug_assert_eq!(len, frame_start);

        self.locals.truncate(len);
      }
    }
  }

  fn define(&mut self, id: StringId, span: Span) -> Result<Binding> {
    // This should always be safe because we start at one, and if we
    // overflow, the addition itself should throw first.
    let binding = Binding(
      id,
      BindingId(unsafe { NonZeroU32::new_unchecked(self.next) }),
      span,
    );
    self.next += 1;

    if let Some(existing) = self
      .locals
      .iter()
      .rev()
      .enumerate()
      .find_map(|(idx, Binding(i, ..))| if *i == id { Some(idx) } else { None })
    {
      define_error! {
        /// duplicate binding
        pub struct DuplicateBinding;
      }

      let frame_start = *self.frames.last().unwrap();
      if frame_start <= existing {
        return Err(Error::new(DuplicateBinding::new(span)));
      }
    }

    // TODO: Validate that we don't have duplicates within the same frame.
    self.locals.push(binding);
    Ok(binding)
  }

  fn lookup(&self, id: StringId) -> Option<Binding> {
    self
      .locals
      .iter()
      .rev()
      .find(|Binding(i, ..)| *i == id)
      .cloned()
  }

  fn bind(&self, id: StringId, span: Span) -> Result<Binding> {
    define_error! {
      /// failed to bind local
      struct BindingError;
    }

    self
      .lookup(id)
      .ok_or_else(|| Error::new(BindingError::new(span)))
  }
}

struct BinderFrame<'a> {
  binder: &'a mut Binder,
  #[cfg(debug_assertions)]
  start: usize,
}

impl<'a> Drop for BinderFrame<'a> {
  fn drop(&mut self) {
    self.binder.pop_frame(
      #[cfg(debug_assertions)]
      self.start,
    )
  }
}

pub(crate) fn bind(
  ctx: &mut Context,
  core_ast: crate::ast::core::Core,
  allocator: &core_ast::Allocator,
) -> Result<Id<Core>> {
  let mut binder = Binder::new();
  binder
    .define(ctx.strings.intern("std"), Span::EMPTY)
    .unwrap();

  let mut frame = binder.push_frame();
  let result = core_ast.bind(&mut frame, ctx, allocator)?;
  drop(frame);
  debug_assert!(binder.frames.is_empty());
  debug_assert!(binder.locals.is_empty());

  Ok(result)
}

trait Bind {
  type Ret = Id<Core>;

  fn bind(
    &self,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret>;
}

trait BindInner {
  type Ret = Id<Core>;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret>;
}

impl Bind for core_ast::Core {
  type Ret = Id<Core>;

  fn bind(
    &self,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let span = self.span;

    let expr: Core = self.expr.get(&a.exprs).bind_inner(span, frame, ctx, a)?;
    todo!()
  }
}

impl BindInner for core_ast::CoreExpr {
  type Ret = Core;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    match self {
      core_ast::CoreExpr::Null => Ok(CoreNull { span }.into()),
      core_ast::CoreExpr::True => Ok(CoreTrue { span }.into()),
      core_ast::CoreExpr::False => Ok(CoreFalse { span }.into()),
      core_ast::CoreExpr::SelfValue => {
        let binding = frame.binder.bind(ctx.strings.intern("self"), span)?;
        Ok(CoreIdent { span, binding }.into())
      }
      core_ast::CoreExpr::Super => {
        let binding = frame.binder.bind(ctx.strings.intern("super"), span)?;
        Ok(CoreIdent { span, binding }.into())
      }
      core_ast::CoreExpr::String(value) => Ok(
        CoreString {
          span,
          value: *value,
        }
        .into(),
      ),
      core_ast::CoreExpr::Number(value) => Ok(
        CoreNumber {
          span,
          value: *value,
        }
        .into(),
      ),
      core_ast::CoreExpr::Object(obj) => obj.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::ObjectComp(obj_comp) => {
        obj_comp.bind_inner(span, frame, ctx, a).map(Core::from)
      }
      core_ast::CoreExpr::Array(arr) => {
        // TODO: Get rid of vec allocation here.
        let items = arr
          .get(&a.cores)
          .iter()
          .map(|c| c.expr.get(&a.exprs).bind_inner(c.span, frame, ctx, a))
          .collect::<Result<Vec<_>>>()?;
        let items = ctx.exprs.push_slice(items);
        Ok(CoreArray { span, items }.into())
      }
      core_ast::CoreExpr::MemberAccess(ma) => ma.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Ident(id) => {
        let binding = frame.binder.bind(*id, span)?;
        Ok(CoreIdent { span, binding }.into())
      }
      core_ast::CoreExpr::Local(l) => l.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::If(i) => i.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Binary(b) => b.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Unary(u) => u.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Function(f) => f.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Apply(e) => e.bind_inner(span, frame, ctx, a).map(Core::from),
      core_ast::CoreExpr::Error(e) => {
        let expr = e.bind(frame, ctx, a)?;
        Ok(CoreError { span, expr }.into())
      }
      core_ast::CoreExpr::Import(p) => Ok(CoreImport { span, path: *p }.into()),
      core_ast::CoreExpr::ImportStr(p) => Ok(CoreImportStr { span, path: *p }.into()),
    }
  }
}

impl BindInner for core_ast::CoreLocal {
  type Ret = CoreLocal;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let mut frame = frame.binder.push_frame();
    let binds = self.binds.get(&a.binds);
    let mut bindings = Vec::with_capacity(binds.len());
    for b in binds {
      let span = b.span;
      let binding = frame.binder.define(b.name, span)?;
      let value = b.value.get(&a.cores).bind(&mut frame, ctx, a)?;
      bindings.push(CoreBinding {
        span,
        binding,
        value,
      });
    }

    let expr = self.rest.get(&a.cores).bind(&mut frame, ctx, a)?;
    drop(frame);

    let bindings = ctx.bindings.push_slice(bindings);
    Ok(CoreLocal {
      span,
      bindings,
      expr,
    })
  }
}

impl BindInner for core_ast::CoreFunction {
  type Ret = CoreFunction;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let mut frame = frame.binder.push_frame();
    let params = self.params.get(&a.params);
    let mut bindings = Vec::with_capacity(params.len());

    // first pre-populate all the bindings
    for param in params {
      frame.binder.define(param.name, param.span)?;
    }

    // then we can evaluate the default values
    for param in params {
      let span = param.span;
      let binding = frame.binder.bind(param.name, span)?;
      let default_value = param.default_value.get(&a.cores).bind(&mut frame, ctx, a)?;
      bindings.push(CoreBinding {
        span,
        binding,
        value: default_value,
      });
    }

    let body = self.expr.get(&a.cores).bind(&mut frame, ctx, a)?;
    drop(frame);

    let params = ctx.bindings.push_slice(bindings);
    Ok(CoreFunction { span, params, body })
  }
}

impl BindInner for core_ast::CoreMemberAccess {
  type Ret = CoreMemberAccess;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let target = self.target.get(&a.cores).bind(frame, ctx, a)?;
    let member = self.field.get(&a.cores).bind(frame, ctx, a)?;

    Ok(CoreMemberAccess {
      span,
      target,
      member,
    })
  }
}

impl BindInner for core_ast::CoreIf {
  type Ret = CoreIf;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let cond = self.cond.get(&a.cores).bind(frame, ctx, a)?;
    let if_true = self.if_true.get(&a.cores).bind(frame, ctx, a)?;
    let if_false = self.if_false.get(&a.cores).bind(frame, ctx, a)?;

    Ok(CoreIf {
      span,
      cond,
      if_true,
      if_false,
    })
  }
}

impl BindInner for core_ast::CoreBinary {
  type Ret = CoreBinary;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let lhs = self.lhs.get(&a.cores).bind(frame, ctx, a)?;
    let rhs = self.rhs.get(&a.cores).bind(frame, ctx, a)?;
    let op = self.op;

    Ok(CoreBinary { span, lhs, rhs, op })
  }
}

impl BindInner for core_ast::CoreUnary {
  type Ret = CoreUnary;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let expr = self.expr.get(&a.cores).bind(frame, ctx, a)?;
    let op = self.op;

    Ok(CoreUnary { span, expr, op })
  }
}

impl BindInner for core_ast::CoreApply {
  type Ret = CoreApply;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let target = self.target.get(&a.cores).bind(frame, ctx, a)?;
    let positional = self
      .positionals
      .get(&a.cores)
      .iter()
      .map(|c| c.expr.get(&a.exprs).bind_inner(c.span, frame, ctx, a))
      .collect::<Result<Vec<_>>>()?;
    let named = self
      .named
      .get(&a.named_args)
      .iter()
      .map(|n| n.bind(frame, ctx, a))
      .collect::<Result<Vec<_>>>()?;

    let positional = ctx.exprs.push_slice(positional);
    let named = ctx.named_args.push_slice(named);

    Ok(CoreApply {
      span,
      target,
      positional,
      named,
    })
  }
}

impl Bind for core_ast::CoreApplyNamedArg {
  type Ret = CoreNamedArgument;

  fn bind(
    &self,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let span = self.span;
    let name = self.name;
    let value = self.value.get(&a.cores).bind(frame, ctx, a)?;

    Ok(CoreNamedArgument { span, name, value })
  }
}

impl Bind for core_ast::CoreObjectField {
  type Ret = CoreObjectField;

  fn bind(
    &self,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let span = self.span;
    let field = self.key.get(&a.cores).bind(frame, ctx, a)?;
    let kind = self.kind;
    let value = self.value.get(&a.cores).bind(frame, ctx, a)?;

    Ok(CoreObjectField {
      span,
      field,
      kind,
      value,
    })
  }
}

impl BindInner for core_ast::CoreObject {
  type Ret = CoreObject;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let asserts = self
      .asserts
      .get(&a.cores)
      .iter()
      .map(|c| c.expr.get(&a.exprs).bind_inner(c.span, frame, ctx, a))
      .collect::<Result<Vec<_>>>()?;
    let fields = self
      .fields
      .get(&a.fields)
      .iter()
      .map(|f| f.bind(frame, ctx, a))
      .collect::<Result<Vec<_>>>()?;

    let asserts = ctx.exprs.push_slice(asserts);
    let fields = ctx.fields.push_slice(fields);

    Ok(CoreObject {
      span,
      asserts,
      fields,
    })
  }
}

impl BindInner for core_ast::CoreObjectComp {
  type Ret = CoreObjectComp;

  fn bind_inner(
    &self,
    span: Span,
    frame: &mut BinderFrame,
    ctx: &mut Context,
    a: &core_ast::Allocator,
  ) -> Result<Self::Ret> {
    let list = self.list.get(&a.cores).bind(frame, ctx, a)?;
    let mut frame = frame.binder.push_frame();
    let binding = frame.binder.define(self.id, span)?;
    let field = self.field.get(&a.cores).bind(&mut frame, ctx, a)?;
    let value = self.value.get(&a.cores).bind(&mut frame, ctx, a)?;
    drop(frame);

    Ok(CoreObjectComp {
      span,
      binding,
      list,
      field,
      value,
    })
  }
}
