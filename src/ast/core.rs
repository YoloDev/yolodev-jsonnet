//! The core language.

use crate::{
  ast::{full::*, punctuated::Punctuated},
  lex::{
    span::Span,
    token::{Ident, Spanned},
  },
  utils::{
    arena::{Arena, Id, SliceId},
    intern::{StringId, StringInterner},
    print::{FormatterExt, IndentFormatter},
  },
};
use alloc::{collections::VecDeque, rc::Rc};
use core::{
  fmt,
  fmt::{Debug, Display, Write},
};
use derive_more::From;
use hashbrown::HashMap;

pub use crate::ast::full::{ObjectFieldOperatorKind, UnaryOperatorKind};

trait IntoCore: Sized {
  fn into_core(self, span: Span) -> Core;

  #[inline]
  fn into_core_empty_span(self) -> Core {
    self.into_core(Span::EMPTY)
  }
}

impl IntoCore for Id<CoreExpr> {
  #[inline]
  fn into_core(self, span: Span) -> Core {
    Core { expr: self, span }
  }
}

trait Alloc<T> {
  type Id: Clone + Copy + PartialEq + Eq;
  type SliceId: Clone + Copy + PartialEq + Eq;

  fn alloc(&mut self, item: impl Into<T>) -> Self::Id;
  fn alloc_slice<I, L>(&mut self, item: L) -> Self::SliceId
  where
    I: Into<T>,
    L: IntoIterator<Item = I>,
    <L as IntoIterator>::IntoIter: ExactSizeIterator;
  fn empty_slice(&self) -> Self::SliceId;
}

impl<T> Alloc<T> for Arena<T> {
  type Id = Id<T>;
  type SliceId = SliceId<T>;

  #[inline]
  fn alloc(&mut self, item: impl Into<T>) -> Self::Id {
    self.push(item.into())
  }

  fn alloc_slice<I, L>(&mut self, items: L) -> Self::SliceId
  where
    I: Into<T>,
    L: IntoIterator<Item = I>,
    <L as IntoIterator>::IntoIter: ExactSizeIterator,
  {
    self.push_slice(items.into_iter().map(<I as Into<T>>::into))
  }

  fn empty_slice(&self) -> Self::SliceId {
    <Arena<T>>::empty_slice(self)
  }
}

struct Allocator {
  cores: Arena<Core>,
  exprs: Arena<CoreExpr>,
  named_args: Arena<CoreApplyNamedArg>,
  binds: Arena<CoreLocalBind>,
  params: Arena<CoreFunctionParam>,
  fields: Arena<CoreObjectField>,
  strings: StringInterner,
  null_ref: Id<CoreExpr>,
  true_ref: Id<CoreExpr>,
  false_ref: Id<CoreExpr>,
  self_ref: Id<CoreExpr>,
  super_ref: Id<CoreExpr>,
  std_ref: Id<CoreExpr>,
  root_ref: Id<CoreExpr>,
  empty_arr_ref: Id<CoreExpr>,
  assertion_failed_ref: Id<CoreExpr>,
  param_not_bound_ref: Id<CoreExpr>,
  std_refs: HashMap<&'static str, Id<CoreExpr>>,
}

impl Allocator {
  fn new() -> Allocator {
    let mut strings = StringInterner::with_capacity(1024);
    let mut exprs = Arena::new();
    let mut cores = Arena::new();
    let mut binds = Arena::new();
    let mut params = Arena::new();
    let mut fields = Arena::new();
    let named_args = Arena::new();
    let null_ref = exprs.alloc(CoreExpr::Null);
    let true_ref = exprs.alloc(CoreExpr::True);
    let false_ref = exprs.alloc(CoreExpr::False);
    let self_ref = exprs.alloc(CoreExpr::SelfValue);
    let super_ref = exprs.alloc(CoreExpr::Super);
    let std_ref = exprs.alloc(CoreExpr::Ident(strings.intern("std")));
    let root_ref = exprs.alloc(CoreExpr::Ident(strings.intern("$")));
    let empty_arr_ref = exprs.alloc(CoreExpr::Array(cores.empty_slice()));
    let assertion_failed_ref = {
      let message = exprs
        .alloc(CoreExpr::String(strings.intern("Assertion failed")))
        .into_core_empty_span();
      exprs.alloc(CoreExpr::Error(message))
    };
    let param_not_bound_ref = {
      let message = exprs
        .alloc(CoreExpr::String(strings.intern("Parameter not bound")))
        .into_core_empty_span();
      exprs.alloc(CoreExpr::Error(message))
    };

    Allocator {
      exprs,
      cores,
      named_args,
      binds,
      params,
      fields,
      strings,
      null_ref,
      true_ref,
      false_ref,
      self_ref,
      super_ref,
      std_ref,
      root_ref,
      empty_arr_ref,
      assertion_failed_ref,
      param_not_bound_ref,
      std_refs: HashMap::new(),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperatorKind {
  /// *
  Mul,

  /// /
  Div,

  /// +
  Plus,

  /// -
  Minus,

  /// <<
  ShiftLeft,

  /// >>
  ShiftRight,

  /// >
  GreaterThan,

  /// >=
  GreaterThanOrEqual,

  /// <
  LessThan,

  /// <=
  LessThanOrEqual,

  /// &
  BitwiseAnd,

  /// ^
  BitwiseXor,

  /// |
  BitwiseOr,

  /// &&
  And,

  /// ||
  Or,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Core {
  expr: Id<CoreExpr>,
  span: Span,
}

impl Core {
  #[inline]
  fn with_span(self, span: Span) -> Self {
    Self { span, ..self }
  }
}

#[derive(Debug, Clone, From)]
pub(crate) enum CoreExpr {
  Null,
  True,
  False,
  SelfValue,
  Super,
  #[from(ignore)]
  String(StringId),
  #[from(ignore)]
  Number(f64),
  Object(CoreObject),
  ObjectComp(CoreObjectComp),
  Array(SliceId<Core>),
  MemberAccess(CoreMemberAccess),
  #[from(ignore)]
  Ident(StringId),
  Local(CoreLocal),
  If(CoreIf),
  Binary(CoreBinary),
  Unary(CoreUnary),
  Function(CoreFunction),
  Apply(CoreApply),
  #[from(ignore)]
  Error(Core),
  #[from(ignore)]
  Import(StringId),
  #[from(ignore)]
  ImportStr(StringId),
}

#[derive(Debug, Clone)]
pub(crate) struct CoreObjectField {
  pub key: Id<Core>,
  pub kind: ObjectFieldOperatorKind,
  pub value: Id<Core>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreObject {
  pub asserts: SliceId<Core>,
  pub fields: SliceId<CoreObjectField>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreObjectComp {
  pub field: Id<Core>,
  pub value: Id<Core>,
  pub id: StringId,
  pub list: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreMemberAccess {
  pub target: Id<Core>,
  pub field: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreLocalBind {
  pub name: StringId,
  pub value: Id<Core>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreLocal {
  pub binds: SliceId<CoreLocalBind>,
  pub rest: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreIf {
  pub cond: Id<Core>,
  pub if_true: Id<Core>,
  pub if_false: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreBinary {
  pub lhs: Id<Core>,
  pub op: BinaryOperatorKind,
  pub rhs: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreUnary {
  pub op: UnaryOperatorKind,
  pub expr: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreFunctionParam {
  pub name: StringId,
  pub default_value: Id<Core>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreFunction {
  pub params: SliceId<CoreFunctionParam>,
  pub expr: Id<Core>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreApply {
  pub target: Id<Core>,
  pub positionals: SliceId<Core>,
  pub named: SliceId<CoreApplyNamedArg>,
}

#[derive(Debug, Clone)]
pub(crate) struct CoreApplyNamedArg {
  pub name: StringId,
  pub value: Id<Core>,
}

trait ObjectState: Clone + Copy + PartialEq + Eq {
  const IN_OBJECT: bool;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InObject;

impl ObjectState for InObject {
  const IN_OBJECT: bool = true;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NotInObject;

impl ObjectState for NotInObject {
  const IN_OBJECT: bool = false;
}

trait DesugarExpr {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core;
}

trait DesugarAssert {
  fn desugar_assert(self, a: &mut Allocator, binds: SliceId<CoreLocalBind>) -> Core;
}

trait DesugarField {
  fn desugar_field<T: ObjectState>(
    self,
    a: &mut Allocator,
    binds: SliceId<CoreLocalBind>,
    state: T,
  ) -> CoreObjectField;
}

trait DesugarBind {
  type Ret: Debug;

  fn desugar_bind<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret;
}

trait DesugarParam {
  type Ret: Debug;

  fn desugar_param<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret;
}

fn call_std_func<I>(a: &mut Allocator, name: &'static str, args: I) -> Core
where
  I: IntoIterator<Item = Core>,
  <I as IntoIterator>::IntoIter: ExactSizeIterator,
{
  let arena = &mut a.exprs;
  let strings = &mut a.strings;
  let cores = &mut a.cores;
  let std_ref = cores.alloc(a.std_ref.into_core_empty_span());
  let target = a
    .std_refs
    .entry(name)
    .or_insert_with(|| {
      let field = arena
        .alloc(CoreExpr::String(strings.intern(name)))
        .into_core_empty_span();
      arena
        .alloc(CoreExpr::from(CoreMemberAccess {
          target: std_ref,
          field: cores.alloc(field),
        }))
        .into()
    })
    .into_core_empty_span();

  let args = a.cores.alloc_slice(args);

  a.exprs
    .alloc(CoreApply {
      target: a.cores.alloc(target),
      positionals: args,
      named: a.named_args.empty_slice(),
    })
    .into_core_empty_span()
}

fn desugar_arrcomp<T: ObjectState>(
  a: &mut Allocator,
  expr: Expr,
  mut specs: VecDeque<CompSpec>,
  state: T,
) -> Core {
  debug_assert!(!specs.is_empty());

  let next = specs.pop_front().unwrap();
  let rest = if specs.is_empty() { None } else { Some(specs) };
  match (next, rest) {
    (CompSpec::If(f), Some(specs)) => {
      let cond = f.expr.desugar_expr(a, state);
      let if_true = desugar_arrcomp(a, expr, specs, state);
      let if_false = a.empty_arr_ref.into_core_empty_span();

      a.exprs
        .alloc(CoreIf {
          cond: a.cores.alloc(cond),
          if_true: a.cores.alloc(if_true),
          if_false: a.cores.alloc(if_false),
        })
        .into_core(Span::EMPTY)
    }

    (CompSpec::If(f), None) => {
      let cond = f.expr.desugar_expr(a, state);
      let if_true = {
        let expr = expr.desugar_expr(a, state);
        a.exprs
          .alloc(CoreExpr::Array(a.cores.alloc_slice(Some(expr))))
          .into_core_empty_span()
      };
      let if_false = a.empty_arr_ref.into_core_empty_span();

      a.exprs
        .alloc(CoreIf {
          cond: a.cores.alloc(cond),
          if_true: a.cores.alloc(if_true),
          if_false: a.cores.alloc(if_false),
        })
        .into_core_empty_span()
    }

    (CompSpec::For(f), Some(specs)) => {
      let arr_id = a.strings.intern("arr");
      let i_id = a.strings.intern("i");

      let arr = a
        .exprs
        .alloc(CoreExpr::Ident(arr_id))
        .into_core_empty_span();
      let i = a.exprs.alloc(CoreExpr::Ident(i_id)).into_core_empty_span();

      let arr_bind = CoreLocalBind {
        name: arr_id,
        value: {
          let value = f.expr.desugar_expr(a, state);
          a.cores.alloc(value)
        },
        span: Span::EMPTY,
      };

      let inner = desugar_arrcomp(a, expr, specs, state);
      let inner = a
        .exprs
        .alloc(CoreExpr::Array(a.cores.alloc_slice(Some(inner))))
        .into_core_empty_span();
      let arr_i = a
        .exprs
        .alloc(CoreMemberAccess {
          target: a.cores.alloc(arr),
          field: a.cores.alloc(i),
        })
        .into_core_empty_span();
      let loop_bind = CoreLocalBind {
        name: a.strings.intern(f.id.as_ref()),
        value: a.cores.alloc(arr_i),
        span: Span::EMPTY,
      };
      let fn_body = a
        .exprs
        .alloc(CoreLocal {
          binds: a.binds.alloc_slice(Some(loop_bind)),
          rest: a.cores.alloc(inner),
        })
        .into_core_empty_span();
      let i_param = CoreFunctionParam {
        name: i_id,
        default_value: a.cores.alloc(a.param_not_bound_ref.into_core_empty_span()),
        span: Span::EMPTY,
      };
      let inner_fn = a
        .exprs
        .alloc(CoreFunction {
          params: a.params.alloc_slice(Some(i_param)),
          expr: a.cores.alloc(fn_body),
        })
        .into_core_empty_span();
      let len = call_std_func(a, "length", vec![arr]);
      let arr_right = call_std_func(a, "makeArray", vec![len, inner_fn]);
      let joined = call_std_func(
        a,
        "join",
        vec![a.empty_arr_ref.into_core_empty_span(), arr_right],
      );

      a.exprs
        .alloc(CoreLocal {
          binds: a.binds.alloc_slice(Some(arr_bind)),
          rest: a.cores.alloc(joined),
        })
        .into_core_empty_span()
    }

    (CompSpec::For(f), None) => {
      let arr_id = a.strings.intern("arr");
      let i_id = a.strings.intern("i");

      let arr = a
        .exprs
        .alloc(CoreExpr::Ident(arr_id))
        .into_core_empty_span();
      let i = a.exprs.alloc(CoreExpr::Ident(i_id)).into_core_empty_span();

      let arr_bind = CoreLocalBind {
        name: arr_id,
        value: {
          let value = f.expr.desugar_expr(a, state);
          a.cores.alloc(value)
        },
        span: Span::EMPTY,
      };

      let inner = expr.desugar_expr(a, state);
      let inner = a
        .exprs
        .alloc(CoreExpr::Array(a.cores.alloc_slice(Some(inner))))
        .into_core_empty_span();
      let arr_i = a
        .exprs
        .alloc(CoreMemberAccess {
          target: a.cores.alloc(arr),
          field: a.cores.alloc(i),
        })
        .into_core_empty_span();
      let loop_bind = CoreLocalBind {
        name: a.strings.intern(f.id.as_ref()),
        value: a.cores.alloc(arr_i),
        span: Span::EMPTY,
      };
      let fn_body = a
        .exprs
        .alloc(CoreLocal {
          binds: a.binds.alloc_slice(Some(loop_bind)),
          rest: a.cores.alloc(inner),
        })
        .into_core_empty_span();
      let i_param = CoreFunctionParam {
        name: i_id,
        default_value: a.cores.alloc(a.param_not_bound_ref.into_core_empty_span()),
        span: Span::EMPTY,
      };
      let inner_fn = a
        .exprs
        .alloc(CoreFunction {
          params: a.params.alloc_slice(Some(i_param)),
          expr: a.cores.alloc(fn_body),
        })
        .into_core_empty_span();
      let len = call_std_func(a, "length", vec![arr]);
      let arr_right = call_std_func(a, "makeArray", vec![len, inner_fn]);
      let joined = call_std_func(
        a,
        "join",
        vec![a.empty_arr_ref.into_core_empty_span(), arr_right],
      );

      a.exprs
        .alloc(CoreLocal {
          binds: a.binds.alloc_slice(Some(arr_bind)),
          rest: a.cores.alloc(joined),
        })
        .into_core_empty_span()
    }
  }
}

impl DesugarExpr for Expr {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    match self {
      Expr::Apply(e) => (*e).desugar_expr(a, state),
      Expr::Array(e) => (*e).desugar_expr(a, state),
      Expr::ArrayComp(e) => (*e).desugar_expr(a, state),
      Expr::Assert(e) => (*e).desugar_expr(a, state),
      Expr::Binary(e) => (*e).desugar_expr(a, state),
      Expr::ComputedFieldAccess(e) => (*e).desugar_expr(a, state),
      Expr::Error(e) => (*e).desugar_expr(a, state),
      Expr::False(e) => (*e).desugar_expr(a, state),
      Expr::FieldAccess(e) => (*e).desugar_expr(a, state),
      Expr::Function(e) => (*e).desugar_expr(a, state),
      Expr::Group(e) => (*e).desugar_expr(a, state),
      Expr::Ident(e) => (*e).desugar_expr(a, state),
      Expr::If(e) => (*e).desugar_expr(a, state),
      Expr::Import(e) => (*e).desugar_expr(a, state),
      Expr::ImportStr(e) => (*e).desugar_expr(a, state),
      Expr::InSuper(e) => (*e).desugar_expr(a, state),
      Expr::Local(e) => (*e).desugar_expr(a, state),
      Expr::Null(e) => (*e).desugar_expr(a, state),
      Expr::Number(e) => (*e).desugar_expr(a, state),
      Expr::Object(e) => (*e).desugar_expr(a, state),
      Expr::ObjectApply(e) => (*e).desugar_expr(a, state),
      Expr::ObjectComp(e) => (*e).desugar_expr(a, state),
      Expr::Root(e) => (*e).desugar_expr(a, state),
      Expr::SelfValue(e) => (*e).desugar_expr(a, state),
      Expr::Slice(e) => (*e).desugar_expr(a, state),
      Expr::String(e) => (*e).desugar_expr(a, state),
      Expr::Super(e) => (*e).desugar_expr(a, state),
      Expr::True(e) => (*e).desugar_expr(a, state),
      Expr::Unary(e) => (*e).desugar_expr(a, state),
    }
  }
}

impl DesugarExpr for ExprObject {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let mut locals = Vec::new();
    let mut asserts = Vec::new();
    let mut values = Vec::new();
    let mut functions = Vec::new();

    for field in self.fields {
      match field {
        ObjectField::Assert(f) => asserts.push(*f),
        ObjectField::Function(f) => functions.push(*f),
        ObjectField::Local(f) => locals.push(*f),
        ObjectField::Value(f) => values.push(*f),
      }
    }

    let mut binds: Vec<_> = locals
      .into_iter()
      .map(|local| local.desugar_bind(a, state))
      .collect();
    if !T::IN_OBJECT {
      binds.push(CoreLocalBind {
        name: a.strings.intern("$"),
        value: a.cores.alloc(a.self_ref.into_core_empty_span()),
        span: Span::EMPTY,
      });
    }

    let binds = a.binds.alloc_slice(binds);

    let asserts: Vec<_> = asserts
      .into_iter()
      .map(|assert| assert.desugar_assert(a, binds))
      .collect();

    let mut fields = Vec::with_capacity(values.len() + functions.len());
    fields.extend(values.into_iter().map(|f| f.desugar_field(a, binds, state)));
    fields.extend(
      functions
        .into_iter()
        .map(|f| f.desugar_field(a, binds, state)),
    );

    a.exprs
      .alloc(CoreObject {
        asserts: a.cores.alloc_slice(asserts),
        fields: a.fields.alloc_slice(fields),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprObjectComp {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let arr_id = a.strings.intern("arr");
    let arr = Ident::from(Rc::from("arr")); // TODO: Really want to get rid of this...
    let mut xs = Vec::with_capacity(self.tail_spec.len() + 1);

    xs.push(self.for_spec.id.clone());
    for comp in &self.tail_spec {
      match comp {
        CompSpec::For(f) => xs.push(f.id.clone()),
        CompSpec::If(_) => (),
      }
    }

    let comp_field = self.field;

    let field = {
      let binds = xs
        .iter()
        .enumerate()
        .map(|(index, name)| {
          Bind::Value(
            BindValue {
              name: name.clone(),
              assign_token: Default::default(),
              body: ExprComputedFieldAccess {
                target: ExprIdent { name: arr.clone() }.into(),
                left_bracket_token: Default::default(),
                expr: ExprNumber {
                  value: (index as f64).into(),
                }
                .into(),
                right_bracket_token: Default::default(),
              }
              .into(),
            }
            .into(),
          )
        })
        .collect();

      let local = ExprLocal {
        local_token: Default::default(),
        binds,
        semi_colon_token: Default::default(),
        body: comp_field.field,
      };

      local.desugar_expr(a, state)
    };

    let value = {
      let binds = xs
        .iter()
        .enumerate()
        .map(|(index, name)| {
          Bind::Value(
            BindValue {
              name: name.clone().into(),
              assign_token: Default::default(),
              body: ExprComputedFieldAccess {
                target: ExprIdent { name: arr.clone() }.into(),
                left_bracket_token: Default::default(),
                expr: ExprNumber {
                  value: (index as f64).into(),
                }
                .into(),
                right_bracket_token: Default::default(),
              }
              .into(),
            }
            .into(),
          )
        })
        .collect();

      let mut inner_binds = Punctuated::with_capacity(
        self.before_field_locals.len()
          + self
            .after_field_locals
            .as_ref()
            .map(|(_, b)| b.len())
            .unwrap_or(0),
      );
      inner_binds.extend(self.before_field_locals.into_iter().map(|(f, _)| f.bind));
      if let Some((_, b)) = self.after_field_locals {
        inner_binds.extend(b.into_iter().map(|b| b.bind));
      }

      let local = ExprLocal {
        local_token: Default::default(),
        binds,
        semi_colon_token: Default::default(),
        body: ExprLocal {
          local_token: Default::default(),
          binds: inner_binds,
          semi_colon_token: Default::default(),
          body: comp_field.value,
        }
        .into(),
      };

      local.desugar_expr(a, InObject)
    };

    let list = {
      let comp = ExprArrayComp {
        left_bracket_token: Default::default(),
        expr: ExprArray {
          left_bracket_token: Default::default(),
          items: xs
            .into_iter()
            .map(|name| Expr::from(ExprIdent { name }))
            .collect(),
          right_bracket_token: Default::default(),
        }
        .into(),
        comma_token: None,
        for_spec: self.for_spec,
        tail_spec: self.tail_spec,
        right_bracket_token: Default::default(),
      };

      comp.desugar_expr(a, state)
    };

    a.exprs
      .alloc(CoreObjectComp {
        field: a.cores.alloc(field),
        value: a.cores.alloc(value),
        id: arr_id,
        list: a.cores.alloc(list),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprArrayComp {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let mut spec = VecDeque::with_capacity(self.tail_spec.len() + 1);
    spec.push_back(self.for_spec.into());
    spec.extend(self.tail_spec);

    desugar_arrcomp(a, self.expr, spec, state)
  }
}

impl DesugarExpr for ExprLocal {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let binds: Vec<_> = self
      .binds
      .into_iter()
      .map(|b| b.desugar_bind(a, state))
      .collect();

    let rest = self.body.desugar_expr(a, state);

    a.exprs
      .alloc(CoreLocal {
        binds: a.binds.alloc_slice(binds),
        rest: a.cores.alloc(rest),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprObjectApply {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    ExprBinary {
      lhs: self.target,
      op: BinaryOperator::Plus(Default::default()),
      rhs: self.object.into(),
    }
    .desugar_expr(a, state)
    .with_span(span)
  }
}

impl DesugarExpr for ExprFunction {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let params: Vec<_> = self
      .params
      .into_iter()
      .map(|p| p.desugar_param(a, state))
      .collect();

    let expr = self.body.desugar_expr(a, state);

    a.exprs
      .alloc(CoreFunction {
        params: a.params.alloc_slice(params),
        expr: a.cores.alloc(expr),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprAssert {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let cond = self.cond.desugar_expr(a, state);
    let if_true = self.rest.desugar_expr(a, state);
    let if_false = if let Some((_, msg)) = self.msg {
      let err = msg.desugar_expr(a, state);
      a.exprs.alloc(CoreExpr::Error(err)).into_core_empty_span()
    } else {
      a.assertion_failed_ref.into_core_empty_span()
    };

    a.exprs
      .alloc(CoreIf {
        cond: a.cores.alloc(cond),
        if_true: a.cores.alloc(if_true),
        if_false: a.cores.alloc(if_false),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprSlice {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let start = self
      .begin_index
      .map(|e| e.desugar_expr(a, state))
      .unwrap_or_else(|| a.null_ref.into_core_empty_span());
    let end = self
      .end_index
      .map(|e| e.desugar_expr(a, state))
      .unwrap_or_else(|| a.null_ref.into_core_empty_span());
    let step = self
      .step
      .map(|e| e.desugar_expr(a, state))
      .unwrap_or_else(|| a.null_ref.into_core_empty_span());

    call_std_func(a, "slice", vec![start, end, step])
  }
}

impl DesugarExpr for ExprIf {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let cond = self.cond.desugar_expr(a, state);
    let if_true = self.if_true.desugar_expr(a, state);
    let if_false = self
      .if_false
      .map(|(_, e)| e.desugar_expr(a, state))
      .unwrap_or_else(|| a.null_ref.into_core_empty_span());

    a.exprs
      .alloc(CoreIf {
        cond: a.cores.alloc(cond),
        if_true: a.cores.alloc(if_true),
        if_false: a.cores.alloc(if_false),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprFieldAccess {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let target = self.target.desugar_expr(a, state);
    let field_span = self.field_name.span();
    let field = {
      let str_id = a.strings.intern(self.field_name.as_ref());
      a.exprs
        .alloc(CoreExpr::String(str_id))
        .into_core(field_span)
    };

    a.exprs
      .alloc(CoreMemberAccess {
        target: a.cores.alloc(target),
        field: a.cores.alloc(field),
      })
      .into_core(span)
  }
}

impl DesugarExpr for SuperField {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let target = a.super_ref.into_core(self.super_token.span());
    let field_span = self.field_name.span();
    let field = {
      let str_id = a.strings.intern(self.field_name.as_ref());
      a.exprs
        .alloc(CoreExpr::String(str_id))
        .into_core(field_span)
    };

    a.exprs
      .alloc(CoreMemberAccess {
        target: a.cores.alloc(target),
        field: a.cores.alloc(field),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprBinary {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    match self.op {
      BinaryOperator::NotEqual(_) => {
        let expr = ExprBinary {
          lhs: self.lhs,
          op: BinaryOperator::Equal(Default::default()),
          rhs: self.rhs,
        }
        .desugar_expr(a, state);

        a.exprs
          .alloc(CoreUnary {
            op: UnaryOperatorKind::Not,
            expr: a.cores.alloc(expr),
          })
          .into_core(span)
      }

      BinaryOperator::Equal(_) => {
        let args = vec![
          self.lhs.desugar_expr(a, state),
          self.rhs.desugar_expr(a, state),
        ];

        call_std_func(a, "equals", args)
      }

      BinaryOperator::Mod(_) => {
        let args = vec![
          self.lhs.desugar_expr(a, state),
          self.rhs.desugar_expr(a, state),
        ];

        call_std_func(a, "mod", args)
      }

      BinaryOperator::In(_) => {
        let args = vec![
          self.rhs.desugar_expr(a, state),
          self.lhs.desugar_expr(a, state),
          a.true_ref.into_core_empty_span(),
        ];

        call_std_func(a, "objectHasEx", args)
      }

      _ => {
        let lhs = self.lhs.desugar_expr(a, state);
        let rhs = self.rhs.desugar_expr(a, state);

        a.exprs
          .alloc(CoreBinary {
            lhs: a.cores.alloc(lhs),
            rhs: a.cores.alloc(rhs),
            op: match self.op {
              BinaryOperator::Mul(_) => BinaryOperatorKind::Mul,
              BinaryOperator::Div(_) => BinaryOperatorKind::Div,
              BinaryOperator::Mod(_) => unreachable!(),
              BinaryOperator::Plus(_) => BinaryOperatorKind::Plus,
              BinaryOperator::Minus(_) => BinaryOperatorKind::Minus,
              BinaryOperator::ShiftLeft(_) => BinaryOperatorKind::ShiftLeft,
              BinaryOperator::ShiftRight(_) => BinaryOperatorKind::ShiftRight,
              BinaryOperator::GreaterThan(_) => BinaryOperatorKind::GreaterThan,
              BinaryOperator::GreaterThanOrEqual(_) => BinaryOperatorKind::GreaterThanOrEqual,
              BinaryOperator::LessThan(_) => BinaryOperatorKind::LessThan,
              BinaryOperator::LessThanOrEqual(_) => BinaryOperatorKind::LessThanOrEqual,
              BinaryOperator::In(_) => unreachable!(),
              BinaryOperator::Equal(_) => unreachable!(),
              BinaryOperator::NotEqual(_) => unreachable!(),
              BinaryOperator::BitwiseAnd(_) => BinaryOperatorKind::BitwiseAnd,
              BinaryOperator::BitwiseXor(_) => BinaryOperatorKind::BitwiseXor,
              BinaryOperator::BitwiseOr(_) => BinaryOperatorKind::BitwiseOr,
              BinaryOperator::And(_) => BinaryOperatorKind::And,
              BinaryOperator::Or(_) => BinaryOperatorKind::Or,
            },
          })
          .into_core(span)
      }
    }
  }
}

impl DesugarExpr for ExprInSuper {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let args = vec![
      a.super_ref.into_core_empty_span(),
      self.target.desugar_expr(a, state),
      a.true_ref.into_core_empty_span(),
    ];

    call_std_func(a, "objectHasEx", args)
  }
}

impl DesugarExpr for ExprApply {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let mut positionals = Vec::new();
    let mut named = Vec::new();

    // args should already be validated to be positional before named.
    let mut found_named = false;
    for arg in self.args {
      match arg {
        Argument::Positional(arg) => {
          assert!(!found_named, "positional afer named");
          positionals.push(arg.value.desugar_expr(a, state));
        }
        Argument::Named(arg) => {
          found_named = true;
          named.push(CoreApplyNamedArg {
            name: a.strings.intern(arg.name.as_ref()),
            value: {
              let value = arg.value.desugar_expr(a, state);
              a.cores.alloc(value)
            },
          });
        }
      }
    }

    let target = self.target.desugar_expr(a, state);

    a.exprs
      .alloc(CoreApply {
        target: a.cores.alloc(target),
        positionals: a.cores.alloc_slice(positionals),
        named: a.named_args.alloc_slice(named),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprArray {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let items: Vec<_> = self
      .items
      .into_iter()
      .map(|e| e.desugar_expr(a, state))
      .collect();

    a.exprs
      .alloc(CoreExpr::Array(a.cores.alloc_slice(items)))
      .into_core(span)
  }
}

impl DesugarExpr for ExprComputedFieldAccess {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let target = self.target.desugar_expr(a, state);
    let field = self.expr.desugar_expr(a, state);

    a.exprs
      .alloc(CoreMemberAccess {
        target: a.cores.alloc(target),
        field: a.cores.alloc(field),
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprError {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let msg = self.expr.desugar_expr(a, state);

    a.exprs.alloc(CoreExpr::Error(msg)).into_core(span)
  }
}

impl DesugarExpr for ExprFalse {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.false_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprGroup {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    self.expr.desugar_expr(a, state)
  }
}

impl DesugarExpr for ExprIdent {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = a.strings.intern(self.name.as_ref());
    a.exprs.alloc(CoreExpr::Ident(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprImportStr {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = a.strings.intern(self.file.value.as_ref());
    a.exprs.alloc(CoreExpr::ImportStr(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprImport {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = a.strings.intern(self.file.value.as_ref());
    a.exprs.alloc(CoreExpr::Import(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprNull {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.null_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprNumber {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    a.exprs
      .alloc(CoreExpr::Number(self.value.into()))
      .into_core(span)
  }
}

impl DesugarExpr for ExprRoot {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.root_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprSelf {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.self_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprString {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = a.strings.intern(self.value.as_ref());
    a.exprs.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprSuper {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.super_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprTrue {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    a.true_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprUnary {
  fn desugar_expr<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let expr = self.expr.desugar_expr(a, state);

    a.exprs
      .alloc(CoreUnary {
        op: self.op.kind(),
        expr: a.cores.alloc(expr),
      })
      .into_core(span)
  }
}

trait DesugarFieldName {
  fn desugar_field_name<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core;
}

impl DesugarFieldName for FieldNameIdent {
  fn desugar_field_name<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.name.span();

    let str_id = a.strings.intern(self.name.as_ref());
    a.exprs.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarFieldName for FieldNameString {
  fn desugar_field_name<T: ObjectState>(self, a: &mut Allocator, _: T) -> Core {
    let span = self.name.span();

    let str_id = a.strings.intern(self.name.as_ref());
    a.exprs.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarFieldName for FieldNameComputed {
  fn desugar_field_name<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    self.name.desugar_expr(a, state)
  }
}

impl DesugarFieldName for ObjectFieldName {
  fn desugar_field_name<T: ObjectState>(self, a: &mut Allocator, state: T) -> Core {
    match self {
      ObjectFieldName::Ident(n) => (*n).desugar_field_name(a, state),
      ObjectFieldName::String(n) => (*n).desugar_field_name(a, state),
      ObjectFieldName::Computed(n) => (*n).desugar_field_name(a, state),
    }
  }
}

impl DesugarField for ObjectFieldValue {
  fn desugar_field<T: ObjectState>(
    self,
    a: &mut Allocator,
    binds: SliceId<CoreLocalBind>,
    state: T,
  ) -> CoreObjectField {
    let span = self.span();
    let name = self.name.desugar_field_name(a, state);
    let kind = self.op.kind();

    let rest = self.value.desugar_expr(a, state);
    let value = a
      .exprs
      .alloc(CoreLocal {
        binds,
        rest: a.cores.alloc(rest),
      })
      .into_core_empty_span();

    CoreObjectField {
      key: a.cores.alloc(name),
      kind,
      value: a.cores.alloc(value),
      span,
    }
  }
}

impl DesugarField for ObjectFieldFunction {
  fn desugar_field<T: ObjectState>(
    self,
    a: &mut Allocator,
    binds: SliceId<CoreLocalBind>,
    state: T,
  ) -> CoreObjectField {
    ObjectFieldValue {
      name: self.name,
      op: match self.op {
        ObjectFieldFunctionOperator::Default(t) => ObjectFieldOperator::Default(t),
        ObjectFieldFunctionOperator::Hidden(t) => ObjectFieldOperator::Hidden(t),
        ObjectFieldFunctionOperator::Public(t) => ObjectFieldOperator::Public(t),
      },
      value: ExprFunction {
        function_token: Default::default(),
        left_paren_token: Default::default(),
        params: self.params,
        right_paren_token: Default::default(),
        body: self.value,
      }
      .into(),
    }
    .desugar_field(a, binds, state)
  }
}

impl DesugarAssert for ObjectFieldAssert {
  fn desugar_assert(self, a: &mut Allocator, binds: SliceId<CoreLocalBind>) -> Core {
    let span = self.span();

    let err_expr = if let Some((_, msg)) = self.msg {
      let msg = msg.desugar_expr(a, InObject);

      a.exprs.alloc(CoreExpr::Error(msg)).into_core_empty_span()
    } else {
      a.assertion_failed_ref.into_core_empty_span()
    };

    let cond = self.cond.desugar_expr(a, InObject);
    let if_expr = a
      .exprs
      .alloc(CoreIf {
        cond: a.cores.alloc(cond),
        if_true: a.cores.alloc(a.null_ref.into_core_empty_span()),
        if_false: a.cores.alloc(err_expr),
      })
      .into_core_empty_span();

    a.exprs
      .alloc(CoreLocal {
        binds,
        rest: a.cores.alloc(if_expr),
      })
      .into_core(span)
  }
}

impl DesugarBind for ObjectFieldLocal {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret {
    match self.bind {
      Bind::Value(b) => (*b).desugar_bind(a, state),
      Bind::Function(b) => (*b).desugar_bind(a, state),
    }
  }
}

impl DesugarBind for Bind {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret {
    match self {
      Bind::Value(b) => (*b).desugar_bind(a, state),
      Bind::Function(b) => (*b).desugar_bind(a, state),
    }
  }
}

impl DesugarBind for BindValue {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret {
    let span = self.span();

    CoreLocalBind {
      name: a.strings.intern(self.name.as_ref()),
      value: {
        let value = self.body.desugar_expr(a, state);
        a.cores.alloc(value)
      },
      span,
    }
  }
}

impl DesugarBind for BindFunction {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret {
    let span = self.span();

    CoreLocalBind {
      name: a.strings.intern(self.name.as_ref()),
      value: {
        let value = ExprFunction {
          function_token: Default::default(),
          left_paren_token: Default::default(),
          params: self.params,
          right_paren_token: Default::default(),
          body: self.body,
        }
        .desugar_expr(a, state);
        a.cores.alloc(value)
      },
      span,
    }
  }
}

impl DesugarParam for Param {
  type Ret = CoreFunctionParam;

  fn desugar_param<T: ObjectState>(self, a: &mut Allocator, state: T) -> Self::Ret {
    let span = self.span();
    let default_value = self
      .default_value
      .map(|(_, e)| e.desugar_expr(a, state))
      .unwrap_or(a.param_not_bound_ref.into_core_empty_span());

    CoreFunctionParam {
      name: a.strings.intern(self.name.as_ref()),
      default_value: a.cores.alloc(default_value),
      span,
    }
  }
}

trait DisplayCore {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result;
}

trait CoreExt: DisplayCore {
  fn display<'a, 'b>(&'a self, a: &'b Allocator) -> CoreDisplay<'a, 'b, Self>;
}

impl<C: DisplayCore> CoreExt for C {
  fn display<'a, 'b>(&'a self, a: &'b Allocator) -> CoreDisplay<'a, 'b, Self> {
    CoreDisplay(self, a)
  }
}

struct CoreDisplay<'a, 'b, C: DisplayCore + ?Sized>(&'a C, &'b Allocator);

impl<'a, 'b, C: DisplayCore + ?Sized> Display for CoreDisplay<'a, 'b, C> {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.indented_with(0, |f| DisplayCore::fmt(self.0, self.1, f))
  }
}

impl DisplayCore for Core {
  #[inline]
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    DisplayCore::fmt(self.expr.get(&a.exprs), a, f)
  }
}

impl DisplayCore for CoreExpr {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    match self {
      CoreExpr::Null => write!(f, "null"),
      CoreExpr::True => write!(f, "true"),
      CoreExpr::False => write!(f, "false"),
      CoreExpr::SelfValue => write!(f, "self"),
      CoreExpr::Super => write!(f, "super"),
      CoreExpr::Number(e) => write!(f, "{}", e),
      CoreExpr::Ident(e) => write!(f, "{}", &a.strings[*e]),
      CoreExpr::String(e) => {
        f.write_char('"')?;
        crate::utils::format_code_string(&a.strings[*e], f)?;
        f.write_char('"')
      }
      CoreExpr::Import(e) => {
        write!(f, "import \"")?;
        crate::utils::format_code_string(&a.strings[*e], f)?;
        f.write_char('"')
      }
      CoreExpr::ImportStr(e) => {
        write!(f, "importstr \"")?;
        crate::utils::format_code_string(&a.strings[*e], f)?;
        f.write_char('"')
      }
      CoreExpr::Object(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::ObjectComp(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Array(e) => {
        write!(f, "[\n")?;
        f.indented(|f| {
          for item in e.get(&a.cores) {
            DisplayCore::fmt(item, a, f)?;
            write!(f, ",\n");
          }

          Ok(())
        })?;
        write!(f, "]")?;

        Ok(())
      }
      CoreExpr::MemberAccess(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Local(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::If(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Binary(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Unary(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Function(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Apply(e) => DisplayCore::fmt(e, a, f),
      CoreExpr::Error(e) => {
        write!(f, "error ")?;
        DisplayCore::fmt(&a.exprs[e.expr], a, f)
      }
    }
  }
}

impl DisplayCore for CoreObject {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    write!(f, "{{\n")?;
    f.indented(|f| {
      for assert in self.asserts.get(&a.cores) {
        f.indented(|f| {
          write!(f, "assert ")?;
          DisplayCore::fmt(assert, a, f)?;
          write!(f, ",")?;

          Ok(())
        })?;
      }

      for field in self.fields.get(&a.fields) {
        f.indented(|f| {
          write!(f, "[")?;
          DisplayCore::fmt(field.key.get(&a.cores), a, f)?;
          write!(f, "]")?;
          DisplayCore::fmt(&field.kind, a, f)?;
          write!(f, " ");
          DisplayCore::fmt(field.value.get(&a.cores), a, f)?;

          Ok(())
        })?;
        write!(f, ",\n");
      }

      Ok(())
    })?;
    write!(f, "}}")?;

    Ok(())
  }
}

impl DisplayCore for ObjectFieldOperatorKind {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    match self {
      ObjectFieldOperatorKind::Default => write!(f, ":"),
      ObjectFieldOperatorKind::Hidden => write!(f, "::"),
      ObjectFieldOperatorKind::Public => write!(f, ":::"),
      ObjectFieldOperatorKind::Merge => write!(f, "+:"),
      ObjectFieldOperatorKind::MergeHidden => write!(f, "+::"),
      ObjectFieldOperatorKind::MergePublic => write!(f, "+:::"),
    }
  }
}

impl DisplayCore for CoreObjectComp {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    write!(f, "{{\n")?;
    f.indented(|f| {
      f.indented(|f| {
        write!(f, "[")?;
        DisplayCore::fmt(self.field.get(&a.cores), a, f)?;
        write!(f, "]")?;
        DisplayCore::fmt(&ObjectFieldOperatorKind::Default, a, f)?;
        write!(f, " ")?;
        DisplayCore::fmt(self.value.get(&a.cores), a, f)?;

        Ok(())
      })?;

      write!(f, "\nfor {} in ", &a.strings[self.id])?;
      DisplayCore::fmt(self.list.get(&a.cores), a, f)?;

      Ok(())
    })?;
    write!(f, "}}")?;

    Ok(())
  }
}

impl DisplayCore for CoreMemberAccess {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    DisplayCore::fmt(self.target.get(&a.cores), a, f)?;
    f.indented(|f| {
      write!(f, "[")?;
      DisplayCore::fmt(self.field.get(&a.cores), a, f)?;
      write!(f, "]")?;

      Ok(())
    })
  }
}

impl DisplayCore for CoreLocalBind {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    f.indented(|f| {
      write!(f, "{} = ", &a.strings[self.name])?;
      DisplayCore::fmt(self.value.get(&a.cores), a, f)
    })
  }
}

impl DisplayCore for CoreLocal {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    f.indented(|f| {
      write!(f, "local\n")?;
      let mut first = true;
      for bind in self.binds.get(&a.binds) {
        if first {
          first = false
        } else {
          write!(f, ",\n")?;
        }

        DisplayCore::fmt(bind, a, f)?;
      }

      write!(f, ";\n")
    })?;

    DisplayCore::fmt(self.rest.get(&a.cores), a, f)
  }
}

impl DisplayCore for CoreIf {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    f.indented(|f| {
      write!(f, "\nif ")?;
      DisplayCore::fmt(self.cond.get(&a.cores), a, f)?;
      write!(f, "\nthen ")?;
      DisplayCore::fmt(self.if_true.get(&a.cores), a, f)?;
      write!(f, "\nelse ")?;
      DisplayCore::fmt(self.if_false.get(&a.cores), a, f)?;

      Ok(())
    })
  }
}

impl DisplayCore for BinaryOperatorKind {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    let op = match self {
      BinaryOperatorKind::Mul => "*",
      BinaryOperatorKind::Div => "/",
      BinaryOperatorKind::Plus => "+",
      BinaryOperatorKind::Minus => "-",
      BinaryOperatorKind::ShiftLeft => "<<",
      BinaryOperatorKind::ShiftRight => ">>",
      BinaryOperatorKind::GreaterThan => ">",
      BinaryOperatorKind::GreaterThanOrEqual => ">=",
      BinaryOperatorKind::LessThan => "<",
      BinaryOperatorKind::LessThanOrEqual => "<=",
      BinaryOperatorKind::BitwiseAnd => "&",
      BinaryOperatorKind::BitwiseXor => "^",
      BinaryOperatorKind::BitwiseOr => "|",
      BinaryOperatorKind::And => "&&",
      BinaryOperatorKind::Or => "|",
    };

    f.write_str(op)
  }
}

impl DisplayCore for CoreBinary {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    DisplayCore::fmt(self.lhs.get(&a.cores), a, f)?;
    f.indented(|f| {
      write!(f, "\n")?;
      DisplayCore::fmt(&self.op, a, f)?;
      write!(f, " ")?;
      DisplayCore::fmt(self.rhs.get(&a.cores), a, f)
    })
  }
}

impl DisplayCore for UnaryOperatorKind {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    let op = match self {
      UnaryOperatorKind::Not => "!",
      UnaryOperatorKind::BitwiseNot => "~",
      UnaryOperatorKind::Plus => "+",
      UnaryOperatorKind::Minus => "-",
    };

    f.write_str(op)
  }
}

impl DisplayCore for CoreUnary {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    DisplayCore::fmt(&self.op, a, f)?;
    DisplayCore::fmt(self.expr.get(&a.cores), a, f)
  }
}

impl DisplayCore for CoreFunctionParam {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    write!(f, "{} = ", &a.strings[self.name])?;
    DisplayCore::fmt(self.default_value.get(&a.cores), a, f)
  }
}

impl DisplayCore for CoreFunction {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    f.indented(|f| {
      write!(f, "function (\n")?;
      for param in self.params.get(&a.params) {
        DisplayCore::fmt(param, a, f)?;
      }

      Ok(())
    })?;
    write!(f, "\n)")?;
    f.indented(|f| {
      write!(f, "\n")?;
      DisplayCore::fmt(self.expr.get(&a.cores), a, f)
    })
  }
}

impl DisplayCore for CoreApplyNamedArg {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    write!(f, "{} = ", &a.strings[self.name])?;
    DisplayCore::fmt(self.value.get(&a.cores), a, f)
  }
}

impl DisplayCore for CoreApply {
  fn fmt(&self, a: &Allocator, f: &mut IndentFormatter) -> fmt::Result {
    DisplayCore::fmt(self.target.get(&a.cores), a, f)?;
    f.indented(|f| {
      f.write_str("(\n")?;
      for arg in self.positionals.get(&a.cores) {
        DisplayCore::fmt(arg, a, f)?;
        f.write_str(",\n")?;
      }

      for named in self.named.get(&a.named_args) {
        DisplayCore::fmt(named, a, f)?;
        f.write_str(",\n")?;
      }

      Ok(())
    })?;
    f.write_str(")")
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lex::span::FileId;
  use test_generator::test_resources;

  #[derive(PartialEq, Eq, Clone, Copy)]
  struct PrettyString<'a>(&'a str);

  impl<'a> PrettyString<'a> {
    #[inline]
    fn new<S: AsRef<str> + ?Sized>(value: &'a S) -> Self {
      PrettyString(value.as_ref())
    }
  }

  impl<'a> fmt::Debug for PrettyString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      f.write_str(self.0)
    }
  }

  macro_rules! assert_eq {
    ($left:expr, $right:expr $(,$($rest:tt)*)?) => {
      pretty_assertions::assert_eq!(
        PrettyString::new($left),
        PrettyString::new($right)
        $(,$($rest)*)?
      );
    }
  }

  const IS_CI: bool = core::option_env!("CI").is_some();

  // TODO: CFG std or get file content embedded
  #[test_resources("test-cases/core/*.jsonnet")]
  fn verify_desugar(path: &str) {
    use std::path::Path;
    let path: &Path = path.as_ref();
    let golden = path.with_extension("golden");

    let content = std::fs::read(path).expect("read input");
    let content = core::str::from_utf8(&content).expect("valid utf8");
    let expr: Expr = crate::parse::parse(content, FileId::UNKNOWN).expect("parse");

    let mut allocator = Allocator::new();
    let core = expr.desugar_expr(&mut allocator, NotInObject);
    let output = format!("{}\n", core.display(&allocator));

    if !golden.is_file() {
      if IS_CI {
        panic!("missing golden file for {} on CI", path.display());
      }

      std::fs::write(golden, output).expect("write golden");
    } else {
      let golden_content = std::fs::read(golden).expect("read golden");
      let golden_content = core::str::from_utf8(&golden_content).expect("golden valid utf8");
      assert_eq!(golden_content, output.as_str());
    }
  }
}
