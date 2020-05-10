//! The core language.

use crate::{
  ast::{full::*, punctuated::Punctuated},
  lex::{
    span::Span,
    token,
    token::{Ident, Spanned},
  },
  utils::intern::{StringId, StringInterner},
};
use alloc::{collections::VecDeque, rc::Rc};
use core::fmt::Debug;
use derive_more::From;
use hashbrown::HashMap;
use id_arena::{Arena, Id as ArenaId};

pub use crate::ast::full::{ObjectFieldOperatorKind, UnaryOperatorKind};

trait IntoCore: Sized {
  fn into_core(self, span: Span) -> Core;

  #[inline]
  fn into_core_empty_span(self) -> Core {
    self.into_core(Span::EMPTY)
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, From)]
struct CoreRef(ArenaId<CoreExpr>);

impl IntoCore for CoreRef {
  #[inline]
  fn into_core(self, span: Span) -> Core {
    Core { expr: self, span }
  }
}

impl IntoCore for ArenaId<CoreExpr> {
  #[inline]
  fn into_core(self, span: Span) -> Core {
    Core {
      expr: self.into(),
      span,
    }
  }
}

struct Allocator {
  exprs: Arena<CoreExpr>,
  strings: StringInterner,
  null_ref: CoreRef,
  true_ref: CoreRef,
  false_ref: CoreRef,
  self_ref: CoreRef,
  super_ref: CoreRef,
  std_ref: CoreRef,
  root_ref: CoreRef,
  empty_arr_ref: CoreRef,
  assertion_failed_ref: CoreRef,
  param_not_bound_ref: CoreRef,
  std_refs: HashMap<&'static str, CoreRef>,
}

impl Allocator {
  fn new() -> Allocator {
    let mut strings = StringInterner::with_capacity(1024);
    let mut exprs = Arena::<CoreExpr>::new();
    let null_ref = exprs.alloc(CoreExpr::Null).into();
    let true_ref = exprs.alloc(CoreExpr::True).into();
    let false_ref = exprs.alloc(CoreExpr::False).into();
    let self_ref = exprs.alloc(CoreExpr::SelfValue).into();
    let super_ref = exprs.alloc(CoreExpr::Super).into();
    let std_ref = exprs.alloc(CoreExpr::Ident(strings.intern("std"))).into();
    let root_ref = exprs.alloc(CoreExpr::Ident(strings.intern("$"))).into();
    let empty_arr_ref = exprs.alloc(CoreExpr::Array(Vec::new())).into();
    let assertion_failed_ref = {
      let message = exprs
        .alloc(CoreExpr::String(strings.intern("Assertion failed")))
        .into_core_empty_span();
      exprs.alloc(CoreExpr::Error(message)).into()
    };
    let param_not_bound_ref = {
      let message = exprs
        .alloc(CoreExpr::String(strings.intern("Parameter not bound")))
        .into_core_empty_span();
      exprs.alloc(CoreExpr::Error(message)).into()
    };

    Allocator {
      exprs,
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

  fn alloc(&mut self, e: impl Into<CoreExpr>) -> CoreRef {
    let id = self.exprs.alloc(e.into());
    CoreRef(id)
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
struct Core {
  expr: CoreRef,
  span: Span,
}

impl Core {
  #[inline]
  fn with_span(self, span: Span) -> Self {
    Self { span, ..self }
  }
}

#[derive(Debug, Clone, From)]
enum CoreExpr {
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
  Array(Vec<Core>),
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
struct CoreObjectField {
  pub key: Core,
  pub kind: ObjectFieldOperatorKind,
  pub value: Core,
}

#[derive(Debug, Clone)]
struct CoreObject {
  pub asserts: Vec<Core>,
  pub fields: Vec<CoreObjectField>,
}

#[derive(Debug, Clone)]
struct CoreObjectComp {
  pub field: Core,
  pub value: Core,
  pub id: StringId,
  pub list: Core,
}

#[derive(Debug, Clone)]
struct CoreMemberAccess {
  pub target: Core,
  pub field: Core,
}

#[derive(Debug, Clone)]
struct CoreLocalBind {
  pub name: StringId,
  pub value: Core,
}

#[derive(Debug, Clone)]
struct CoreLocal {
  pub binds: Vec<CoreLocalBind>,
  pub rest: Core,
}

#[derive(Debug, Clone)]
struct CoreIf {
  pub cond: Core,
  pub if_true: Core,
  pub if_false: Core,
}

#[derive(Debug, Clone)]
struct CoreBinary {
  pub lhs: Core,
  pub op: BinaryOperatorKind,
  pub rhs: Core,
}

#[derive(Debug, Clone)]
struct CoreUnary {
  pub op: UnaryOperatorKind,
  pub expr: Core,
}

#[derive(Debug, Clone)]
struct CoreFunctionParam {
  pub name: StringId,
  pub default_value: Core,
}

#[derive(Debug, Clone)]
struct CoreFunction {
  pub params: Vec<CoreFunctionParam>,
  pub expr: Core,
}

#[derive(Debug, Clone)]
struct CoreApply {
  pub target: Core,
  pub positionals: Vec<Core>,
  pub named: Vec<(StringId, Core)>,
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
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core;
}

trait DesugarAssert {
  fn desugar_assert(self, allocator: &mut Allocator, binds: &[CoreLocalBind]) -> Core;
}

trait DesugarField {
  fn desugar_field<T: ObjectState>(
    self,
    allocator: &mut Allocator,
    binds: &[CoreLocalBind],
    state: T,
  ) -> CoreObjectField;
}

trait DesugarBind {
  type Ret: Debug;

  fn desugar_bind<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret;
}

trait DesugarParam {
  type Ret: Debug;

  fn desugar_param<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret;
}

fn call_std_func(
  allocator: &mut Allocator,
  name: &'static str,
  args: impl IntoIterator<Item = Core>,
) -> Core {
  let arena = &mut allocator.exprs;
  let strings = &mut allocator.strings;
  let std_ref = allocator.std_ref;
  let target = allocator
    .std_refs
    .entry(name)
    .or_insert_with(|| {
      let field = arena
        .alloc(CoreExpr::Ident(strings.intern(name)))
        .into_core_empty_span();
      arena
        .alloc(CoreExpr::from(CoreMemberAccess {
          target: std_ref.into_core_empty_span(),
          field,
        }))
        .into()
    })
    .into_core_empty_span();

  let args = args.into_iter().collect();

  allocator
    .alloc(CoreApply {
      target: target,
      positionals: args,
      named: Vec::new(),
    })
    .into_core_empty_span()
}

fn desugar_arrcomp<T: ObjectState>(
  allocator: &mut Allocator,
  expr: Expr,
  mut specs: VecDeque<CompSpec>,
  state: T,
) -> Core {
  debug_assert!(!specs.is_empty());

  let next = specs.pop_front().unwrap();
  let rest = if specs.is_empty() { None } else { Some(specs) };
  match (next, rest) {
    (CompSpec::If(f), Some(specs)) => {
      let cond = f.expr.desugar_expr(allocator, state);
      let if_true = desugar_arrcomp(allocator, expr, specs, state);
      let if_false = allocator.empty_arr_ref.into_core_empty_span();

      allocator
        .alloc(CoreIf {
          cond,
          if_true,
          if_false,
        })
        .into_core(Span::EMPTY)
    }

    (CompSpec::If(f), None) => {
      let cond = f.expr.desugar_expr(allocator, state);
      let if_true = {
        let expr = expr.desugar_expr(allocator, state);
        allocator
          .alloc(CoreExpr::Array(vec![expr]))
          .into_core_empty_span()
      };
      let if_false = allocator.empty_arr_ref.into_core_empty_span();

      allocator
        .alloc(CoreIf {
          cond,
          if_true,
          if_false,
        })
        .into_core_empty_span()
    }

    (CompSpec::For(f), Some(specs)) => {
      let arr_id = allocator.strings.intern("arr");
      let i_id = allocator.strings.intern("i");

      let arr = allocator
        .alloc(CoreExpr::Ident(arr_id))
        .into_core_empty_span();
      let i = allocator
        .alloc(CoreExpr::Ident(i_id))
        .into_core_empty_span();

      let arr_bind = CoreLocalBind {
        name: arr_id.clone(),
        value: f.expr.desugar_expr(allocator, state),
      };

      let inner = desugar_arrcomp(allocator, expr, specs, state);
      let inner = allocator
        .alloc(CoreExpr::Array(vec![inner]))
        .into_core_empty_span();
      let arr_i = allocator
        .alloc(CoreMemberAccess {
          target: arr,
          field: i,
        })
        .into_core_empty_span();
      let loop_bind = CoreLocalBind {
        name: allocator.strings.intern(f.id.as_ref()),
        value: arr_i,
      };
      let fn_body = allocator
        .alloc(CoreLocal {
          binds: vec![loop_bind],
          rest: inner,
        })
        .into_core_empty_span();
      let i_param = CoreFunctionParam {
        name: i_id,
        default_value: allocator.param_not_bound_ref.into_core_empty_span(),
      };
      let inner_fn = allocator
        .alloc(CoreFunction {
          params: vec![i_param],
          expr: fn_body,
        })
        .into_core_empty_span();
      let len = call_std_func(allocator, "len", vec![arr]);
      let arr_right = call_std_func(allocator, "makeArray", vec![len, inner_fn]);
      let joined = call_std_func(
        allocator,
        "join",
        vec![allocator.empty_arr_ref.into_core_empty_span(), arr_right],
      );

      allocator
        .alloc(CoreLocal {
          binds: vec![arr_bind],
          rest: joined,
        })
        .into_core_empty_span()
    }

    (CompSpec::For(f), None) => {
      let arr_id = allocator.strings.intern("arr");
      let i_id = allocator.strings.intern("i");

      let arr = allocator
        .alloc(CoreExpr::Ident(arr_id))
        .into_core_empty_span();
      let i = allocator
        .alloc(CoreExpr::Ident(i_id))
        .into_core_empty_span();

      let arr_bind = CoreLocalBind {
        name: arr_id,
        value: f.expr.desugar_expr(allocator, state),
      };

      let inner = expr.desugar_expr(allocator, state);
      let inner = allocator
        .alloc(CoreExpr::Array(vec![inner]))
        .into_core_empty_span();
      let arr_i = allocator
        .alloc(CoreMemberAccess {
          target: arr,
          field: i,
        })
        .into_core_empty_span();
      let loop_bind = CoreLocalBind {
        name: allocator.strings.intern(f.id.as_ref()),
        value: arr_i,
      };
      let fn_body = allocator
        .alloc(CoreLocal {
          binds: vec![loop_bind],
          rest: inner,
        })
        .into_core_empty_span();
      let i_param = CoreFunctionParam {
        name: i_id,
        default_value: allocator.param_not_bound_ref.into_core_empty_span(),
      };
      let inner_fn = allocator
        .alloc(CoreFunction {
          params: vec![i_param],
          expr: fn_body,
        })
        .into_core_empty_span();
      let len = call_std_func(allocator, "len", vec![arr]);
      let arr_right = call_std_func(allocator, "makeArray", vec![len, inner_fn]);
      let joined = call_std_func(
        allocator,
        "join",
        vec![allocator.empty_arr_ref.into_core_empty_span(), arr_right],
      );

      allocator
        .alloc(CoreLocal {
          binds: vec![arr_bind],
          rest: joined,
        })
        .into_core_empty_span()
    }
  }
}

impl DesugarExpr for Expr {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    match self {
      Expr::Apply(e) => (*e).desugar_expr(allocator, state),
      Expr::Array(e) => (*e).desugar_expr(allocator, state),
      Expr::ArrayComp(e) => (*e).desugar_expr(allocator, state),
      Expr::Assert(e) => (*e).desugar_expr(allocator, state),
      Expr::Binary(e) => (*e).desugar_expr(allocator, state),
      Expr::ComputedFieldAccess(e) => (*e).desugar_expr(allocator, state),
      Expr::Error(e) => (*e).desugar_expr(allocator, state),
      Expr::False(e) => (*e).desugar_expr(allocator, state),
      Expr::FieldAccess(e) => (*e).desugar_expr(allocator, state),
      Expr::Function(e) => (*e).desugar_expr(allocator, state),
      Expr::Group(e) => (*e).desugar_expr(allocator, state),
      Expr::Ident(e) => (*e).desugar_expr(allocator, state),
      Expr::If(e) => (*e).desugar_expr(allocator, state),
      Expr::Import(e) => (*e).desugar_expr(allocator, state),
      Expr::ImportStr(e) => (*e).desugar_expr(allocator, state),
      Expr::InSuper(e) => (*e).desugar_expr(allocator, state),
      Expr::Local(e) => (*e).desugar_expr(allocator, state),
      Expr::Null(e) => (*e).desugar_expr(allocator, state),
      Expr::Number(e) => (*e).desugar_expr(allocator, state),
      Expr::Object(e) => (*e).desugar_expr(allocator, state),
      Expr::ObjectApply(e) => (*e).desugar_expr(allocator, state),
      Expr::ObjectComp(e) => (*e).desugar_expr(allocator, state),
      Expr::Root(e) => (*e).desugar_expr(allocator, state),
      Expr::SelfValue(e) => (*e).desugar_expr(allocator, state),
      Expr::Slice(e) => (*e).desugar_expr(allocator, state),
      Expr::String(e) => (*e).desugar_expr(allocator, state),
      Expr::Super(e) => (*e).desugar_expr(allocator, state),
      Expr::True(e) => (*e).desugar_expr(allocator, state),
      Expr::Unary(e) => (*e).desugar_expr(allocator, state),
    }
  }
}

impl DesugarExpr for ExprObject {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
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
      .map(|local| local.desugar_bind(allocator, state))
      .collect();
    if !T::IN_OBJECT {
      binds.push(CoreLocalBind {
        name: allocator.strings.intern("$"),
        value: allocator.self_ref.into_core_empty_span(),
      });
    }

    let asserts: Vec<_> = asserts
      .into_iter()
      .map(|assert| assert.desugar_assert(allocator, &binds))
      .collect();

    let mut fields = Vec::with_capacity(values.len() + functions.len());
    fields.extend(
      values
        .into_iter()
        .map(|f| f.desugar_field(allocator, &binds, state)),
    );
    fields.extend(
      functions
        .into_iter()
        .map(|f| f.desugar_field(allocator, &binds, state)),
    );

    allocator
      .alloc(CoreObject { asserts, fields })
      .into_core(span)

    // if T::IN_OBJECT {
    //   let binds = vec![
    //     CoreLocalBind {
    //       name: Rc::from("$outerself"),
    //       value: allocator.self_ref,
    //     },
    //     CoreLocalBind {
    //       name: Rc::from("$outersuper"),
    //       value: allocator.super_ref,
    //     },
    //   ];

    //   allocator.alloc(CoreLocal { binds, rest: obj }, Span::EMPTY)
    // } else {
    //   obj
    // }
  }
}

impl DesugarExpr for ExprObjectComp {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let arr_id = allocator.strings.intern("arr");
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

      local.desugar_expr(allocator, state)
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

      local.desugar_expr(allocator, InObject)
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

      comp.desugar_expr(allocator, state)
    };

    allocator
      .alloc(CoreObjectComp {
        field: field,
        value: value,
        id: arr_id,
        list: list,
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprArrayComp {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let mut spec = VecDeque::with_capacity(self.tail_spec.len() + 1);
    spec.push_back(self.for_spec.into());
    spec.extend(self.tail_spec);

    desugar_arrcomp(allocator, self.expr, spec, state)
  }
}

impl DesugarExpr for ExprLocal {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let binds = self
      .binds
      .into_iter()
      .map(|b| b.desugar_bind(allocator, state))
      .collect();

    let rest = self.body.desugar_expr(allocator, state);

    allocator.alloc(CoreLocal { binds, rest }).into_core(span)
  }
}

impl DesugarExpr for ExprObjectApply {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    ExprBinary {
      lhs: self.target,
      op: BinaryOperator::Plus(Default::default()),
      rhs: self.object.into(),
    }
    .desugar_expr(allocator, state)
    .with_span(span)
  }
}

impl DesugarExpr for ExprFunction {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let params = self
      .params
      .into_iter()
      .map(|p| p.desugar_param(allocator, state))
      .collect();

    let expr = self.body.desugar_expr(allocator, state);

    allocator
      .alloc(CoreFunction { params, expr })
      .into_core(span)
  }
}

impl DesugarExpr for ExprAssert {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let cond = self.cond.desugar_expr(allocator, state);
    let if_true = self.rest.desugar_expr(allocator, state);
    let if_false = if let Some((_, msg)) = self.msg {
      let err = msg.desugar_expr(allocator, state);
      allocator.alloc(CoreExpr::Error(err)).into_core_empty_span()
    } else {
      allocator.assertion_failed_ref.into_core_empty_span()
    };

    allocator
      .alloc(CoreIf {
        cond,
        if_true,
        if_false,
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprSlice {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let start = self
      .begin_index
      .map(|e| e.desugar_expr(allocator, state))
      .unwrap_or_else(|| allocator.null_ref.into_core_empty_span());
    let end = self
      .end_index
      .map(|e| e.desugar_expr(allocator, state))
      .unwrap_or_else(|| allocator.null_ref.into_core_empty_span());
    let step = self
      .step
      .map(|e| e.desugar_expr(allocator, state))
      .unwrap_or_else(|| allocator.null_ref.into_core_empty_span());

    call_std_func(allocator, "slice", vec![start, end, step])
  }
}

impl DesugarExpr for ExprIf {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let cond = self.cond.desugar_expr(allocator, state);
    let if_true = self.if_true.desugar_expr(allocator, state);
    let if_false = self
      .if_false
      .map(|(_, e)| e.desugar_expr(allocator, state))
      .unwrap_or_else(|| allocator.null_ref.into_core_empty_span());

    allocator
      .alloc(CoreIf {
        cond,
        if_true,
        if_false,
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprFieldAccess {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let target = self.target.desugar_expr(allocator, state);
    let field_span = self.field_name.span();
    let field = {
      let str_id = allocator.strings.intern(self.field_name.as_ref());
      allocator
        .alloc(CoreExpr::String(str_id))
        .into_core(field_span)
    };

    allocator
      .alloc(CoreMemberAccess { target, field })
      .into_core(span)
  }
}

impl DesugarExpr for SuperField {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let target = allocator.super_ref.into_core(self.super_token.span());
    let field_span = self.field_name.span();
    let field = {
      let str_id = allocator.strings.intern(self.field_name.as_ref());
      allocator
        .alloc(CoreExpr::String(str_id))
        .into_core(field_span)
    };

    allocator
      .alloc(CoreMemberAccess { target, field })
      .into_core(span)
  }
}

impl DesugarExpr for ExprBinary {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    match self.op {
      BinaryOperator::NotEqual(_) => {
        let expr = ExprBinary {
          lhs: self.lhs,
          op: BinaryOperator::Equal(Default::default()),
          rhs: self.rhs,
        }
        .desugar_expr(allocator, state);

        allocator
          .alloc(CoreUnary {
            op: UnaryOperatorKind::Not,
            expr,
          })
          .into_core(span)
      }

      BinaryOperator::Equal(_) => {
        let args = vec![
          self.lhs.desugar_expr(allocator, state),
          self.rhs.desugar_expr(allocator, state),
        ];

        call_std_func(allocator, "equals", args)
      }

      BinaryOperator::Mod(_) => {
        let args = vec![
          self.lhs.desugar_expr(allocator, state),
          self.rhs.desugar_expr(allocator, state),
        ];

        call_std_func(allocator, "mod", args)
      }

      BinaryOperator::In(_) => {
        let args = vec![
          self.rhs.desugar_expr(allocator, state),
          self.lhs.desugar_expr(allocator, state),
          allocator.true_ref.into_core_empty_span(),
        ];

        call_std_func(allocator, "objectHasEx", args)
      }

      _ => {
        let lhs = self.lhs.desugar_expr(allocator, state);
        let rhs = self.rhs.desugar_expr(allocator, state);

        allocator
          .alloc(CoreBinary {
            lhs,
            rhs,
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
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let args = vec![
      allocator.super_ref.into_core_empty_span(),
      self.target.desugar_expr(allocator, state),
      allocator.true_ref.into_core_empty_span(),
    ];

    call_std_func(allocator, "objectHasEx", args)
  }
}

impl DesugarExpr for ExprApply {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let mut positionals = Vec::new();
    let mut named = Vec::new();

    // args should already be validated to be positional before named.
    let mut found_named = false;
    for arg in self.args {
      match arg {
        Argument::Positional(a) => {
          assert!(!found_named, "positional afer named");
          positionals.push(a.value.desugar_expr(allocator, state));
        }
        Argument::Named(a) => {
          found_named = true;
          named.push((
            allocator.strings.intern(a.name.as_ref()),
            a.value.desugar_expr(allocator, state),
          ));
        }
      }
    }

    let target = self.target.desugar_expr(allocator, state);

    allocator
      .alloc(CoreApply {
        target,
        positionals,
        named,
      })
      .into_core(span)
  }
}

impl DesugarExpr for ExprArray {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let items = self
      .items
      .into_iter()
      .map(|e| e.desugar_expr(allocator, state))
      .collect();

    allocator.alloc(CoreExpr::Array(items)).into_core(span)
  }
}

impl DesugarExpr for ExprComputedFieldAccess {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let target = self.target.desugar_expr(allocator, state);
    let field = self.expr.desugar_expr(allocator, state);

    allocator
      .alloc(CoreMemberAccess { target, field })
      .into_core(span)
  }
}

impl DesugarExpr for ExprError {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let msg = self.expr.desugar_expr(allocator, state);

    allocator.alloc(CoreExpr::Error(msg)).into_core(span)
  }
}

impl DesugarExpr for ExprFalse {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.false_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprGroup {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    self.expr.desugar_expr(allocator, state)
  }
}

impl DesugarExpr for ExprIdent {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = allocator.strings.intern(self.name.as_ref());
    allocator.alloc(CoreExpr::Ident(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprImportStr {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = allocator.strings.intern(self.file.value.as_ref());
    allocator.alloc(CoreExpr::ImportStr(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprImport {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = allocator.strings.intern(self.file.value.as_ref());
    allocator.alloc(CoreExpr::Import(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprNull {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.null_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprNumber {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    allocator
      .alloc(CoreExpr::Number(self.value.into()))
      .into_core(span)
  }
}

impl DesugarExpr for ExprRoot {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.root_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprSelf {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.self_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprString {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.span();
    let str_id = allocator.strings.intern(self.value.as_ref());
    allocator.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarExpr for ExprSuper {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.super_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprTrue {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    allocator.true_ref.into_core(self.span())
  }
}

impl DesugarExpr for ExprUnary {
  fn desugar_expr<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    let span = self.span();
    let expr = self.expr.desugar_expr(allocator, state);

    allocator
      .alloc(CoreUnary {
        op: self.op.kind(),
        expr,
      })
      .into_core(span)
  }
}

trait DesugarFieldName {
  fn desugar_field_name<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core;
}

impl DesugarFieldName for FieldNameIdent {
  fn desugar_field_name<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.name.span();

    let str_id = allocator.strings.intern(self.name.as_ref());
    allocator.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarFieldName for FieldNameString {
  fn desugar_field_name<T: ObjectState>(self, allocator: &mut Allocator, _: T) -> Core {
    let span = self.name.span();

    let str_id = allocator.strings.intern(self.name.as_ref());
    allocator.alloc(CoreExpr::String(str_id)).into_core(span)
  }
}

impl DesugarFieldName for FieldNameComputed {
  fn desugar_field_name<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    self.name.desugar_expr(allocator, state)
  }
}

impl DesugarFieldName for ObjectFieldName {
  fn desugar_field_name<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Core {
    match self {
      ObjectFieldName::Ident(n) => (*n).desugar_field_name(allocator, state),
      ObjectFieldName::String(n) => (*n).desugar_field_name(allocator, state),
      ObjectFieldName::Computed(n) => (*n).desugar_field_name(allocator, state),
    }
  }
}

impl DesugarField for ObjectFieldValue {
  fn desugar_field<T: ObjectState>(
    self,
    allocator: &mut Allocator,
    binds: &[CoreLocalBind],
    state: T,
  ) -> CoreObjectField {
    let name = self.name.desugar_field_name(allocator, state);
    let kind = self.op.kind();

    let rest = self.value.desugar_expr(allocator, state);
    let value = allocator
      .alloc(CoreLocal {
        binds: binds.iter().cloned().collect(),
        rest,
      })
      .into_core_empty_span();

    CoreObjectField {
      key: name,
      kind,
      value,
    }
  }
}

impl DesugarField for ObjectFieldFunction {
  fn desugar_field<T: ObjectState>(
    self,
    allocator: &mut Allocator,
    binds: &[CoreLocalBind],
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
    .desugar_field(allocator, binds, state)
  }
}

impl DesugarAssert for ObjectFieldAssert {
  fn desugar_assert(self, allocator: &mut Allocator, binds: &[CoreLocalBind]) -> Core {
    let span = self.span();

    let err_expr = if let Some((_, msg)) = self.msg {
      let msg = msg.desugar_expr(allocator, InObject);

      allocator.alloc(CoreExpr::Error(msg)).into_core_empty_span()
    } else {
      allocator.assertion_failed_ref.into_core_empty_span()
    };

    let cond = self.cond.desugar_expr(allocator, InObject);
    let if_expr = allocator
      .alloc(CoreIf {
        cond,
        if_true: allocator.null_ref.into_core_empty_span(),
        if_false: err_expr,
      })
      .into_core_empty_span();

    allocator
      .alloc(CoreLocal {
        binds: binds.iter().cloned().collect(),
        rest: if_expr,
      })
      .into_core(span)
  }
}

impl DesugarBind for ObjectFieldLocal {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret {
    match self.bind {
      Bind::Value(b) => (*b).desugar_bind(allocator, state),
      Bind::Function(b) => (*b).desugar_bind(allocator, state),
    }
  }
}

impl DesugarBind for Bind {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret {
    match self {
      Bind::Value(b) => (*b).desugar_bind(allocator, state),
      Bind::Function(b) => (*b).desugar_bind(allocator, state),
    }
  }
}

impl DesugarBind for BindValue {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret {
    CoreLocalBind {
      name: allocator.strings.intern(self.name.as_ref()),
      value: self.body.desugar_expr(allocator, state),
    }
  }
}

impl DesugarBind for BindFunction {
  type Ret = CoreLocalBind;

  fn desugar_bind<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret {
    CoreLocalBind {
      name: allocator.strings.intern(self.name.as_ref()),
      value: ExprFunction {
        function_token: Default::default(),
        left_paren_token: Default::default(),
        params: self.params,
        right_paren_token: Default::default(),
        body: self.body,
      }
      .desugar_expr(allocator, state),
    }
  }
}

impl DesugarParam for Param {
  type Ret = CoreFunctionParam;

  fn desugar_param<T: ObjectState>(self, allocator: &mut Allocator, state: T) -> Self::Ret {
    let default_value = self
      .default_value
      .map(|(_, e)| e.desugar_expr(allocator, state))
      .unwrap_or(allocator.param_not_bound_ref.into_core_empty_span());

    CoreFunctionParam {
      name: allocator.strings.intern(self.name.as_ref()),
      default_value,
    }
  }
}
