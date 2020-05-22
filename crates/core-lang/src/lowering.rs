mod binding;

use crate::*;
use alloc::collections::VecDeque;
use binding::BinderFrame;
use jsonnet_syntax::{
  ast::{self, AstNode, AstToken},
  SmolStr,
};

type Error = (Option<TextRange>, String);

struct ExprCtx {
  in_object: bool,
}

impl ExprCtx {
  const NOT_IN_OBJECT: &'static ExprCtx = &ExprCtx { in_object: false };
  const IN_OBJECT: &'static ExprCtx = &ExprCtx { in_object: true };
}

trait Desugar<T: 'static, TCtx> {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &TCtx) -> T;
}

fn call_std_function(
  binder: &mut BinderFrame,
  name: &'static str,
  args: Vec<CoreExpr>,
) -> CoreExpr {
  const STD: SmolStr = SmolStr::new_inline_from_ascii(3, b"std");

  let std = IdentCoreExpr::new(binder.bind(STD.clone(), None).unwrap());
  let fn_expr = MemberAccessCoreExpr::new(std, LiteralCoreExpr::new_str(name));
  let apply_expr = ApplyCoreExpr::new(fn_expr, args, Vec::new());

  apply_expr.into()
}

fn param_not_bound_expr(name: &str) -> CoreExpr {
  ErrorCoreExpr::new_str(format!("Parameter '{}' not bound", name)).into()
}

fn desugar_arrcomp(
  errors: &mut Vec<Error>,
  binder: &mut BinderFrame,
  expr: CoreExpr,
  mut specs: VecDeque<ast::CompSpec>,
  ctx: &ExprCtx,
) -> CoreExpr {
  const ARR: SmolStr = SmolStr::new_inline_from_ascii(4, b"$arr");
  const I: SmolStr = SmolStr::new_inline_from_ascii(2, b"$i");

  debug_assert!(!specs.is_empty());

  let next = specs.pop_front().unwrap();
  let rest = if specs.is_empty() { None } else { Some(specs) };
  match (next, rest) {
    (ast::CompSpec::If(f), Some(specs)) => {
      let cond = f.expr().desugar(errors, binder, ctx);
      let if_true = desugar_arrcomp(errors, binder, expr, specs, ctx);
      let if_false = ArrayCoreExpr::new_empty();

      IfCoreExpr::new(cond, if_true, if_false).into_expr()
    }

    (ast::CompSpec::If(f), None) => {
      let cond = f.expr().desugar(errors, binder, ctx);
      let if_true = ArrayCoreExpr::new(vec![expr]);
      let if_false = ArrayCoreExpr::new_empty();

      IfCoreExpr::new(cond, if_true, if_false).into_expr()
    }

    (ast::CompSpec::For(f), Some(specs)) => {
      let mut binder = binder.frame();
      let arr_ident = binder.define(ARR.clone(), None).unwrap();
      let i_ident = binder.define(I.clone(), None).unwrap();

      let arr = IdentCoreExpr::new(arr_ident.clone()).into_expr();
      let i = IdentCoreExpr::new(i_ident.clone());

      let arr_bind = LocalBind::new(arr_ident, f.expr().desugar(errors, &mut binder, ctx));
      let arr_i = MemberAccessCoreExpr::new(arr.clone(), i.clone());
      let loop_bind_var = match f.id() {
        None => {
          errors.push((
            f.syntax().text_range().into(),
            "No for-spec identifier found.".into(),
          ));
          return ErrorCoreExpr::new_str("Missing for-spec identifier").into_expr();
        }
        Some(id) => binder
          .bind(id.name().into(), Some(id.syntax().text_range()))
          .unwrap(),
      };
      let loop_bind = LocalBind::new(loop_bind_var, arr_i);
      let inner = desugar_arrcomp(errors, &mut binder, expr, specs, ctx);
      let fn_body = LocalCoreExpr::new(vec![loop_bind], inner);
      let i_param = FunctionParam::new(i_ident.clone(), param_not_bound_expr(&i_ident.name));
      let inner_fn = FunctionCoreExpr::new(vec![i_param], fn_body).into_expr();
      let len = call_std_function(&mut binder, "length", vec![arr]);
      let arr_right = call_std_function(&mut binder, "makeArray", vec![len, inner_fn]);
      let joined = call_std_function(
        &mut binder,
        "join",
        vec![ArrayCoreExpr::new_empty().into_expr(), arr_right],
      );

      LocalCoreExpr::new(vec![arr_bind], joined).into_expr()
    }

    (ast::CompSpec::For(f), None) => {
      let mut binder = binder.frame();
      let arr_ident = binder.define(ARR.clone(), None).unwrap();
      let i_ident = binder.define(I.clone(), None).unwrap();

      let arr = IdentCoreExpr::new(arr_ident.clone()).into_expr();
      let i = IdentCoreExpr::new(i_ident.clone());

      let arr_bind = LocalBind::new(arr_ident, f.expr().desugar(errors, &mut binder, ctx));
      let arr_i = MemberAccessCoreExpr::new(arr.clone(), i.clone());
      let loop_bind_var = match f.id() {
        None => {
          errors.push((
            f.syntax().text_range().into(),
            "No for-spec identifier found.".into(),
          ));
          return ErrorCoreExpr::new_str("Missing for-spec identifier").into_expr();
        }
        Some(id) => binder
          .bind(id.name().into(), Some(id.syntax().text_range()))
          .unwrap(),
      };
      let loop_bind = LocalBind::new(loop_bind_var, arr_i);
      let inner = ArrayCoreExpr::new(vec![expr]);
      let fn_body = LocalCoreExpr::new(vec![loop_bind], inner);
      let i_param = FunctionParam::new(i_ident.clone(), param_not_bound_expr(&i_ident.name));
      let inner_fn = FunctionCoreExpr::new(vec![i_param], fn_body).into_expr();
      let len = call_std_function(&mut binder, "length", vec![arr]);
      let arr_right = call_std_function(&mut binder, "makeArray", vec![len, inner_fn]);
      let joined = call_std_function(
        &mut binder,
        "join",
        vec![ArrayCoreExpr::new_empty().into_expr(), arr_right],
      );

      LocalCoreExpr::new(vec![arr_bind], joined).into_expr()
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for Option<ast::Expr> {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    match self {
      None => ErrorCoreExpr::new_str("Missing expression").into_expr(),
      Some(e) => e.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::Expr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    todo!()
    // match self {
    //   ast::Expr::Apply(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Array(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::ArrayComp(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Assert(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Binary(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::ComputedFieldAccess(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Error(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::False(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::IdentFieldAccess(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Function(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Group(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Ident(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::If(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Import(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::ImportStr(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::InSuper(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Local(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Null(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Number(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Object(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::ObjectApply(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::ObjectComp(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::RootObj(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::SelfValue(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Slice(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::String(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::SuperField(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::SuperComputed(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::True(it) => it.desugar(errors, binder, ctx).into_expr(),
    //   ast::Expr::Unary(it) => it.desugar(errors, binder, ctx).into_expr(),
    // }
  }
}
