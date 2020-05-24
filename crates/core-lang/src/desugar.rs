mod binding;

use crate::*;
use binding::BinderFrame;
use core::iter::Peekable;
use jsonnet_syntax::{
  ast::{self, AstChildren, AstNode, AstToken},
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

trait Desugar<T: 'static, TCtx: ?Sized> {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &TCtx) -> T;
}

const ERR: SmolStr = SmolStr::new_inline_from_ascii(4, b"$err");
const ROOT: SmolStr = SmolStr::new_inline_from_ascii(1, b"$");

fn call_std_function(
  binder: &mut BinderFrame,
  name: &'static str,
  args: Vec<CoreExpr>,
) -> CoreExpr {
  const STD: SmolStr = SmolStr::new_inline_from_ascii(3, b"std");

  let std = IdentCoreExpr::new(binder.bind(STD.clone(), None).unwrap());
  let fn_expr = MemberAccessCoreExpr::new(std, LiteralCoreExpr::new_str(name));
  let apply_expr = ApplyCoreExpr::new(fn_expr, args, Vec::new(), false);

  apply_expr.into()
}

fn param_not_bound_expr(name: &str) -> CoreExpr {
  ErrorCoreExpr::new_str(format!("Parameter '{}' not bound", name)).into()
}

// Note: All loop variables (`x` and `y` in `for x in [] for y in []`)
// must have already been defined outside of this call.
fn desugar_arrcomp(
  errors: &mut Vec<Error>,
  binder: &mut BinderFrame,
  expr: CoreExpr,
  mut specs: Peekable<AstChildren<ast::CompSpec>>,
  ctx: &ExprCtx,
) -> CoreExpr {
  const ARR: SmolStr = SmolStr::new_inline_from_ascii(4, b"$arr");
  const I: SmolStr = SmolStr::new_inline_from_ascii(2, b"$i");

  debug_assert!(specs.peek().is_some());

  let next = specs.next().unwrap();
  let rest = if specs.peek().is_none() {
    None
  } else {
    Some(specs)
  };

  match (next, rest) {
    (ast::CompSpec::If(f), Some(specs)) => {
      let text_range = f.syntax().text_range();
      let cond = f.expr().desugar(errors, binder, ctx);
      let if_true = desugar_arrcomp(errors, binder, expr, specs, ctx);
      let if_false = ArrayCoreExpr::new_empty();

      IfCoreExpr::new_from(text_range, cond, if_true, if_false).into_expr()
    }

    (ast::CompSpec::If(f), None) => {
      let text_range = f.syntax().text_range();
      let cond = f.expr().desugar(errors, binder, ctx);
      let if_true = ArrayCoreExpr::new(vec![expr]);
      let if_false = ArrayCoreExpr::new_empty();

      IfCoreExpr::new_from(text_range, cond, if_true, if_false).into_expr()
    }

    (ast::CompSpec::For(f), Some(specs)) => {
      let text_range = f.syntax().text_range();
      let mut binder = binder.frame();
      let arr_ident = binder.define(ARR.clone(), None).unwrap();
      let i_ident = binder.define(I.clone(), None).unwrap();

      let arr = IdentCoreExpr::new(arr_ident.clone()).into_expr();
      let i = IdentCoreExpr::new(i_ident.clone());

      let arr_bind = CoreLocalBind::new(arr_ident, f.expr().desugar(errors, &mut binder, ctx));
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
      let loop_bind = CoreLocalBind::new(loop_bind_var, arr_i);
      let inner = desugar_arrcomp(errors, &mut binder, expr, specs, ctx);
      let fn_body = LocalCoreExpr::new(vec![loop_bind], inner);
      let i_param = CoreFunctionParam::new(i_ident.clone(), param_not_bound_expr(&i_ident.name));
      let inner_fn = FunctionCoreExpr::new(vec![i_param], fn_body).into_expr();
      let len = call_std_function(&mut binder, "length", vec![arr]);
      let arr_right = call_std_function(&mut binder, "makeArray", vec![len, inner_fn]);
      let joined = call_std_function(
        &mut binder,
        "join",
        vec![ArrayCoreExpr::new_empty().into_expr(), arr_right],
      );

      LocalCoreExpr::new_from(text_range, vec![arr_bind], joined).into_expr()
    }

    (ast::CompSpec::For(f), None) => {
      let text_range = f.syntax().text_range();
      let mut binder = binder.frame();
      let arr_ident = binder.define(ARR.clone(), None).unwrap();
      let i_ident = binder.define(I.clone(), None).unwrap();

      let arr = IdentCoreExpr::new(arr_ident.clone()).into_expr();
      let i = IdentCoreExpr::new(i_ident.clone());

      let arr_bind = CoreLocalBind::new(arr_ident, f.expr().desugar(errors, &mut binder, ctx));
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
      let loop_bind = CoreLocalBind::new(loop_bind_var, arr_i);
      let inner = ArrayCoreExpr::new(vec![expr]);
      let fn_body = LocalCoreExpr::new(vec![loop_bind], inner);
      let i_param = CoreFunctionParam::new(i_ident.clone(), param_not_bound_expr(&i_ident.name));
      let inner_fn = FunctionCoreExpr::new(vec![i_param], fn_body).into_expr();
      let len = call_std_function(&mut binder, "length", vec![arr]);
      let arr_right = call_std_function(&mut binder, "makeArray", vec![len, inner_fn]);
      let joined = call_std_function(
        &mut binder,
        "join",
        vec![ArrayCoreExpr::new_empty().into_expr(), arr_right],
      );

      LocalCoreExpr::new_from(text_range, vec![arr_bind], joined).into_expr()
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for Option<ast::Expr> {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    match self {
      None => {
        errors.push((None, "Missing expression".into()));
        ErrorCoreExpr::new_str("Missing expression").into_expr()
      }
      Some(e) => e.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::Expr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    match self {
      ast::Expr::Apply(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Array(it) => it.desugar(errors, binder, ctx),
      ast::Expr::ArrayComp(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Assert(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Binary(it) => it.desugar(errors, binder, ctx),
      ast::Expr::ComputedFieldAccess(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Error(it) => it.desugar(errors, binder, ctx),
      ast::Expr::False(it) => it.desugar(errors, binder, ctx),
      ast::Expr::IdentFieldAccess(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Function(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Group(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Ident(it) => it.desugar(errors, binder, ctx),
      ast::Expr::If(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Import(it) => it.desugar(errors, binder, ctx),
      ast::Expr::ImportStr(it) => it.desugar(errors, binder, ctx),
      ast::Expr::InSuper(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Local(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Null(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Number(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Object(it) => it.desugar(errors, binder, ctx),
      ast::Expr::ObjectApply(it) => it.desugar(errors, binder, ctx),
      ast::Expr::ObjectComp(it) => it.desugar(errors, binder, ctx),
      ast::Expr::RootObj(it) => it.desugar(errors, binder, ctx),
      ast::Expr::SelfValue(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Slice(it) => it.desugar(errors, binder, ctx),
      ast::Expr::String(it) => it.desugar(errors, binder, ctx),
      ast::Expr::SuperField(it) => it.desugar(errors, binder, ctx),
      ast::Expr::SuperComputed(it) => it.desugar(errors, binder, ctx),
      ast::Expr::True(it) => it.desugar(errors, binder, ctx),
      ast::Expr::Unary(it) => it.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ObjectExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();
    let mut locals = Vec::new();
    let mut asserts = Vec::new();
    let mut values = Vec::new();
    let mut functions = Vec::new();

    for field in self.fields() {
      match field {
        ast::ObjectField::Assert(it) => asserts.push(it),
        ast::ObjectField::Function(it) => functions.push(it),
        ast::ObjectField::Local(it) => locals.push(it),
        ast::ObjectField::Value(it) => values.push(it),
      }
    }

    let (asserts, fields) = {
      let mut binder = binder.frame();
      let mut binds = Vec::with_capacity(locals.len() + 1);

      if !ctx.in_object {
        binds.push(CoreLocalBind::new(
          binder.define(ROOT.clone(), None).unwrap(),
          SelfCoreExpr::new(),
        ));
      }

      for local in locals.iter().flat_map(|l| l.bind()).flat_map(|b| b.name()) {
        if let Err(_) = binder.define_from(local) {
          errors.push((Some(text_range), "Duplicate binding".into()));
        }
      }

      binds.extend(
        locals
          .into_iter()
          .map(|local| local.desugar(errors, &mut binder, ctx)),
      );

      let asserts = asserts
        .into_iter()
        .map(|assert| assert.desugar(errors, &mut binder, &binds))
        .collect::<Vec<_>>();

      let mut fields = Vec::with_capacity(values.len() + functions.len());
      fields.extend(
        values
          .into_iter()
          .filter_map(|f| f.desugar(errors, &mut binder, &binds)),
      );
      fields.extend(
        functions
          .into_iter()
          .filter_map(|f| f.desugar(errors, &mut binder, &binds)),
      );

      (asserts, fields)
    };

    let fields = fields
      .into_iter()
      .map(|f| f.desugar(errors, binder, ctx))
      .collect::<Vec<_>>();

    ObjectCoreExpr::new_from(text_range, asserts, fields).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ObjectCompExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    const ARR: SmolStr = SmolStr::new_inline_from_ascii(4, b"$arr");
    //const I: SmolStr = SmolStr::new_inline_from_ascii(2, b"$i");

    let text_range = self.syntax().text_range();
    let mut binder = binder.frame();
    let arr_ident = binder.define(ARR.clone(), None).unwrap();
    let arr = IdentCoreExpr::new(arr_ident.clone());

    let specs = match self.specs() {
      None => {
        errors.push((Some(text_range), "Missing object comprehension spec".into()));
        return ErrorCoreExpr::new_str("Missing object comprehension spec").into_expr();
      }
      Some(s) => s.comp_specs(),
    };

    let idents = specs
      .clone()
      .filter_map(|spec| match spec {
        ast::CompSpec::For(for_spec) => for_spec.id(),
        ast::CompSpec::If(_) => None,
      })
      .filter_map(|id| match binder.define_from(id.clone()) {
        Ok(ident) => Some(ident),
        Err(e) => {
          errors.push((Some(id.syntax().text_range()), e));
          None
        }
      })
      .collect::<Vec<_>>();

    let arr_locals = idents
      .iter()
      .enumerate()
      .map(|(idx, id)| {
        CoreLocalBind::new(
          id.clone(),
          MemberAccessCoreExpr::new(arr.clone(), LiteralCoreExpr::new_int(idx as u32)),
        )
      })
      .collect::<Vec<_>>();

    let (comp_field_name_expr, comp_field_value_expr) = match self.field() {
      None => {
        errors.push((
          Some(text_range),
          "Missing field in object comprehension expression".into(),
        ));
        return ErrorCoreExpr::new_str("Missing field in object comprehension expression")
          .into_expr();
      }
      Some(f) => (f.name(), f.expr()),
    };

    let field_name_expr = LocalCoreExpr::new(
      arr_locals.clone(),
      match comp_field_name_expr {
        None => {
          errors.push((
            Some(text_range),
            "Missing field name in object comprehension expression".into(),
          ));
          ErrorCoreExpr::new_str("Missing field name in object comprehension expression")
            .into_expr()
        }
        Some(field) => field.desugar(errors, &mut binder, ctx),
      },
    );

    let mut value_locals = arr_locals;
    value_locals.extend(self.locals().filter_map(|l| match l.bind() {
      None => {
        errors.push((Some(l.syntax().text_range()), "Missing binding".into()));
        None
      }
      Some(b) => Some(b.desugar(errors, &mut binder, ctx)),
    }));

    let field_value_expr = LocalCoreExpr::new(
      value_locals,
      match comp_field_value_expr {
        None => {
          errors.push((
            Some(text_range),
            "Missing field value in object comprehension expression".into(),
          ));
          ErrorCoreExpr::new_str("Missing field value in object comprehension expression")
            .into_expr()
        }
        Some(field) => field.desugar(errors, &mut binder, ExprCtx::IN_OBJECT),
      },
    );

    let arr_exprs = ArrayCoreExpr::new(
      idents
        .into_iter()
        .map(IdentCoreExpr::new)
        .map(|e| e.into_expr())
        .collect::<Vec<_>>(),
    )
    .into_expr();
    let arr_expr = desugar_arrcomp(errors, &mut binder, arr_exprs, specs.peekable(), ctx);

    ObjectCompCoreExpr::new_from(
      text_range,
      field_name_expr,
      field_value_expr,
      arr_ident,
      arr_expr,
    )
    .into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ArrayCompExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let mut binder = binder.frame();
    let specs = match self.specs() {
      None => {
        errors.push((Some(text_range), "Missing object comprehension spec".into()));
        return ErrorCoreExpr::new_str("Missing object comprehension spec").into_expr();
      }
      Some(s) => s.comp_specs(),
    };

    // Define all loop vars
    let _ = specs
      .clone()
      .filter_map(|spec| match spec {
        ast::CompSpec::For(for_spec) => for_spec.id(),
        ast::CompSpec::If(_) => None,
      })
      .filter_map(|id| match binder.define_from(id.clone()) {
        Ok(ident) => Some(ident),
        Err(e) => {
          errors.push((Some(id.syntax().text_range()), e));
          None
        }
      })
      .skip_while(|_| true)
      .next();

    let expr = self.expr().desugar(errors, &mut binder, ctx);
    desugar_arrcomp(errors, &mut binder, expr, specs.peekable(), ctx).with_range(text_range)
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::LocalExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();
    let mut binder = binder.frame();

    for bind in self
      .binds()
      .into_iter()
      .flat_map(|b| b.bindings())
      .flat_map(|b| b.name())
    {
      if let Err(_) = binder.define_from(bind) {
        errors.push((Some(text_range), "Duplicate variable definition".into()));
      }
    }

    let binds = match self.binds() {
      None => {
        errors.push((Some(text_range), "No binds in local expression".into()));
        return ErrorCoreExpr::new_str("No binds in local expression").into_expr();
      }

      Some(b) => b,
    }
    .bindings()
    .map(|b| b.desugar(errors, &mut binder, ctx))
    .collect::<Vec<_>>();

    let rest = self.rest().desugar(errors, &mut binder, ctx);
    LocalCoreExpr::new_from(text_range, binds, rest).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ObjApplyExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let lhs = self.target().desugar(errors, binder, ctx);
    let rhs = self.expr().desugar(errors, binder, ctx);

    BinaryCoreExpr::new_from(text_range, lhs, CoreBinaryOperator::plus(), rhs).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::FunctionExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let mut binder = binder.frame();
    for param in self
      .params()
      .iter()
      .flat_map(|p| p.params())
      .flat_map(|p| p.name())
    {
      if let Err(_) = binder.define_from(param) {
        errors.push((Some(text_range), "Duplicate parameter definition".into()));
      }
    }

    let params = match self.params() {
      None => {
        errors.push((Some(text_range), "No function params list".into()));
        return ErrorCoreExpr::new_str("No function params list").into_expr();
      }
      Some(p) => p,
    }
    .params()
    .map(|p| p.desugar(errors, &mut binder, ctx))
    .collect::<Vec<_>>();

    let expr = self.body().desugar(errors, &mut binder, ctx);

    FunctionCoreExpr::new_from(text_range, params, expr).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::AssertExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let cond = self.cond().desugar(errors, binder, ctx);
    let if_true = self.rest().desugar(errors, binder, ctx);
    let if_false = match self.message() {
      None => match self.cond() {
        None => ErrorCoreExpr::new_str("Assertion failed"),
        Some(c) => ErrorCoreExpr::new_str(format!("Assertion failed: {}", c.syntax().text())),
      },
      Some(m) => ErrorCoreExpr::new(m.desugar(errors, binder, ctx)),
    };

    IfCoreExpr::new_from(text_range, cond, if_true, if_false).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::SliceExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let arr = self.target().desugar(errors, binder, ctx);

    let from = self.from_expr().map_or_else(
      || LiteralCoreExpr::new_null().into_expr(),
      |e| e.desugar(errors, binder, ctx),
    );

    let to = self.to_expr().map_or_else(
      || LiteralCoreExpr::new_null().into_expr(),
      |e| e.desugar(errors, binder, ctx),
    );

    let step = self.step_expr().map_or_else(
      || LiteralCoreExpr::new_null().into_expr(),
      |e| e.desugar(errors, binder, ctx),
    );

    call_std_function(binder, "slice", vec![arr, from, to, step]).with_range(text_range)
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::IfExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let cond = self.cond().desugar(errors, binder, ctx);
    let if_true = self.true_branch().desugar(errors, binder, ctx);
    let if_false = self.false_branch().map_or_else(
      || LiteralCoreExpr::new_null().into_expr(),
      |e| e.desugar(errors, binder, ctx),
    );

    IfCoreExpr::new_from(text_range, cond, if_true, if_false).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::IdentFieldAccessExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let target = self.target().desugar(errors, binder, ctx);
    let field_name = match self.field_name() {
      None => {
        errors.push((Some(text_range), "Missing field name".into()));
        return ErrorCoreExpr::new_str("Missing field name").into_expr();
      }
      Some(id) => LiteralCoreExpr::new_str(id.name()).into_expr(),
    };

    MemberAccessCoreExpr::new_from(text_range, target, field_name).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ComputedFieldAccessExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let target = self.target().desugar(errors, binder, ctx);
    let field_name = self.expr().desugar(errors, binder, ctx);

    MemberAccessCoreExpr::new_from(text_range, target, field_name).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::SuperFieldExpr {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let target = match self.super_token() {
      None => {
        errors.push((Some(text_range), "Missing super".into()));
        SuperCoreExpr::new()
      }
      Some(t) => SuperCoreExpr::new_from(t.text_range()),
    };

    let field_name = match self.field_name() {
      None => {
        errors.push((Some(text_range), "Missing field name".into()));
        return ErrorCoreExpr::new_str("Missing field name").into_expr();
      }
      Some(id) => LiteralCoreExpr::new_str(id.name()).into_expr(),
    };

    MemberAccessCoreExpr::new_from(text_range, target, field_name).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::SuperComputedExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let target = match self.super_token() {
      None => {
        errors.push((Some(text_range), "Missing super".into()));
        SuperCoreExpr::new()
      }
      Some(t) => SuperCoreExpr::new_from(t.text_range()),
    };

    let field_name = self.expr().desugar(errors, binder, ctx);

    MemberAccessCoreExpr::new_from(text_range, target, field_name).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::BinaryExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    use jsonnet_syntax::ast::BinaryOp;

    let text_range = self.syntax().text_range();

    let op = match self.op() {
      None => {
        errors.push((Some(text_range), "Missing op".into()));
        return ErrorCoreExpr::new_str("Missing op").into_expr();
      }
      Some(op) => op,
    };

    let lhs = self.lhs().desugar(errors, binder, ctx);
    let rhs = self.rhs().desugar(errors, binder, ctx);

    match op {
      BinaryOp::NotEquals(_) => UnaryCoreExpr::new_from(
        text_range,
        CoreUnaryOperator::not(),
        call_std_function(binder, "equals", vec![lhs, rhs]),
      )
      .into_expr(),

      BinaryOp::Equals(_) => call_std_function(binder, "equals", vec![lhs, rhs])
        .with_range(text_range)
        .into_expr(),

      BinaryOp::Modulo(_) => call_std_function(binder, "mod", vec![lhs, rhs])
        .with_range(text_range)
        .into_expr(),

      BinaryOp::InObject(_) => call_std_function(binder, "objectHasEx", vec![rhs, lhs])
        .with_range(text_range)
        .into_expr(),

      op => {
        let op = CoreBinaryOperator::from_token(op).unwrap();

        BinaryCoreExpr::new_from(text_range, lhs, op, rhs).into_expr()
      }
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::InSuperExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let lhs = self.expr().desugar(errors, binder, ctx);
    let rhs = match self.super_token() {
      None => {
        errors.push((Some(text_range), "Missing super".into()));
        SuperCoreExpr::new()
      }
      Some(t) => SuperCoreExpr::new_from(t.text_range()),
    }
    .into_expr();

    call_std_function(binder, "objectHasEx", vec![rhs, lhs])
      .with_range(text_range)
      .into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ApplyExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let mut positionals = Vec::new();
    let mut named = Vec::new();

    let args = match self.args() {
      None => {
        errors.push((Some(text_range), "Missing args list".into()));
        return ErrorCoreExpr::new_str("Missing args list").into_expr();
      }
      Some(a) => a.args(),
    };

    for arg in args {
      match arg {
        ast::Arg::Positional(arg) => {
          if !named.is_empty() {
            errors.push((
              Some(arg.syntax().text_range()),
              "Positional argument after named argument(s)".into(),
            ));
          }

          positionals.push(arg.expr().desugar(errors, binder, ctx));
        }

        ast::Arg::Named(arg) => {
          named.push(arg.desugar(errors, binder, ctx));
        }
      }
    }

    let target = self.target().desugar(errors, binder, ctx);
    let is_tailstrict = self.tailstrict_token().is_some();

    ApplyCoreExpr::new_from(text_range, target, positionals, named, is_tailstrict).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ArrayExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let items = self
      .items()
      .map(|item| item.desugar(errors, binder, ctx))
      .collect::<Vec<_>>();
    ArrayCoreExpr::new_from(text_range, items).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ErrorExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let expr = self.expr().desugar(errors, binder, ctx);
    ErrorCoreExpr::new_from(text_range, expr).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::TrueExpr {
  fn desugar(self, _: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    LiteralCoreExpr::new_true_from(text_range).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::FalseExpr {
  fn desugar(self, _: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    LiteralCoreExpr::new_false_from(text_range).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::NullExpr {
  fn desugar(self, _: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    LiteralCoreExpr::new_null_from(text_range).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::GroupExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    self.expr().desugar(errors, binder, ctx)
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::IdentExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let ident = match self.ident_token() {
      None => {
        errors.push((Some(text_range), "Missing identifier".into()));
        return ErrorCoreExpr::new_str("Missing identifier").into_expr();
      }

      Some(id) => id,
    };

    match binder.bind_from(ident) {
      Ok(ident) => IdentCoreExpr::new_from(text_range, ident).into_expr(),
      Err(e) => {
        errors.push((Some(text_range), e.clone()));
        ErrorCoreExpr::new_str(e).into_expr()
      }
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ImportExpr {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let file = match self.value() {
      None => {
        errors.push((Some(text_range), "Missing import value".into()));
        return ErrorCoreExpr::new_str("Missing import value").into_expr();
      }

      Some(s) => match s.value() {
        None => {
          let text_range = s.syntax().text_range();

          errors.push((Some(text_range), "Failed to parse string value".into()));
          return ErrorCoreExpr::new_str("Failed to parse string value").into_expr();
        }

        Some(s) => String::from(s.as_ref()),
      },
    };

    ImportCoreExpr::new_from(text_range, file, CoreImportKind::Jsonnet).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ImportStrExpr {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let file = match self.value() {
      None => {
        errors.push((Some(text_range), "Missing import value".into()));
        return ErrorCoreExpr::new_str("Missing import value").into_expr();
      }

      Some(s) => match s.value() {
        None => {
          let text_range = s.syntax().text_range();

          errors.push((Some(text_range), "Failed to parse string value".into()));
          return ErrorCoreExpr::new_str("Failed to parse string value").into_expr();
        }

        Some(s) => String::from(s.as_ref()),
      },
    };

    ImportCoreExpr::new_from(text_range, file, CoreImportKind::String).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::StringExpr {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let value = match self.token() {
      None => {
        errors.push((Some(text_range), "Missing string token".into()));
        return ErrorCoreExpr::new_str("Missing string token").into_expr();
      }

      Some(s) => match s.value() {
        None => {
          let text_range = s.syntax().text_range();

          errors.push((Some(text_range), "Failed to parse string value".into()));
          return ErrorCoreExpr::new_str("Failed to parse string value").into_expr();
        }

        Some(s) => String::from(s.as_ref()),
      },
    };

    LiteralCoreExpr::new_str_from(text_range, value).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::NumberExpr {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let number = match self.number_token() {
      None => {
        errors.push((Some(text_range), "Missing number value".into()));
        return ErrorCoreExpr::new_str("Missing number value").into_expr();
      }

      Some(n) => match n.value() {
        None => {
          let text_range = n.syntax().text_range();

          errors.push((Some(text_range), "Failed to parse number value".into()));
          return ErrorCoreExpr::new_str("Failed to parse number value").into_expr();
        }

        Some(n) => n,
      },
    };

    LiteralCoreExpr::new_number_from(text_range, number).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::RootObjExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let ident_range = match self.root_token() {
      None => {
        errors.push((Some(text_range), "Missing root token".into()));
        return ErrorCoreExpr::new_str("Missing root token").into_expr();
      }

      Some(id) => id.text_range(),
    };

    match binder.bind(ROOT.clone(), Some(ident_range)) {
      Ok(ident) => IdentCoreExpr::new_from(text_range, ident).into_expr(),
      Err(e) => {
        errors.push((Some(text_range), e.clone()));
        ErrorCoreExpr::new_str(e).into_expr()
      }
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::SelfExpr {
  fn desugar(self, _: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    SelfCoreExpr::new_from(text_range).into_expr()
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::UnaryExpr {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let op = match self.op() {
      None => {
        errors.push((Some(text_range), "Missing op".into()));
        return ErrorCoreExpr::new_str("Missing op").into_expr();
      }
      Some(tok) => CoreUnaryOperator::from_token(tok).unwrap(),
    };

    let expr = self.expr().desugar(errors, binder, ctx);

    UnaryCoreExpr::new_from(text_range, op, expr).into_expr()
  }
}

impl Desugar<CoreNamedArg, ExprCtx> for ast::NamedArg {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreNamedArg {
    let text_range = self.syntax().text_range();

    let name = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing argument name".into()));
        ERR.clone()
      }
      Some(ident) => ident.syntax().text().clone(),
    };

    let value = self.expr().desugar(errors, binder, ctx);

    CoreNamedArg::new_from(text_range, name, value)
  }
}

impl Desugar<CoreFunctionParam, ExprCtx> for ast::Param {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreFunctionParam {
    // Expectes function param names to already be defined.
    let text_range = self.syntax().text_range();

    let name = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing param name".into()));
        binder.new_undef()
      }

      Some(ident) => match binder.bind_from(ident.clone()) {
        Err(e) => {
          errors.push((Some(ident.syntax().text_range()), e));
          binder.new_undef()
        }

        Ok(binding) => binding,
      },
    };

    let default_value = match self.default_value() {
      None => ErrorCoreExpr::new_str(format!("Parameter '{}' not bound", &name.name)).into_expr(),
      Some(e) => e.desugar(errors, binder, ctx).into_expr(),
    };

    CoreFunctionParam::new_from(text_range, name, default_value)
  }
}

impl Desugar<CoreLocalBind, ExprCtx> for ast::Bind {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreLocalBind {
    match self {
      ast::Bind::Function(it) => it.desugar(errors, binder, ctx),
      ast::Bind::Value(it) => it.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreLocalBind, ExprCtx> for ast::ValueBind {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreLocalBind {
    let text_range = self.syntax().text_range();

    let ident = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing member name".into()));
        binder.new_undef()
      }
      Some(ident) => match binder.bind_from(ident) {
        Err(e) => {
          errors.push((Some(text_range), e));
          binder.new_undef()
        }
        Ok(i) => i,
      },
    };

    let value = self.expr().desugar(errors, binder, ctx);
    CoreLocalBind::new_from(text_range, ident, value)
  }
}

impl Desugar<CoreLocalBind, ExprCtx> for ast::FunctionBind {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreLocalBind {
    let text_range = self.syntax().text_range();

    let ident = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing member name".into()));
        binder.new_undef()
      }
      Some(ident) => match binder.bind_from(ident) {
        Err(e) => {
          errors.push((Some(text_range), e));
          binder.new_undef()
        }
        Ok(i) => i,
      },
    };

    let value = {
      let mut binder = binder.frame();
      match self.params() {
        None => {
          errors.push((Some(text_range), "No function params list".into()));
          ErrorCoreExpr::new_str("No function params list").into_expr()
        }
        Some(p) => {
          for param in p.params().flat_map(|p| p.name()) {
            if let Err(_) = binder.define_from(param) {
              errors.push((Some(text_range), "Duplicate parameter definition".into()));
            }
          }

          let params = p
            .params()
            .map(|p| p.desugar(errors, &mut binder, ctx))
            .collect::<Vec<_>>();

          let expr = self.expr().desugar(errors, &mut binder, ctx);

          FunctionCoreExpr::new_from(text_range, params, expr).into_expr()
        }
      }
    };

    CoreLocalBind::new_from(text_range, ident, value)
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ObjectFieldName {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    match self {
      ast::ObjectFieldName::Ident(it) => it.desugar(errors, binder, ctx),
      ast::ObjectFieldName::String(it) => it.desugar(errors, binder, ctx),
      ast::ObjectFieldName::Computed(it) => it.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::IdentFieldName {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    match self.name() {
      None => {
        errors.push((Some(text_range), "Missing identifier".into()));
        return ErrorCoreExpr::new_str("Missing identifier").into_expr();
      }

      Some(ident) => LiteralCoreExpr::new_str_from(text_range, ident.name()).into_expr(),
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::StringFieldName {
  fn desugar(self, errors: &mut Vec<Error>, _: &mut BinderFrame, _: &ExprCtx) -> CoreExpr {
    let text_range = self.syntax().text_range();

    match self.name() {
      None => {
        errors.push((Some(text_range), "Missing string".into()));
        return ErrorCoreExpr::new_str("Missing string").into_expr();
      }

      Some(s) => match s.value() {
        None => {
          let text_range = s.syntax().text_range();

          errors.push((Some(text_range), "Failed to parse string".into()));
          return ErrorCoreExpr::new_str("Failed to parse string").into_expr();
        }

        Some(s) => LiteralCoreExpr::new_str_from(text_range, s.as_ref()).into_expr(),
      },
    }
  }
}

impl Desugar<CoreExpr, ExprCtx> for ast::ComputedFieldName {
  fn desugar(self, errors: &mut Vec<Error>, binder: &mut BinderFrame, ctx: &ExprCtx) -> CoreExpr {
    self.expr().desugar(errors, binder, ctx)
  }
}

impl Desugar<CoreLocalBind, ExprCtx> for ast::LocalObjField {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreLocalBind {
    let text_range = self.syntax().text_range();

    match self.bind() {
      None => {
        errors.push((Some(text_range), "Missing binding".into()));
        CoreLocalBind::new_from(
          text_range,
          binder.new_undef(),
          ErrorCoreExpr::new_str("Missing binding").into_expr(),
        )
      }

      Some(b) => b.desugar(errors, binder, ctx),
    }
  }
}

impl Desugar<CoreExpr, [CoreLocalBind]> for ast::AssertObjField {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &[CoreLocalBind],
  ) -> CoreExpr {
    let text_range = self.syntax().text_range();

    let cond = self.cond().desugar(errors, binder, ExprCtx::IN_OBJECT);
    let if_true = LiteralCoreExpr::new_null();
    let if_false = match self.message() {
      None => match self.cond() {
        None => ErrorCoreExpr::new_str("Assertion failed"),
        Some(c) => ErrorCoreExpr::new_str(format!("Assertion failed: {}", c.syntax().text())),
      },
      Some(m) => ErrorCoreExpr::new(m.desugar(errors, binder, ExprCtx::IN_OBJECT)),
    };

    LocalCoreExpr::new(
      ctx.iter().cloned(),
      IfCoreExpr::new_from(text_range, cond, if_true, if_false),
    )
    .into_expr()
  }
}

struct PartiallyDesugaredField {
  text_range: TextRange,
  name: ast::ObjectFieldName,
  op: CoreObjectFieldOperator,
  value: CoreExpr,
}

impl PartiallyDesugaredField {
  fn new_from(
    text_range: TextRange,
    name: ast::ObjectFieldName,
    op: CoreObjectFieldOperator,
    value: impl IntoCoreExpr,
  ) -> Self {
    PartiallyDesugaredField {
      text_range,
      name,
      op,
      value: value.into_expr(),
    }
  }
}

impl Desugar<CoreObjectField, ExprCtx> for PartiallyDesugaredField {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &ExprCtx,
  ) -> CoreObjectField {
    let name = self.name.desugar(errors, binder, ctx);

    CoreObjectField::new_from(self.text_range, name, self.op, self.value)
  }
}

impl Desugar<Option<PartiallyDesugaredField>, [CoreLocalBind]> for ast::ValueObjField {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &[CoreLocalBind],
  ) -> Option<PartiallyDesugaredField> {
    let text_range = self.syntax().text_range();

    let name = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing member name".into()));
        return None;
      }
      Some(name) => name,
    };

    //let name = self.name().desugar(errors, binder, ExprCtx::IN_OBJECT);
    let op = match self.op() {
      None => {
        errors.push((Some(text_range), "Invalid field operator".into()));
        CoreObjectFieldOperator::default()
      }
      Some(tok) => CoreObjectFieldOperator::from_token(tok).unwrap(),
    };
    let expr = self.expr().desugar(errors, binder, ExprCtx::IN_OBJECT);
    let value = LocalCoreExpr::new(ctx.iter().cloned(), expr);

    Some(PartiallyDesugaredField::new_from(
      text_range, name, op, value,
    ))
  }
}

impl Desugar<Option<PartiallyDesugaredField>, [CoreLocalBind]> for ast::FunctionObjField {
  fn desugar(
    self,
    errors: &mut Vec<Error>,
    binder: &mut BinderFrame,
    ctx: &[CoreLocalBind],
  ) -> Option<PartiallyDesugaredField> {
    let text_range = self.syntax().text_range();

    let name = match self.name() {
      None => {
        errors.push((Some(text_range), "Missing member name".into()));
        return None;
      }
      Some(name) => name,
    };

    let op = match self.op() {
      None => {
        errors.push((Some(text_range), "Invalid field operator".into()));
        CoreObjectFieldOperator::default()
      }
      Some(tok) => CoreObjectFieldOperator::from_token(tok).unwrap(),
    };

    let expr = {
      let mut binder = binder.frame();
      match self.params() {
        None => {
          errors.push((Some(text_range), "No function params list".into()));
          ErrorCoreExpr::new_str("No function params list").into_expr()
        }
        Some(p) => {
          for param in p.params().flat_map(|p| p.name()) {
            if let Err(_) = binder.define_from(param) {
              errors.push((Some(text_range), "Duplicate parameter definition".into()));
            }
          }

          let params = p
            .params()
            .map(|p| p.desugar(errors, &mut binder, ExprCtx::IN_OBJECT))
            .collect::<Vec<_>>();

          let expr = self.expr().desugar(errors, &mut binder, ExprCtx::IN_OBJECT);

          FunctionCoreExpr::new_from(text_range, params, expr).into_expr()
        }
      }
    };

    let value = LocalCoreExpr::new(ctx.iter().cloned(), expr);

    Some(PartiallyDesugaredField::new_from(
      text_range, name, op, value,
    ))
  }
}

/// Desugars an AST into the core language.
pub fn desugar(source_file: ast::SourceFile) -> (CoreExpr, Vec<(Option<TextRange>, String)>) {
  let mut binder = binding::Binder::new();
  let mut errors = Vec::new();
  let mut root_frame = binder.frame();

  let desugared = source_file
    .root()
    .desugar(&mut errors, &mut root_frame, ExprCtx::NOT_IN_OBJECT);
  drop(root_frame);

  (desugared, errors)
}
