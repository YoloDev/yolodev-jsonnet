use super::*;
use crate::*;

impl_format! {
  fn CoreExpr(e, f) {
    match e {
      CoreExpr::Literal(it) => it.format(f),
      CoreExpr::SelfValue(it) => it.format(f),
      CoreExpr::Super(it) => it.format(f),
      CoreExpr::Object(it) => it.format(f),
      CoreExpr::ObjectComp(it) => it.format(f),
      CoreExpr::Array(it) => it.format(f),
      CoreExpr::MemberAccess(it) => it.format(f),
      CoreExpr::Ident(it) => it.format(f),
      CoreExpr::Local(it) => it.format(f),
      CoreExpr::If(it) => it.format(f),
      CoreExpr::Binary(it) => it.format(f),
      CoreExpr::Unary(it) => it.format(f),
      CoreExpr::Function(it) => it.format(f),
      CoreExpr::Apply(it) => it.format(f),
      CoreExpr::Error(it) => it.format(f),
      CoreExpr::Import(it) => it.format(f),
    }.group()
  }
}

impl_format! {
  fn LiteralCoreExpr(e, f) {
    match &e.token {
      LiteralToken::Null => f.text("null"),
      LiteralToken::True => f.text("true"),
      LiteralToken::False => f.text("false"),
      LiteralToken::String(v) => f.text(format!("{:?}", v)),
      LiteralToken::Number(v) => {
        let mut buf = [b'\0'; 20];
        let len = dtoa::write(&mut buf[..], *v).unwrap();
        let s = core::str::from_utf8(&buf[..len]).unwrap();
        let s = String::from(s);

        f.text(s)
      },
    }
  }
}

impl_format! {
  fn SelfCoreExpr(_, f) {
    f.text("self")
  }
}

impl_format! {
  fn SuperCoreExpr(_, f) {
    f.text("super")
  }
}

impl_format! {
  fn IdentCoreExpr(e, f) {
    e.ident.format(f)
  }
}

impl_format! {
  fn CoreIdent(e, f) {
    let id: i64 = e.id.map_or(-1, |n| n.get() as i64);
    f.text(format!("{}#{}", &e.name, id))
  }
}

impl_format! {
  fn CoreLocalBind(e, f) {
    e.ident.format(f)
      .append(f.space())
      .append("=")
      .append(f.line().append(e.value.format(f)).nest(2))
      .group()
  }
}

impl_format! {
  fn LocalCoreExpr(e, f) {
    f.text("local")
      .append(f.space())
      .append(
        f.intersperse(
          e.binds.iter().map(|b| b.format(f)),
          f.text(",").append(f.hardline())
        ).nest(6)
      )
      .append(";")
      .append(f.hardline())
      .append(e.rest.format(f))
  }
}

impl_format! {
  fn ErrorCoreExpr(e, f) {
    f.text("error")
      .append(f.space())
      .append(e.expr.format(f))
  }
}

impl_format! {
  fn ImportCoreExpr(e, f) {
    match e.kind {
      CoreImportKind::Jsonnet => f.text("import"),
      CoreImportKind::String => f.text("importstr"),
    }
    .append(f.space())
    .append(format!("{:?}", &e.file))
  }
}

impl_format! {
  fn UnaryCoreExpr(e, f) {
    e.op.format(f)
      .append(e.expr.format(f))
  }
}

impl_format! {
  fn CoreUnaryOperator(e, f) {
    match e {
      CoreUnaryOperator::Plus(_) => f.text("+"),
      CoreUnaryOperator::Minus(_) => f.text("-"),
      CoreUnaryOperator::Not(_) => f.text("!"),
      CoreUnaryOperator::BitNeg(_) => f.text("~"),
    }
  }
}

impl_format! {
  fn BinaryCoreExpr(e, f) {
    e.lhs.format(f)
      .append(f.space())
      .append(
        e.op.format(f)
          .append(f.space())
          .append(e.rhs.format(f))
          .nest(2)
      )
      .parens()
  }
}

impl_format! {
  fn CoreBinaryOperator(e, f) {
    match e {
      CoreBinaryOperator::Mult(_) => f.text("*"),
      CoreBinaryOperator::Div(_) => f.text("/"),
      CoreBinaryOperator::Plus(_) => f.text("+"),
      CoreBinaryOperator::Minus(_) => f.text("-"),
      CoreBinaryOperator::ShiftL(_) => f.text("<<"),
      CoreBinaryOperator::ShiftR(_) => f.text(">>"),
      CoreBinaryOperator::GreaterThan(_) => f.text(">"),
      CoreBinaryOperator::GreaterThanOrEquals(_) => f.text(">="),
      CoreBinaryOperator::LessThan(_) => f.text("<"),
      CoreBinaryOperator::LessThanOrEquals(_) => f.text("<="),
      CoreBinaryOperator::BitAnd(_) => f.text("&"),
      CoreBinaryOperator::BitXor(_) => f.text("^"),
      CoreBinaryOperator::BitOr(_) => f.text("|"),
      CoreBinaryOperator::And(_) => f.text("&&"),
      CoreBinaryOperator::Or(_) => f.text("||"),
    }
  }
}

impl_format! {
  fn IfCoreExpr(e, f) {
    f.text("if")
      .append(f.space())
      .append(e.cond.format(f))
      .append(f.line())
      .append("then")
      .append(f.space())
      .append(e.if_true.format(f))
      .append(f.line())
      .append("else")
      .append(f.space())
      .append(e.if_false.format(f))
  }
}

impl_format! {
  fn ArrayCoreExpr(e, f) {
    if e.items.is_empty() {
      return f.text("[]");
    }

    let sep = f.text(",").append(f.line());

    f.intersperse(
      e.items.iter().map(|e| e.format(f)),
      sep.clone(),
    )
    .nest(2)
    .append(sep.flat_alt(f.nil()))
    .group()
    .brackets()
  }
}

impl_format! {
  fn ObjectCoreExpr(e, f) {
    if e.asserts.is_empty() && e.fields.is_empty() {
      return f.text("{}");
    }

    let sep = f.text(",").append(f.line());

    let asserts = f.intersperse(
      e.asserts.iter().map(|e|
        f.text("assert")
          .append(f.space())
          .append(e.format(f))),
      sep.clone());

    let fields = f.intersperse(
      e.fields.iter().map(|e| e.format(f)),
      sep.clone());

    let any_empty = e.asserts.is_empty() || e.fields.is_empty();

    asserts
      .append(if any_empty { f.nil() } else { f.line_() })
      .append(fields)
      .nest(2)
      .append(sep.flat_alt(f.nil()))
      .group()
      .braces()
  }
}

impl_format! {
  fn CoreObjectField(e, f) {
    e.name.format(f)
      .brackets()
      .append(":")
      .append(f.line())
      .append(e.value.format(f))
      .nest(2)
      .group()
  }
}

impl_format! {
  fn MemberAccessCoreExpr(e, f) {
    e.target.format(f)
      .append(
        f.line_()
          .append(e.field_name.format(f))
          .nest(2)
          .append(f.line_())
          .brackets()
      )
  }
}

impl_format! {
  fn ObjectCompCoreExpr(e, f) {
    let field_name =
      f.line_()
        .append(e.field_name.format(f))
        .nest(2)
        .append(f.line_())
        .brackets();

    let field =
      field_name
        .append(":")
        .append(f.line())
        .append(e.field_value.format(f).nest(2))
        .group();

    field.append(f.line())
      .append("for")
      .append(f.space())
      .append(e.loop_var_ident.format(f))
      .append(f.space())
      .append("in")
      .append(f.line().append(e.list.format(f).nest(2)).group())
  }
}

impl_format! {
  fn FunctionCoreExpr(e, f) {
    let sep = f.text(",").append(f.line());
    let params = f.intersperse(
      e.params.iter().map(|p| p.format(f)),
      sep.clone());

    let params = params
      .nest(2)
      .append(sep.flat_alt(f.nil()))
      .parens()
      .group();

    f.text("function")
      .append(params)
      .append(f.line().append(e.expr.format(f)).nest(2))
  }
}

impl_format! {
  fn CoreFunctionParam(e, f) {
    e.name.format(f)
      .append(f.space())
      .append("=")
      .append(f.line().append(e.default_value.format(f)).nest(2))
  }
}

impl_format! {
  fn ApplyCoreExpr(e, f) {
    let sep = f.text(",").append(f.line());
    let mut args = Vec::with_capacity(e.named.len() + e.positionals.len());
    args.extend(e.positionals.iter().map(|a| a.format(f)));
    args.extend(e.named.iter().map(|a| a.format(f)));

    let args = f.intersperse(args, sep.clone());

    let args = args
      .nest(2)
      .append(sep.flat_alt(f.nil()))
      .parens()
      .group();

    e.target.format(f)
      .append(args)
  }
}

impl_format! {
  fn CoreNamedArg(e, f) {
    f.text(e.name.as_str())
      .append(f.space())
      .append("=")
      .append(f.line().append(e.value.format(f)).nest(2))
  }
}
