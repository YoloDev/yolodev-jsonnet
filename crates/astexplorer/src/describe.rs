use jsonnet_syntax::ast::*;
use jsonnet_syntax::SyntaxToken;
use serde::ser::*;

pub(crate) struct Describe<'a, T: ?Sized>(&'a T);

trait Spanned {
  fn span(&self) -> (u32, u32);
}

pub(crate) trait DescribeExt {
  fn describe<'a>(&'a self) -> Describe<'a, Self>;
}

impl<T> DescribeExt for T
where
  for<'b> Describe<'b, T>: Serialize,
{
  fn describe<'a>(&'a self) -> Describe<'a, Self> {
    Describe(self)
  }
}

macro_rules! impl_option {
  ($ty:ident) => {
    impl<'a> Serialize for Describe<'a, Option<$ty>> {
      #[inline]
      fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
      where
        S: Serializer,
      {
        self.0.as_ref().map(Describe).serialize(serializer)
      }
    }
  };
}

macro_rules! impl_node {
  (fn $ty:ident($self:ident, $s:ident, $len:literal) $b:block) => {
    impl Spanned for $ty {
      fn span(&self) -> (u32, u32) {
        let range = self.syntax().text_range();
        (range.start().into(), range.end().into())
      }
    }

    impl<'a> Serialize for Describe<'a, $ty> {
      fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
      where
        S: Serializer,
      {
        let mut $s = serializer.serialize_struct(stringify!($ty), $len + 2)?;
        $s.serialize_field("type", stringify!($ty))?;
        $s.serialize_field("span", &self.0.span())?;
        let $self = self.0;
        $b
        $s.end()
      }
    }

    impl_option!($ty);
  };
}

macro_rules! impl_enum {
  ($ty:ident {
    $(
      $variant:ident
    ),+$(,)?
  }) => {
    impl Spanned for $ty {
      fn span(&self) -> (u32, u32) {
        match self {
          $(
            $ty::$variant(it) => it.span(),
          )+
        }
      }
    }

    impl<'a> Serialize for Describe<'a, $ty> {
      fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
      where
        S: Serializer,
      {
        match self.0 {
          $(
            $ty::$variant(it) => it.describe().serialize(serializer),
          )+
        }
      }
    }

    impl_option!($ty);
  };
}

impl Spanned for SyntaxToken {
  fn span(&self) -> (u32, u32) {
    let range = self.text_range();
    (range.start().into(), range.end().into())
  }
}

impl<'a> Serialize for Describe<'a, SyntaxToken> {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    let mut s = serializer.serialize_struct(stringify!($ty), 2)?;
    s.serialize_field("type", &format!("{:?}", self.0.kind()))?;
    s.serialize_field("span", &self.0.span())?;
    s.end()
  }
}
impl_option!(SyntaxToken);

impl<'a, T> Serialize for Describe<'a, AstChildren<T>>
where
  T: AstNode + Clone,
  for<'b> Describe<'b, T>: Serialize,
{
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    let mut s = serializer.serialize_seq(None)?;
    let list: AstChildren<T> = Clone::clone(self.0);
    for node in list {
      s.serialize_element(&node.describe())?;
    }

    s.end()
  }
}

impl_node! {
  fn Ident(n, s, 1) {
    s.serialize_field("name", &n.name())?;
  }
}

impl_node! {
  fn Number(n, s, 1) {
    let text: &str = n.syntax().text().as_ref();
    s.serialize_field("value", text)?;
  }
}

impl_node! {
  fn String(n, s, 2) {
    let raw: &str = n.syntax().text().as_ref();
    let value = n.value();
    let value: Option<&str> = value.as_ref().map(|cow| cow.as_ref());
    s.serialize_field("raw", raw)?;
    s.serialize_field("value", &value)?;
  }
}

impl_node! {
  fn SourceFile(n, s, 1) {
    s.serialize_field("root", &n.root().describe())?;
  }
}

impl_node! {
  fn ErrorExpr(n, s, 2) {
    s.serialize_field("error_token", &n.error_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn StringExpr(n, s, 1) {
    s.serialize_field("token", &n.token().describe())?;
  }
}

impl_node! {
  fn AssertExpr(n, s, 6) {
    s.serialize_field("assert_token", &n.assert_token().describe())?;
    s.serialize_field("cond", &n.cond().describe())?;
    s.serialize_field("colon_token", &n.colon_token().describe())?;
    s.serialize_field("message", &n.message().describe())?;
    s.serialize_field("semicolon_token", &n.semicolon_token().describe())?;
    s.serialize_field("rest", &n.rest().describe())?;
  }
}

impl_node! {
  fn IfExpr(n, s, 6) {
    s.serialize_field("if_token", &n.if_token().describe())?;
    s.serialize_field("cond", &n.cond().describe())?;
    s.serialize_field("then_token", &n.then_token().describe())?;
    s.serialize_field("true_branch", &n.true_branch().describe())?;
    s.serialize_field("else_token", &n.else_token().describe())?;
    s.serialize_field("false_branch", &n.false_branch().describe())?;
  }
}

impl_node! {
  fn FunctionExpr(n, s, 3) {
    s.serialize_field("function_token", &n.function_token().describe())?;
    s.serialize_field("params", &n.params().describe())?;
    s.serialize_field("body", &n.body().describe())?;
  }
}

impl_node! {
  fn ParamList(n, s, 3) {
    s.serialize_field("l_paren_token", &n.l_paren_token().describe())?;
    s.serialize_field("params", &n.params().describe())?;
    s.serialize_field("r_paren_token", &n.r_paren_token().describe())?;
  }
}

impl_node! {
  fn Param(n, s, 3) {
    s.serialize_field("name", &n.name().describe())?;
    s.serialize_field("assign_token", &n.assign_token().describe())?;
    s.serialize_field("default_value", &n.default_value().describe())?;
  }
}

impl_node! {
  fn PositionalArg(n, s, 1) {
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn NamedArg(n, s, 3) {
    s.serialize_field("named_arg", &n.name().describe())?;
    s.serialize_field("assign_token", &n.assign_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_enum!(Arg { Positional, Named });

impl_node! {
  fn AssertObjField(n, s, 4) {
    s.serialize_field("assert_token", &n.assert_token().describe())?;
    s.serialize_field("cond", &n.cond().describe())?;
    s.serialize_field("colon_token", &n.colon_token().describe())?;
    s.serialize_field("message", &n.message().describe())?;
  }
}

impl_node! {
  fn IdentFieldName(n, s, 1) {
    s.serialize_field("name", &n.name().describe())?;
  }
}

impl_node! {
  fn StringFieldName(n, s, 1) {
    s.serialize_field("name", &n.name().describe())?;
  }
}

impl_node! {
  fn ComputedFieldName(n, s, 3) {
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_enum!(ObjectFieldName {
  Ident,
  String,
  Computed,
});

impl_enum!(ObjectFieldAssignmentOp {
  Default,
  Hidden,
  Visible,
  MergeDefault,
  MergeHidden,
  MergeVisible,
});

impl_node! {
  fn ValueObjField(n, s, 3) {
    s.serialize_field("name", &n.name().describe())?;
    s.serialize_field("op", &n.op().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn FunctionObjField(n, s, 4) {
    s.serialize_field("name", &n.name().describe())?;
    s.serialize_field("params", &n.params().describe())?;
    s.serialize_field("op", &n.op().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn LocalObjField(n, s, 2) {
    s.serialize_field("local_bind", &n.local_token().describe())?;
    s.serialize_field("bind", &n.bind().describe())?;
  }
}

impl_enum!(ObjectField {
  Assert,
  Function,
  Local,
  Value,
});

impl_node! {
  fn ValueBind(n, s, 3) {
    s.serialize_field("name", &n.name().describe())?;
    s.serialize_field("assign_token", &n.assign_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn FunctionBind(n, s, 4) {
    s.serialize_field("name", &n.name().describe())?;
    s.serialize_field("params", &n.params().describe())?;
    s.serialize_field("assign_token", &n.assign_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_enum!(Bind { Function, Value });

impl_node! {
  fn ImportExpr(n, s, 2) {
    s.serialize_field("import_token", &n.import_token().describe())?;
    s.serialize_field("value", &n.value().describe())?;
  }
}

impl_node! {
  fn ImportStrExpr(n, s, 2) {
    s.serialize_field("importstr_token", &n.importstr_token().describe())?;
    s.serialize_field("value", &n.value().describe())?;
  }
}

impl_node! {
  fn LocalExpr(n, s, 4) {
    s.serialize_field("local_token", &n.local_token().describe())?;
    s.serialize_field("binds", &n.binds().describe())?;
    s.serialize_field("semicolon_token", &n.semicolon_token().describe())?;
    s.serialize_field("rest", &n.rest().describe())?;
  }
}

impl_node! {
  fn BindList(n, s, 1) {
    s.serialize_field("bindings", &n.bindings().describe())?;
  }
}

impl_enum!(UnaryOp {
  Plus,
  Minus,
  Not,
  BitNeg
});

impl_node! {
  fn UnaryExpr(n, s, 2) {
    s.serialize_field("op", &n.op().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_enum!(BinaryOp {
  Mult,
  Div,
  Mod,
  Plus,
  Minus,
  ShiftL,
  ShiftR,
  GreaterThan,
  GreaterThanOrEquals,
  LessThan,
  LessThanOrEquals,
  In,
  Equals,
  NotEquals,
  BitAnd,
  BitXor,
  BitOr,
  And,
  Or,
});

impl_node! {
  fn BinaryExpr(n, s, 3) {
    s.serialize_field("lhs", &n.lhs().describe())?;
    s.serialize_field("op", &n.op().describe())?;
    s.serialize_field("rhs", &n.rhs().describe())?;
  }
}

impl_node! {
  fn SliceExpr(n, s, 2) {
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_node! {
  fn ComputedFieldAccessExpr(n, s, 4) {
    s.serialize_field("target", &n.target().describe())?;
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_node! {
  fn IdentFieldAccessExpr(n, s, 3) {
    s.serialize_field("target", &n.target().describe())?;
    s.serialize_field("dot_token", &n.dot_token().describe())?;
    s.serialize_field("field_name", &n.field_name().describe())?;
  }
}

impl_node! {
  fn ApplyExpr(n, s, 3) {
    s.serialize_field("target", &n.target().describe())?;
    s.serialize_field("args", &n.args().describe())?;
    s.serialize_field("tailstrict_token", &n.tailstrict_token().describe())?;
  }
}

impl_node! {
  fn ArgList(n, s, 3) {
    s.serialize_field("l_paren_token", &n.l_paren_token().describe())?;
    s.serialize_field("args", &n.args().describe())?;
    s.serialize_field("r_paren_token", &n.r_paren_token().describe())?;
  }
}

impl_node! {
  fn ObjApplyExpr(n, s, 2) {
    s.serialize_field("target", &n.target().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn InSuperExpr(n, s, 3) {
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("in_token", &n.in_token().describe())?;
    s.serialize_field("super_token", &n.super_token().describe())?;
  }
}

impl_node! {
  fn GroupExpr(n, s, 3) {
    s.serialize_field("l_paren_token", &n.l_paren_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("r_paren_token", &n.r_paren_token().describe())?;
  }
}

impl_node! {
  fn NullExpr(n, s, 1) {
    s.serialize_field("null_token", &n.null_token().describe())?;
  }
}

impl_node! {
  fn TrueExpr(n, s, 1) {
    s.serialize_field("true_token", &n.true_token().describe())?;
  }
}

impl_node! {
  fn FalseExpr(n, s, 1) {
    s.serialize_field("false_token", &n.false_token().describe())?;
  }
}

impl_node! {
  fn SelfExpr(n, s, 1) {
    s.serialize_field("self_token", &n.self_token().describe())?;
  }
}

impl_node! {
  fn RootObjExpr(n, s, 1) {
    s.serialize_field("root_token", &n.root_token().describe())?;
  }
}

impl_node! {
  fn NumberExpr(n, s, 1) {
    s.serialize_field("number_token", &n.number_token().describe())?;
  }
}

impl_node! {
  fn IdentExpr(n, s, 1) {
    s.serialize_field("ident_token", &n.ident_token().describe())?;
  }
}

impl_node! {
  fn SuperFieldExpr(n, s, 3) {
    s.serialize_field("super_token", &n.super_token().describe())?;
    s.serialize_field("dot_token", &n.dot_token().describe())?;
    s.serialize_field("field_name", &n.field_name().describe())?;
  }
}

impl_node! {
  fn SuperComputedExpr(n, s, 4) {
    s.serialize_field("super_token", &n.super_token().describe())?;
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_node! {
  fn ArrayExpr(n, s, 3) {
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("items", &n.items().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_node! {
  fn ForCompSpec(n, s, 4) {
    s.serialize_field("for_token", &n.for_token().describe())?;
    s.serialize_field("id", &n.id().describe())?;
    s.serialize_field("in_token", &n.in_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_node! {
  fn IfCompSpec(n, s, 2) {
    s.serialize_field("if_token", &n.if_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
  }
}

impl_enum!(CompSpec { For, If });

impl_node! {
  fn CompSpecList(n, s, 1) {
    s.serialize_field("comp_specs", &n.comp_specs().describe())?;
  }
}

impl_node! {
  fn ArrayCompExpr(n, s, 5) {
    s.serialize_field("l_brack_token", &n.l_brack_token().describe())?;
    s.serialize_field("expr", &n.expr().describe())?;
    s.serialize_field("comma_token", &n.comma_token().describe())?;
    s.serialize_field("specs", &n.specs().describe())?;
    s.serialize_field("r_brack_token", &n.r_brack_token().describe())?;
  }
}

impl_node! {
  fn ObjectExpr(n, s, 3) {
    s.serialize_field("l_curly_token", &n.l_curly_token().describe())?;
    s.serialize_field("fields", &n.fields().describe())?;
    s.serialize_field("r_curly_token", &n.r_curly_token().describe())?;
  }
}

impl_node! {
  fn ObjectCompExpr(n, s, 5) {
    s.serialize_field("l_curly_token", &n.l_curly_token().describe())?;
    s.serialize_field("locals", &n.locals().describe())?;
    s.serialize_field("field", &n.field().describe())?;
    s.serialize_field("specs", &n.specs().describe())?;
    s.serialize_field("r_curly_token", &n.r_curly_token().describe())?;
  }
}

impl_enum!(Expr {
  Apply,
  Array,
  ArrayComp,
  Assert,
  Binary,
  ComputedFieldAccess,
  Error,
  False,
  IdentFieldAccess,
  Function,
  Group,
  Ident,
  If,
  Import,
  ImportStr,
  InSuper,
  Local,
  Null,
  Number,
  Object,
  ObjectApply,
  ObjectComp,
  RootObj,
  SelfValue,
  Slice,
  String,
  SuperField,
  SuperComputed,
  True,
  Unary,
});
