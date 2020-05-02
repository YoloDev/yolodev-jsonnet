use crate::{
  ast::punctuated::Punctuated,
  lex::{
    error::ErrorToken,
    span::{FileId, Span},
    token,
    token::Token,
    IntoToken,
  },
  parse::buffer::Cursor,
};
use core::{cmp, convert::TryFrom, fmt::Debug};
use derive_more::From;
use token::*;

macro_rules! check_keyword_matches {
  (struct struct) => {};
  (enum enum) => {};
  (pub pub) => {};
}

macro_rules! strip_attrs_pub {
  ($mac:ident!($(#[$m:meta])* $pub:ident $($t:tt)*)) => {
    check_keyword_matches!(pub $pub);

    $mac!([$(#[$m])* $pub] $($t)*);
  }
}

macro_rules! ast_struct {
  (
    [$($attrs_pub:tt)*]
    struct $name:ident {$(
      $(#[$m:meta])* pub $field:ident: $field_ty:ty,
    )*}
  ) => {
    #[derive(Debug, Eq, PartialEq, Hash, Clone)]
    $($attrs_pub)* struct $name {
      $(
        $(#[$m])* pub $field: $field_ty,
      )*
    }

    impl private::Sealed for $name {}
    impl Spanned for $name {
      fn span(&self) -> Span {
        SpanBuilder::new()
          $(.add(&self.$field))*
          .into()
      }
    }
  };

  ($($t:tt)*) => {
    strip_attrs_pub!(ast_struct!($($t)*));
  };
}

macro_rules! ast_enum {
  (
    [$($attrs_pub:tt)*]
    enum $name:ident {$(
      $(#[$m:meta])* $variant:ident($inner:ty),
    )*}
  ) => {
    #[derive(Debug, Eq, PartialEq, Hash, Clone)]
    $($attrs_pub)* enum $name {
      $(
        $(#[$m])* $variant(Box<$inner>),
      )*
    }

    $(
      impl From<Box<$inner>> for $name {
        #[inline]
        fn from(expr: Box<$inner>) -> Self {
          Self::$variant(expr)
        }
      }

      impl From<$inner> for $name {
        #[inline]
        fn from(expr: $inner) -> Self {
          Self::$variant(Box::new(expr))
        }
      }

      impl TryFrom<$name> for $inner {
        type Error = $name;

        #[inline]
        fn try_from(expr: $name) -> Result<Self, Self::Error> {
          match expr {
            $name::$variant(e) => Ok(*e),
            expr => Err(expr),
          }
        }
      }
    )*

    impl private::Sealed for $name {}
    impl Spanned for $name {
      fn span(&self) -> Span {
        match self {
          $(Self::$variant(e) => Spanned::span(e.as_ref()),)*
        }
      }
    }
  };

  ($($t:tt)*) => {
    strip_attrs_pub!(ast_enum!($($t)*));
  };
}

macro_rules! define_operator_kind {
  (
    [$($attrs_pub:tt)*]
    enum $name:ident($kind_name:ident, $expect_name:expr) {$(
      $(#[$m:meta])* $variant:ident($inner:ty),
    )*}
  ) => {
    #[derive(Debug, Eq, PartialEq, Hash, Clone, From)]
    $($attrs_pub)* enum $name {
      $(
        $(#[$m])* $variant($inner),
      )*
    }

    #[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
    $($attrs_pub)* enum $kind_name {
      $(
        $(#[$m])* $variant,
      )*
    }

    impl $name {
      fn kind(&self) -> $kind_name {
        match self {
          $(
            $name::$variant(_) => $kind_name::$variant,
          )*
        }
      }
    }

    // impl Parse for $name {
    //   fn parse(input: ParseStream) -> Result<Self, ParseError> {
    //     $(
    //       if let Ok(t) = <$inner as Parse>::parse(input) {
    //         Ok(t.into())
    //       } else
    //     )* { Err(make_expected_op(stringify!($name), input.peek_token()?)) }
    //   }
    // }

    impl private::Sealed for $name {}
    impl Spanned for $name {
      fn span(&self) -> Span {
        match self {
          $(
            $name::$variant(t) => t.span(),
          )*
        }
      }
    }

    impl IntoToken for $name {
      fn into_token(self) -> std::result::Result<Token, ErrorToken> {
        match self {
          $(
            $name::$variant(t) => t.into_token(),
          )*
        }
      }
    }

    impl Tok for $name {
      const EOF: Option<bool> = Some(false);
      const NAME: &'static str = $expect_name;

      fn peek(cursor: Cursor) -> bool {
        $(
          <$inner as Tok>::peek(cursor) ||
        )* false
      }
    }
  };

  ($($t:tt)*) => {
    strip_attrs_pub!(define_operator_kind!($($t)*));
  };
}

pub(crate) trait SpanHelper {
  fn get_span(&self) -> Span;
}

impl<S: Spanned> SpanHelper for S {
  #[inline]
  fn get_span(&self) -> Span {
    <S as Spanned>::span(self)
  }
}

impl<S: Spanned> SpanHelper for Option<S> {
  #[inline]
  fn get_span(&self) -> Span {
    match self {
      None => Span::EMPTY,
      Some(s) => <S as Spanned>::span(s),
    }
  }
}

pub(crate) struct SpanBuilder {
  span: Span,
}

impl SpanBuilder {
  #[inline]
  pub(crate) const fn new() -> Self {
    Self { span: Span::EMPTY }
  }

  #[inline]
  pub(crate) fn add(mut self, spanned: &impl SpanHelper) -> Self {
    let first = self.span;
    let next = spanned.get_span();

    if first == Span::EMPTY {
      self.span = next;
    } else if first.file() == FileId::UNKNOWN && next.file() != FileId::UNKNOWN {
      self.span = next;
    } else {
      let start = cmp::min(first.start(), next.start());
      let end = cmp::max(first.end(), next.end());
      self.span = Span::new(next.file(), start, end);
    }

    self
  }
}

impl Into<Span> for SpanBuilder {
  #[inline]
  fn into(self) -> Span {
    self.span
  }
}

define_operator_kind! {
  pub enum UnaryOperator(UnaryOperatorKind, "unary operator") {
    /// !
    Not(Not),

    /// ~
    BitwiseNot(BitNeg),

    /// +
    Plus(Plus),

    /// -
    Minus(Minus),
  }
}

define_operator_kind! {
  pub enum BinaryOperator(BinaryOperatorKind, "binary operator") {
    /// *
    Mul(Mul),

    /// /
    Div(Div),

    /// %
    Mod(Mod),

    /// +
    Plus(Plus),

    /// -
    Minus(Minus),

    /// <<
    ShiftLeft(ShiftLeft),

    /// >>
    ShiftRight(ShiftRight),

    /// >
    GreaterThan(GreaterThan),

    /// >=
    GreaterThanOrEqual(GreaterThanOrEqual),

    /// <
    LessThan(LessThan),

    /// <=
    LessThanOrEqual(LessThanOrEqual),

    /// in
    In(In),

    /// ==
    Equal(Equal),

    /// !=
    NotEqual(NotEqual),

    /// &
    BitwiseAnd(BitAnd),

    /// ^
    BitwiseXor(BitXor),

    /// |
    BitwiseOr(BitOr),

    /// &&
    And(And),

    /// ||
    Or(Or),
  }
}

define_operator_kind! {
  pub enum IndexOperator(IndexOperatorKind, "index operator") {
    /// :
    Colon(Colon),

    /// ::
    DoubleColon(DoubleColon),
  }
}

// impl TryFrom<Operator> for BinaryOperator {
//   type Error = Operator;

//   fn try_from(value: Operator) -> Result<Self, Self::Error> {
//     match value {
//       Operator::Mul(t) => Ok(t.into()),
//       Operator::Div(t) => Ok(t.into()),
//       Operator::Mod(t) => Ok(t.into()),
//       Operator::Plus(t) => Ok(t.into()),
//       Operator::Minus(t) => Ok(t.into()),
//       Operator::ShiftLeft(t) => Ok(t.into()),
//       Operator::ShiftRight(t) => Ok(t.into()),
//       Operator::GreaterThan(t) => Ok(t.into()),
//       Operator::GreaterThanOrEqual(t) => Ok(t.into()),
//       Operator::LessThan(t) => Ok(t.into()),
//       Operator::LessThanOrEqual(t) => Ok(t.into()),
//       Operator::Equal(t) => Ok(t.into()),
//       Operator::NotEqual(t) => Ok(t.into()),
//       Operator::BitAnd(t) => Ok(t.into()),
//       Operator::BitXor(t) => Ok(t.into()),
//       Operator::BitOr(t) => Ok(t.into()),
//       Operator::And(t) => Ok(t.into()),
//       Operator::Or(t) => Ok(t.into()),
//       t => Err(t),
//     }
//   }
// }

// impl TryFrom<Keyword> for BinaryOperator {
//   type Error = Keyword;

//   fn try_from(value: Keyword) -> Result<Self, Self::Error> {
//     match value {
//       Keyword::In(t) => Ok(t.into()),
//       t => Err(t),
//     }
//   }
// }

// impl TryFrom<Token> for BinaryOperator {
//   type Error = Token;

//   fn try_from(value: Token) -> Result<Self, Self::Error> {
//     match value {
//       Token::Operator(Operator::Mul(t)) => Ok(t.into()),
//       Token::Operator(Operator::Div(t)) => Ok(t.into()),
//       Token::Operator(Operator::Mod(t)) => Ok(t.into()),
//       Token::Operator(Operator::Plus(t)) => Ok(t.into()),
//       Token::Operator(Operator::Minus(t)) => Ok(t.into()),
//       Token::Operator(Operator::ShiftLeft(t)) => Ok(t.into()),
//       Token::Operator(Operator::ShiftRight(t)) => Ok(t.into()),
//       Token::Operator(Operator::GreaterThan(t)) => Ok(t.into()),
//       Token::Operator(Operator::GreaterThanOrEqual(t)) => Ok(t.into()),
//       Token::Operator(Operator::LessThan(t)) => Ok(t.into()),
//       Token::Operator(Operator::LessThanOrEqual(t)) => Ok(t.into()),
//       Token::Keyword(Keyword::In(t)) => Ok(t.into()),
//       Token::Operator(Operator::Equal(t)) => Ok(t.into()),
//       Token::Operator(Operator::NotEqual(t)) => Ok(t.into()),
//       Token::Operator(Operator::BitAnd(t)) => Ok(t.into()),
//       Token::Operator(Operator::BitXor(t)) => Ok(t.into()),
//       Token::Operator(Operator::BitOr(t)) => Ok(t.into()),
//       Token::Operator(Operator::And(t)) => Ok(t.into()),
//       Token::Operator(Operator::Or(t)) => Ok(t.into()),
//       t => Err(t),
//     }
//   }
// }

ast_struct! {
  /// An error expressions: `error "foo"`.
  pub struct ExprError {
    pub error_token: Error,
    pub expr: Expr,
  }
}

ast_struct! {
  /// A string expressions: `"foo"`.
  pub struct ExprString {
    pub token: String,
  }
}

impl ExprString {
  #[inline]
  pub fn kind(&self) -> StringKind {
    self.token.kind()
  }
}

ast_struct! {
  /// An assert expression: `assert "foo" : "message" ; <rest>`.
  pub struct ExprAssert {
    pub assert_token: Assert,
    pub cond: Expr,
    pub col_token: Option<Colon>,
    pub msg: Option<Expr>,
    pub semi_colon_token: SemiColon,
    pub rest: Expr,
  }
}

ast_struct! {
  /// An if expression: `if "foo" then "bar" else "baz"`.
  pub struct ExprIf {
    pub if_token: If,
    pub cond: Expr,
    pub then_token: Then,
    pub if_true: Expr,
    pub else_token: Option<Else>,
    pub if_false: Option<Expr>,
  }
}

ast_struct! {
  /// A function expression: `function(x) x * x`.
  pub struct ExprFunction {
    pub function_token: Function,
    pub left_paren_token: LeftParen,
    pub params: Punctuated<Param, Comma>,
    pub right_paren_token: RightParen,
    pub body: Expr,
  }
}

ast_struct! {
  /// A function parameter: `x = "foo"`.
  pub struct Param {
    pub name: Ident,
    pub assign_token: Option<Assign>,
    pub default_arg: Option<Expr>,
  }
}

ast_struct! {
  /// A positional function argument: `"foo"`.
  pub struct ArgPositional {
    pub value: Expr,
  }
}

ast_struct! {
  /// A positional function argument: `x = "foo"`.
  pub struct ArgNamed {
    pub name: Ident,
    pub assign_token: Assign,
    pub value: Expr,
  }
}

ast_enum! {
  /// A function argument: `x = "foo"`.
  pub enum Argument {
    Positional(ArgPositional),
    Named(ArgNamed),
  }
}

ast_struct! {
  /// Object scoped assert: `assert "foo" : "bar"`.
  pub struct ObjectFieldAssert {
    pub assert_token: Assert,
    pub cond: Expr,
    pub col_token: Option<Colon>,
    pub msg: Option<Expr>,
  }
}

ast_struct! {
  /// Object id field: `foo: "bar"`.
  pub struct ObjectFieldIdent {
    pub name: Ident,
    pub colon_token: Colon, // TODO: This is likely long
    pub value: Expr,
  }
}

ast_struct! {
  /// Object computed field: `["foo"]: "bar"`.
  pub struct ObjectFieldComputed {
    pub name: Expr,
    pub colon_token: Colon, // TODO: This is likely long
    pub value: Expr,
  }
}

ast_struct! {
  /// Object computed field: `"foo": "bar"`.
  pub struct ObjectFieldString {
    pub name: String,
    pub colon_token: Colon, // TODO: This is likely long
    pub value: Expr,
  }
}

ast_struct! {
  /// Object scoped local: `local foo = "bar"`.
  pub struct ObjectFieldLocal {
    pub local_token: Local,
    pub name: Ident,
    pub assign_token: Assign,
    pub body: Expr,
  }
}

ast_enum! {
  pub enum ObjectField {
    Assert(ObjectFieldAssert),
    Ident(ObjectFieldIdent),
    Computed(ObjectFieldComputed),
    String(ObjectFieldString),
    Local(ObjectFieldLocal),
  }
}

ast_struct! {
  /// An import expression: `import "foo.libsonnet"`.
  pub struct ExprImport {
    pub import_token: Import,
    pub file: ExprString,
  }
}

ast_struct! {
  /// An importstr expression: `importstr "foo.txt"`.
  pub struct ExprImportStr {
    pub import_str_token: ImportStr,
    pub file: ExprString,
  }
}

ast_struct! {
  /// A local expression: `local foo = "bar"`.
  pub struct ExprLocal {
    pub local_token: Local,
    pub binds: Punctuated<Bind, Comma>,
    pub semi_colon_token: SemiColon,
    pub body: Expr,
  }
}

ast_struct! {
  /// A local value bind: `foo = "bar"`.
  pub struct BindValue {
    pub name: Ident,
    pub assign_token: Assign,
    pub body: Expr,
  }
}

ast_struct! {
  /// A local function bind: `foo(bar) = bar`.
  pub struct BindFunction {
    pub name: Ident,
    pub left_paren_token: LeftParen,
    pub params: Punctuated<Param, Comma>,
    pub right_paren_token: RightParen,
    pub assign_token: Assign,
    pub body: Expr,
  }
}

ast_enum! {
  /// A local bind.
  pub enum Bind {
    Value(BindValue),
    Function(BindFunction),
  }
}

ast_struct! {
  /// An unary expression: `-foo`.
  pub struct ExprUnary {
    pub operator: UnaryOperator,
    pub expr: Expr,
  }
}

ast_struct! {
  /// An index expression: `a[b]`.
  pub struct ExprIndex {
    pub target: Expr,
    pub left_bracket_token: LeftBracket,
    pub index: Expr,
    pub right_bracket_token: RightBracket,
  }
}

ast_struct! {
  /// An index expression: `a[b]`.
  pub struct ExprSlice {
    pub target: Expr,
    pub left_bracket_token: LeftBracket,
    pub begin_index: Option<Expr>,
    pub end_colon_token: Option<IndexOperator>,
    pub end_index: Option<Expr>,
    pub step_colon_token: Option<IndexOperator>,
    pub step: Option<Expr>,
    pub right_bracket_token: RightBracket,
  }
}

ast_struct! {
  /// A field access expression: `a.b`.
  pub struct ExprFieldAccess {
    pub target: Expr,
    pub field_name: Ident,
  }
}

ast_struct! {
  /// An apply expression: `a()`.
  pub struct ExprApply {
    pub target: Expr,
    pub left_paren_token: LeftParen,
    pub args: Punctuated<Argument, Comma>,
    pub right_paren_token: RightParen,
    pub tail_strict_token: Option<TailStrict>,
  }
}

ast_struct! {
  /// A object apply expression: `a { b: true }`.
  /// Desugared to `a + { b: true }`.
  pub struct ExprObjectApply {
    pub target: Expr,
    pub left_brace_token: LeftBrace,
    pub fields: Punctuated<ObjectField, Comma>,
    pub right_brace_token: RightBrace,
  }
}

ast_struct! {
  /// An "in-super" expression: `a in super`.
  pub struct ExprInSuper {
    pub target: Expr,
    pub in_token: In,
    pub super_token: Super,
  }
}

ast_struct! {
  /// A binary expression: `a + b`.
  pub struct ExprBinary {
    pub left: Expr,
    pub op: BinaryOperator,
    pub right: Expr,
  }
}

ast_enum! {
  /// An expression.
  pub enum Expr {
    Apply(ExprApply),
    Assert(ExprAssert),
    Binary(ExprBinary),
    Error(ExprError),
    FieldAccess(ExprFieldAccess),
    Function(ExprFunction),
    If(ExprIf),
    Import(ExprImport),
    ImportStr(ExprImportStr),
    Index(ExprIndex),
    InSuper(ExprInSuper),
    Local(ExprLocal),
    ObjectApply(ExprObjectApply),
    Slice(ExprSlice),
    String(ExprString),
    Unary(ExprUnary),
  }
}
