use crate::{
  ast::punctuated::Punctuated,
  lex::{
    error::ErrorToken,
    span::{FileId, Span},
    token,
    token::Token,
    IntoToken,
  },
  parse::{buffer::Cursor, error::Error as ParseError, lookahead::Peek, Parse, ParseStream},
};
use core::{
  cmp,
  convert::TryFrom,
  fmt,
  fmt::{Debug, Display},
};
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
  (@kind [$name:ident => $kind:ident] [$($attrs_pub:tt)*] {
    $($(#[$m:meta])* $variant:ident,)*
  }) => {
    #[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
    $($attrs_pub)* enum $kind {
      $(
        $(#[$m])* $variant,
      )*
    }

    impl $name {
      pub fn kind(&self) -> $kind {
        match self {
          $(
            $name::$variant(_) => $kind::$variant,
          )*
        }
      }
    }

    impl $kind {
      pub fn default_token(self) -> $name {
        match self {
          $(
            $kind::$variant => $name::$variant(Default::default()),
          )*
        }
      }
    }

    impl From<$name> for $kind {
      #[inline]
      fn from(value: $name) -> $kind {
        value.kind()
      }
    }
  };

  (@kind [$name:ident =>] $t1:tt $t2:tt) => {};

  (
    [$($attrs_pub:tt)*]
    enum $name:ident($($kind_name:ident,)? $expect_name:literal) {$(
      $(#[$m:meta])* $variant:ident($inner:ty),
    )*}
  ) => {
    #[derive(Eq, PartialEq, Hash, Clone, From)]
    $($attrs_pub)* enum $name {
      $(
        $(#[$m])* $variant($inner),
      )*
    }

    impl Parse for $name {
      fn parse(input: ParseStream) -> Result<Self, ParseError> {
        const EXPECTED: &'static [&'static str] = &[
          $(
            <$inner as Tok>::NAME,
          )*
        ];

        input.step(|cursor| {
          let cursor = *cursor;
          $(
            if let Some((t, c)) = cursor.token::<$inner>() {
              Some((Self::from(t), c))
            } else
          )* {
            None
          }.ok_or_else(|| ParseError::expected_tokens(cursor.span(), EXPECTED))
        })
      }
    }

    impl Peek for $name {
      type Token = Self;
    }

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

    impl Debug for $name {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            $name::$variant(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    impl Display for $name {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            $name::$variant(t) => Display::fmt(t, f),
          )*
        }
      }
    }

    impl Tok for $name {
      const NAME: &'static str = $expect_name;

      fn peek(cursor: Cursor) -> bool {
        $(
          <$inner as Tok>::peek(cursor) ||
        )* false
      }
    }

    define_operator_kind!(@kind [$name => $($kind_name)?] [$($attrs_pub)*] {
      $(
        $(#[$m])* $variant,
      )*
    });
  };

  ($($t:tt)*) => {
    strip_attrs_pub!(define_operator_kind!($($t)*));
  };
}

pub(crate) trait SpanBuilderHelper {
  fn add_to(&self, builder: SpanBuilder) -> SpanBuilder;
}

impl<S: Spanned> SpanBuilderHelper for S {
  #[inline]
  fn add_to(&self, builder: SpanBuilder) -> SpanBuilder {
    builder.add_span(self.span())
  }
}

impl<S: SpanBuilderHelper> SpanBuilderHelper for Option<S> {
  #[inline]
  fn add_to(&self, builder: SpanBuilder) -> SpanBuilder {
    match self {
      None => builder,
      Some(s) => s.add_to(builder),
    }
  }
}

impl<S: SpanBuilderHelper> SpanBuilderHelper for Vec<S> {
  #[inline]
  fn add_to(&self, builder: SpanBuilder) -> SpanBuilder {
    self.iter().fold(builder, SpanBuilder::add)
  }
}

impl<S1: SpanBuilderHelper, S2: SpanBuilderHelper> SpanBuilderHelper for (S1, S2) {
  #[inline]
  fn add_to(&self, mut builder: SpanBuilder) -> SpanBuilder {
    builder = self.0.add_to(builder);
    self.1.add_to(builder)
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
  fn add_span(mut self, span: Span) -> Self {
    let first = self.span;
    let next = span;

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

  #[inline]
  pub(crate) fn add(self, spanned: &impl SpanBuilderHelper) -> Self {
    spanned.add_to(self)
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
  pub enum BinaryOperator("binary operator") {
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
  pub enum IndexOperator("index operator") {
    /// :
    Colon(Colon),

    /// ::
    DoubleColon(DoubleColon),
  }
}

define_operator_kind! {
  pub enum ObjectFieldOperator(ObjectFieldOperatorKind, "object field operator") {
    /// `:`
    Default(Colon),

    /// `::`
    Hidden(DoubleColon),

    /// `:::`
    Public(TripleColon),

    /// `+:`
    Merge(PlusColon),

    /// `+::`
    MergeHidden(PlusDoubleColon),

    /// `+:::`
    MergePublic(PlusTripleColon),
  }
}

define_operator_kind! {
  pub enum ObjectFieldFunctionOperator("object field function operator") {
    /// `:`
    Default(Colon),

    /// `::`
    Hidden(DoubleColon),

    /// `:::`
    Public(TripleColon),
  }
}

ast_struct! {
  /// An error expressions: `error "foo"`.
  pub struct ExprError {
    pub error_token: Error,
    pub expr: Expr,
  }
}

ast_struct! {
  /// A string expressions: `"foo"`.
  #[derive(From)]
  pub struct ExprString {
    pub value: String,
  }
}

impl ExprString {
  #[inline]
  pub fn kind(&self) -> StringKind {
    self.value.kind()
  }
}

ast_struct! {
  /// An assert expression: `assert "foo" : "message" ; <rest>`.
  pub struct ExprAssert {
    pub assert_token: Assert,
    pub cond: Expr,
    pub msg: Option<(Colon, Expr)>,
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
    pub if_false: Option<(Else, Expr)>,
  }
}

ast_struct! {
  /// A function expression: `function(x) x * x`.
  pub struct ExprFunction {
    pub function_token: Function,
    pub left_paren_token: ParenL,
    pub params: Punctuated<Param, Comma>,
    pub right_paren_token: ParenR,
    pub body: Expr,
  }
}

ast_struct! {
  /// A function parameter: `x = "foo"`.
  pub struct Param {
    pub name: Ident,
    pub default_value: Option<(Assign, Expr)>,
  }
}

ast_struct! {
  /// A positional function argument: `"foo"`.
  #[derive(From)]
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

impl Argument {
  fn value(&self) -> &Expr {
    match self {
      Self::Positional(a) => &a.value,
      Self::Named(a) => &a.value,
    }
  }

  fn name(&self) -> Option<&Ident> {
    match self {
      Self::Positional(_) => None,
      Self::Named(a) => Some(&a.name),
    }
  }

  fn is_named(&self) -> bool {
    match self {
      Self::Named(_) => true,
      Self::Positional(_) => false,
    }
  }
}

ast_struct! {
  /// Object scoped assert: `assert "foo" : "bar"`.
  pub struct ObjectFieldAssert {
    pub assert_token: Assert,
    pub cond: Expr,
    pub msg: Option<(Colon, Expr)>,
  }
}

ast_struct! {
  /// Object ident field name: `foo`.
  #[derive(From)]
  pub struct FieldNameIdent {
    pub name: Ident,
  }
}

ast_struct! {
  /// Object ident field name: `"foo"`.
  #[derive(From)]
  pub struct FieldNameString {
    pub name: String,
  }
}

ast_struct! {
  /// Object ident field name: `["foo"]`.
  #[derive(From)]
  pub struct FieldNameComputed {
    pub left_bracket_token: BracketL,
    pub name: Expr,
    pub right_bracket_token: BracketR,
  }
}

ast_enum! {
  /// Object field name.
  pub enum ObjectFieldName {
    Ident(FieldNameIdent),
    String(FieldNameString),
    Computed(FieldNameComputed),
  }
}

ast_struct! {
  /// Object id field: `foo: "bar"`.
  pub struct ObjectFieldValue {
    pub name: ObjectFieldName,
    pub op: ObjectFieldOperator,
    pub value: Expr,
  }
}

ast_struct! {
  /// Object id field: `foo(): "bar"`.
  pub struct ObjectFieldFunction {
    pub name: ObjectFieldName,
    pub left_paren_token: ParenL,
    pub params: Punctuated<Param, Comma>,
    pub right_paren_token: ParenR,
    pub op: ObjectFieldFunctionOperator,
    pub value: Expr,
  }
}

ast_struct! {
  /// Object scoped local: `local foo = "bar"`.
  pub struct ObjectFieldLocal {
    pub local_token: Local,
    pub bind: Bind,
  }
}

ast_enum! {
  pub enum ObjectField {
    Assert(ObjectFieldAssert),
    Function(ObjectFieldFunction),
    Local(ObjectFieldLocal),
    Value(ObjectFieldValue),
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
    pub left_paren_token: ParenL,
    pub params: Punctuated<Param, Comma>,
    pub right_paren_token: ParenR,
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
    pub op: UnaryOperator,
    pub expr: Expr,
  }
}

ast_struct! {
  /// An slice expression: `a[b:c]`.
  pub struct ExprSlice {
    pub target: Expr,
    pub left_bracket_token: BracketL,
    pub begin_index: Option<Expr>,
    pub end_op: Option<IndexOperator>,
    pub end_index: Option<Expr>,
    pub step_op: Option<IndexOperator>,
    pub step: Option<Expr>,
    pub right_bracket_token: BracketR,
  }
}

ast_struct! {
  /// A field access expression: `a.b`.
  pub struct ExprFieldAccess {
    pub target: Expr,
    pub dot_token: Dot,
    pub field_name: Ident,
  }
}

ast_struct! {
  /// A computed field access expression: `a['b']`.
  pub struct ExprComputedFieldAccess {
    pub target: Expr,
    pub left_bracket_token: BracketL,
    pub expr: Expr,
    pub right_bracket_token: BracketR,
  }
}

ast_struct! {
  /// An apply expression: `a()`.
  pub struct ExprApply {
    pub target: Expr,
    pub left_paren_token: ParenL,
    pub args: Punctuated<Argument, Comma>,
    pub right_paren_token: ParenR,
    pub tail_strict_token: Option<TailStrict>,
  }
}

ast_struct! {
  /// A object apply expression: `a { b: true }`.
  /// Desugared to `a + { b: true }`.
  pub struct ExprObjectApply {
    pub target: Expr,
    pub object: ObjectOrObjectComp,
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
    pub lhs: Expr,
    pub op: BinaryOperator,
    pub rhs: Expr,
  }
}

ast_struct! {
  /// A grouped expression: `(x)`.
  pub struct ExprGroup {
    pub left_paren_token: ParenL,
    pub expr: Expr,
    pub right_paren_token: ParenR,
  }
}

impl ExprGroup {
  fn new(expr: impl Into<Expr>) -> Self {
    Self {
      left_paren_token: Default::default(),
      expr: expr.into(),
      right_paren_token: Default::default(),
    }
  }
}

ast_struct! {
  /// The `null` literal.
  #[derive(Default, From)]
  pub struct ExprNull {
    pub null_token: Null,
  }
}

ast_struct! {
  /// The `true` literal.
  #[derive(Default, From)]
  pub struct ExprTrue {
    pub true_token: True,
  }
}

ast_struct! {
  /// The `false` literal.
  #[derive(Default, From)]
  pub struct ExprFalse {
    pub false_token: False,
  }
}

ast_struct! {
  /// The `self` expression.
  #[derive(Default, From)]
  pub struct ExprSelf {
    pub self_token: SelfValue,
  }
}

ast_struct! {
  /// The `$` expression.
  #[derive(Default, From)]
  pub struct ExprRoot {
    pub dollar_token: Dollar,
  }
}

ast_struct! {
  /// A number literal expression: `5`.
  #[derive(From)]
  pub struct ExprNumber {
    pub value: Number,
  }
}

ast_struct! {
  /// A ident expression: `x`.
  #[derive(From)]
  pub struct ExprIdent {
    pub name: Ident,
  }
}

ast_struct! {
  /// An super field lookup: `super.x`.
  pub struct SuperField {
    pub super_token: Super,
    pub dot_token: Dot,
    pub field_name: Ident,
  }
}

ast_struct! {
  /// A computed super field lookup: `super['x']`.
  pub struct SuperComputed {
    pub super_token: Super,
    pub left_bracket_token: BracketL,
    pub field: Expr,
    pub right_bracket_token: BracketR,
  }
}

ast_enum! {
  /// A super lookup.
  pub enum ExprSuper {
    Field(SuperField),
    Computed(SuperComputed),
  }
}

ast_struct! {
  /// An array expression: `[1, 2, 3,]`.
  pub struct ExprArray {
    pub left_bracket_token: BracketL,
    pub items: Punctuated<Expr, Comma>,
    pub right_bracket_token: BracketR,
  }
}

ast_struct! {
  /// An array expression: `[x for x in y]`.
  pub struct ForSpec {
    pub for_token: For,
    pub id: Ident,
    pub in_token: In,
    pub expr: Expr,
  }
}

ast_struct! {
  /// An array expression: `[x for x in y]`.
  pub struct IfSpec {
    pub if_token: If,
    pub expr: Expr,
  }
}

ast_enum! {
  /// The tail of a list comprehension.
  pub enum CompSpec {
    For(ForSpec),
    If(IfSpec),
  }
}

ast_struct! {
  /// An array expression: `[x for x in y]`.
  pub struct ExprArrayComp {
    pub left_bracket_token: BracketL,
    pub expr: Expr,
    pub comma_token: Option<Comma>,
    pub for_spec: ForSpec,
    pub tail_spec: Vec<CompSpec>,
    pub right_bracket_token: BracketR,
  }
}

ast_struct! {
  /// An object expression: `{ x: y, [y]: z }`.
  pub struct ExprObject {
    pub left_brace_token: BraceL,
    pub fields: Punctuated<ObjectField, Comma>,
    pub right_brace_token: BraceR,
  }
}

ast_struct! {
  /// An object expression: `{ x: y, [y]: z }`.
  pub struct ExprObjectComp {
    pub left_brace_token: BraceL,
    pub before_field_locals: Vec<(ObjectFieldLocal, Comma)>,
    pub field: ObjectCompField,
    pub after_field_locals: Option<(Comma, Punctuated<ObjectFieldLocal, Comma>)>,
    pub for_spec: ForSpec,
    pub tail_spec: Vec<CompSpec>,
    pub right_brace_token: BraceR,
  }
}

ast_struct! {
  /// Object comprehension computed field: `["foo"]: "bar"`.
  pub struct ObjectCompField {
    pub left_bracket_token: BracketL,
    pub field: Expr,
    pub right_bracket_token: BracketR,
    pub colon_token: Colon,
    pub value: Expr,
  }
}

impl TryFrom<ObjectFieldValue> for ObjectCompField {
  type Error = ParseError;

  fn try_from(value: ObjectFieldValue) -> Result<Self, Self::Error> {
    define_error! {
      /// object comprehentions required computed field names
      struct CompFieldRequired;
    }

    let colon_token = match value.op {
      ObjectFieldOperator::Default(c) => c,
      //ObjectFieldOperator::PlusColon(c) => c.into(),
      op => return Err(ParseError::expected_token(op.span(), Colon::NAME)),
    };

    let (left_bracket_token, field, right_bracket_token) = match value.name {
      ObjectFieldName::Computed(f) => (f.left_bracket_token, f.name, f.right_bracket_token),
      f => return Err(ParseError::new(CompFieldRequired::new(f.span()))),
    };

    Ok(ObjectCompField {
      left_bracket_token,
      field,
      right_bracket_token,
      colon_token,
      value: value.value,
    })
  }
}

ast_enum! {
  pub enum ObjectOrObjectComp {
    Object(ExprObject),
    ObjectComp(ExprObjectComp),
  }
}

impl From<ObjectOrObjectComp> for Expr {
  fn from(obj: ObjectOrObjectComp) -> Self {
    match obj {
      ObjectOrObjectComp::Object(o) => o.into(),
      ObjectOrObjectComp::ObjectComp(o) => o.into(),
    }
  }
}

ast_enum! {
  /// An expression.
  pub enum Expr {
    Apply(ExprApply),
    Array(ExprArray),
    ArrayComp(ExprArrayComp),
    Assert(ExprAssert),
    Binary(ExprBinary),
    ComputedFieldAccess(ExprComputedFieldAccess),
    Error(ExprError),
    False(ExprFalse),
    FieldAccess(ExprFieldAccess),
    Function(ExprFunction),
    Group(ExprGroup),
    Ident(ExprIdent),
    If(ExprIf),
    Import(ExprImport),
    ImportStr(ExprImportStr),
    InSuper(ExprInSuper),
    Local(ExprLocal),
    Null(ExprNull),
    Number(ExprNumber),
    Object(ExprObject),
    ObjectApply(ExprObjectApply),
    ObjectComp(ExprObjectComp),
    Root(ExprRoot),
    SelfValue(ExprSelf),
    Slice(ExprSlice),
    String(ExprString),
    Super(ExprSuper),
    True(ExprTrue),
    Unary(ExprUnary),
  }
}

mod parsing {
  use super::*;
  use crate::parse::{
    buffer,
    buffer::{Braces, Brackets, Delimiter, Parentheses},
    error::Result,
    ParseBuffer,
  };

  #[derive(Copy, Clone, PartialEq, PartialOrd)]
  enum Precedence {
    Any,
    // Application,
    // Unary,
    Term,
    Arithmetic,
    Shift,
    Compare,
    Equals,
    BitAnd,
    BitXor,
    BitOr,
    And,
    Or,
  }

  impl Precedence {
    fn of(op: &BinaryOperator) -> Self {
      match op {
        BinaryOperator::Mul(_) | BinaryOperator::Div(_) | BinaryOperator::Mod(_) => Self::Term,
        BinaryOperator::Plus(_) | BinaryOperator::Minus(_) => Self::Arithmetic,
        BinaryOperator::ShiftLeft(_) | BinaryOperator::ShiftRight(_) => Self::Shift,
        BinaryOperator::GreaterThan(_)
        | BinaryOperator::GreaterThanOrEqual(_)
        | BinaryOperator::LessThan(_)
        | BinaryOperator::LessThanOrEqual(_)
        | BinaryOperator::In(_) => Self::Compare,
        BinaryOperator::Equal(_) | BinaryOperator::NotEqual(_) => Self::Equals,
        BinaryOperator::BitwiseAnd(_) => Self::BitAnd,
        BinaryOperator::BitwiseXor(_) => Self::BitXor,
        BinaryOperator::BitwiseOr(_) => Self::BitOr,
        BinaryOperator::And(_) => Self::And,
        BinaryOperator::Or(_) => Self::Or,
      }
    }
  }

  fn parse_delimited<'a, D: Delimiter>(
    input: &ParseBuffer<'a>,
    delimiter: D,
  ) -> Result<(D::OpenToken, D::CloseToken, ParseBuffer<'a>)> {
    input.step(|cursor| {
      if let Some((content, open_token, close_token, rest)) = cursor.group(delimiter) {
        let scope = buffer::close_span_of_group(*cursor);
        let nested = crate::parse::advance_step_cursor(cursor, content);
        let unexpected = crate::parse::get_unexpected(input);
        let content = crate::parse::new_parse_buffer(scope, nested, unexpected);
        Ok(((open_token, close_token, content), rest))
      } else {
        Err(ParseError::expected_token(cursor.span(), D::NAME))
      }
    })
  }

  // prevents parsers from directly accessing the fields
  mod group {
    use super::*;

    pub(crate) struct Group<'a, D: Delimiter> {
      open_token: D::OpenToken,
      close_token: D::CloseToken,
      pub(crate) content: ParseBuffer<'a>,
    }

    impl<'a, D: Delimiter> Group<'a, D> {
      #[inline]
      pub(crate) fn open(&self) -> D::OpenToken {
        self.open_token
      }

      pub(crate) fn close(self) -> Result<D::CloseToken> {
        if !self.content.is_empty() {
          Err(ParseError::unexpected_token(self.content.span()))
        } else {
          Ok(self.close_token)
        }
      }

      pub(crate) fn full_span(&self) -> Span {
        self.open_token.span() + self.close_token.span()
      }

      pub(crate) fn new(
        (open_token, close_token, content): (D::OpenToken, D::CloseToken, ParseBuffer<'a>),
      ) -> Self {
        Group {
          open_token,
          close_token,
          content,
        }
      }
    }
  }

  use group::Group;

  fn parse_parens<'a>(input: &ParseBuffer<'a>) -> Result<Group<'a, Parentheses>> {
    parse_delimited(input, Parentheses).map(Group::new)
  }

  fn parse_braces<'a>(input: &ParseBuffer<'a>) -> Result<Group<'a, Braces>> {
    parse_delimited(input, Braces).map(Group::new)
  }

  fn parse_brackets<'a>(input: &ParseBuffer<'a>) -> Result<Group<'a, Brackets>> {
    parse_delimited(input, Brackets).map(Group::new)
  }

  macro_rules! parentheses {
    ($input:ident => $group:ident) => {{
      $group = parse_parens($input)?;
      $group.open()
    }};
  }

  macro_rules! braces {
    ($input:ident => $group:ident) => {{
      $group = parse_braces($input)?;
      $group.open()
    }};
  }

  macro_rules! brackets {
    ($input:ident => $group:ident) => {{
      $group = parse_brackets($input)?;
      $group.open()
    }};
  }

  fn peek_precedence(input: ParseStream) -> Precedence {
    input
      .fork()
      .parse::<BinaryOperator>()
      .map_or(Precedence::Any, |op| Precedence::of(&op))
  }

  fn parse_expr_bp(input: ParseStream, mut lhs: Expr, base: Precedence) -> Result<Expr> {
    loop {
      if input
        .fork()
        .parse::<BinaryOperator>()
        .ok()
        .map_or(false, |op| Precedence::of(&op) >= base)
      {
        let op: BinaryOperator = input.parse()?;
        let precedence = Precedence::of(&op);
        let mut rhs = parse_expr_unary(input)?;
        loop {
          let next = peek_precedence(input);
          if next > precedence {
            rhs = parse_expr_bp(input, rhs, next)?;
          } else {
            break;
          }
        }

        lhs = ExprBinary { lhs, op, rhs }.into()
      } else {
        break;
      }
    }

    Ok(lhs)
  }

  // assert <expr>
  // error <expr>
  // function(x) <expr>
  // if x then expr
  // import "foo"
  // importstr "bar"
  // local foo = <expr>; <expr>
  // +/-/!/~foo
  fn parse_expr_unary(input: ParseStream) -> Result<Expr> {
    if input.peek::<Assert>() {
      ExprAssert::parse(input).map(Expr::from)
    } else if input.peek::<Error>() {
      ExprError::parse(input).map(Expr::from)
    } else if input.peek::<Function>() {
      ExprFunction::parse(input).map(Expr::from)
    } else if input.peek::<If>() {
      ExprIf::parse(input).map(Expr::from)
    } else if input.peek::<Import>() {
      ExprImport::parse(input).map(Expr::from)
    } else if input.peek::<ImportStr>() {
      ExprImportStr::parse(input).map(Expr::from)
    } else if input.peek::<Local>() {
      ExprLocal::parse(input).map(Expr::from)
    } else if input.peek::<Minus>()
      || input.peek::<Plus>()
      || input.peek::<Not>()
      || input.peek::<BitNeg>()
    {
      ExprUnary::parse(input).map(Expr::from)
    } else {
      trailer_expr(input)
    }
  }

  // <atom> (..<args>) ...
  // <atom> . <ident> (..<args>) ...
  // <atom> . <ident> ...
  // <atom> [ <expr> ] ...
  fn trailer_expr(input: ParseStream) -> Result<Expr> {
    if input.peek::<Parentheses>() {
      return ExprGroup::parse(input).map(Expr::from);
    }

    let atom = atom_expr(input)?;
    trailer_helper(input, atom)
  }

  fn trailer_helper(input: ParseStream, mut e: Expr) -> Result<Expr> {
    loop {
      if input.peek::<Parentheses>() {
        let group;
        e = ExprApply {
          target: e,
          left_paren_token: parentheses!(input => group),
          args: validate_args(group.content.parse_terminated(Argument::parse)?)?,
          right_paren_token: group.close()?,
          tail_strict_token: input.parse()?,
        }
        .into()
      } else if input.peek::<Dot>() {
        e = ExprFieldAccess {
          target: e,
          dot_token: input.parse()?,
          field_name: input.parse()?,
        }
        .into()
      } else if input.peek::<Brackets>() {
        e = parse_expr_member_or_slice(input, e)?
      } else if input.peek::<Braces>() {
        e = ExprObjectApply {
          target: e,
          object: input.parse()?,
        }
        .into()
      } else if input.peek::<In>() && input.peek2::<Super>() {
        e = ExprInSuper {
          target: e,
          in_token: input.parse()?,
          super_token: input.parse()?,
        }
        .into()
      } else {
        break;
      }
    }

    Ok(e)
  }

  fn atom_expr(input: ParseStream) -> Result<Expr> {
    if input.peek::<Parentheses>() {
      ExprGroup::parse(input).map(Expr::from)
    } else if input.peek::<Null>() {
      ExprNull::parse(input).map(Expr::from)
    } else if input.peek::<True>() {
      ExprTrue::parse(input).map(Expr::from)
    } else if input.peek::<False>() {
      ExprFalse::parse(input).map(Expr::from)
    } else if input.peek::<SelfValue>() {
      ExprSelf::parse(input).map(Expr::from)
    } else if input.peek::<Dollar>() {
      ExprRoot::parse(input).map(Expr::from)
    } else if input.peek::<String>() {
      ExprString::parse(input).map(Expr::from)
    } else if input.peek::<Number>() {
      ExprNumber::parse(input).map(Expr::from)
    } else if input.peek::<Ident>() {
      ExprIdent::parse(input).map(Expr::from)
    } else if input.peek::<Braces>() {
      parse_obj_remainder(input).map(Expr::from)
    } else if input.peek::<Brackets>() {
      parse_array_or_comp(input)
    } else if input.peek::<Super>() {
      ExprSuper::parse(input).map(Expr::from)
    } else {
      Err(ParseError::expected_token(input.span(), "expression"))
    }
  }

  fn parse_obj_remainder_comp(
    group: Group<Braces>,
    fields: Punctuated<ObjectField, Comma>,
  ) -> Result<ExprObjectComp> {
    define_error! {
      /// only computed and local fields are allowed in object comprehensions
      struct IllegalFieldType;
    }

    define_error! {
      /// object comprehension can only have one field
      struct TooManyFields;
    }

    define_error! {
      /// object comprehension require a single computed field
      struct NoField;
    }

    let input = &group.content;
    let mut before_field_locals = Vec::new();
    let mut after_field_locals = Punctuated::new();

    let mut comp_field = None;
    let mut comma_token = None;
    let mut pairs = fields.into_pairs().map(|p| p.into_tuple());
    while let Some((field, punct)) = pairs.next() {
      match field {
        ObjectField::Local(f) => {
          if let Some(punct) = punct {
            before_field_locals.push((*f, punct));
          } else {
            return Err(ParseError::expected_token(input.span(), Comma::NAME));
          }
        }

        ObjectField::Value(f) => {
          comp_field = Some(ObjectCompField::try_from(*f)?);
          comma_token = punct;
          break;
        }

        f => {
          return Err(ParseError::new(IllegalFieldType::new(f.span())));
        }
      }
    }

    let comp_field = if let Some(f) = comp_field {
      f
    } else {
      return Err(ParseError::new(NoField::new(input.span())));
    };

    while let Some((field, punct)) = pairs.next() {
      match field {
        ObjectField::Local(f) => {
          after_field_locals.push_value(*f);
          if let Some(punct) = punct {
            after_field_locals.push_punct(punct);
          }
        }

        ObjectField::Value(f) => {
          return Err(ParseError::new(TooManyFields::new(f.span())));
        }

        f => {
          return Err(ParseError::new(IllegalFieldType::new(f.span())));
        }
      }
    }

    debug_assert!(after_field_locals.is_empty() || comma_token.is_some());
    Ok(ExprObjectComp {
      left_brace_token: group.open(),
      before_field_locals,
      field: comp_field,
      after_field_locals: comma_token.map(|c| (c, after_field_locals)),
      for_spec: input.parse()?,
      tail_spec: {
        let mut spec = Vec::new();
        while !input.is_empty() {
          if input.peek::<For>() || input.peek::<If>() {
            spec.push(input.parse()?);
          } else if !input.is_empty() {
            return Err(ParseError::unexpected_token(input.span()));
          }
        }

        spec
      },
      right_brace_token: group.close()?,
    })
  }

  fn parse_obj_remainder(input: ParseStream) -> Result<ObjectOrObjectComp> {
    let group = parse_braces(input)?;
    let mut fields = Punctuated::new();
    let inner = &group.content;

    while !inner.is_empty() {
      if inner.peek::<For>() {
        // It's a comprehension
        return parse_obj_remainder_comp(group, fields).map(ObjectOrObjectComp::from);
      }

      if !fields.empty_or_trailing() {
        return Err(ParseError::expected_token(inner.span(), Comma::NAME));
      }

      if inner.peek::<Brackets>() || inner.peek::<String>() || inner.peek::<Ident>() {
        let name = ObjectFieldName::parse(inner)?;
        if inner.peek::<Parentheses>() {
          let paren_group;
          fields.push(
            ObjectFieldFunction {
              name,
              left_paren_token: parentheses!(inner => paren_group),
              params: paren_group.content.parse_terminated(Param::parse)?,
              right_paren_token: paren_group.close()?,
              op: inner.parse()?,
              value: inner.parse()?,
            }
            .into(),
          )
        } else if inner.peek::<ObjectFieldOperator>() {
          fields.push(
            ObjectFieldValue {
              name,
              op: inner.parse()?,
              value: inner.parse()?,
            }
            .into(),
          )
        } else {
          return Err(ParseError::expected_token2(
            inner.span(),
            ObjectFieldOperator::NAME,
            Parentheses::NAME,
          ));
        }
      } else if inner.peek::<Local>() {
        fields.push(ObjectFieldLocal::parse(inner)?.into());
      } else if inner.peek::<Assert>() {
        fields.push(ObjectFieldAssert::parse(inner)?.into());
      } else {
        return Err(ParseError::expected_token(inner.span(), "field definition"));
      }

      if inner.peek::<Comma>() {
        fields.push_punct(inner.parse()?);
      }
    }

    Ok(
      ExprObject {
        left_brace_token: group.open(),
        fields,
        right_brace_token: group.close()?,
      }
      .into(),
    )
  }

  // expr[member]
  // expr[:]
  // expr[::]
  // expr[from:]
  // expr[from::]
  // expr[from::step]
  // expr[:to]
  // expr[:to:]
  // expr[from:to]
  // expr[from:to:]
  // expr[from:to:step]
  // expr[:to:step]
  // expr[::step]
  fn parse_expr_member_or_slice(input: ParseStream, lhs: Expr) -> Result<Expr> {
    define_error! {
      /// invalid slice: too many colons
      struct TooManyColons;
    }

    define_error! {
      /// expression or slice indecies required
      struct EmptySlice;
    }

    let group = parse_brackets(input)?;
    let input = &group.content;
    let mut fields = [None, None, None];
    let mut pre_fields = [None, None];
    let mut index = 0;
    let mut ready_for_expr = true;

    while index < 3 {
      if input.is_empty() {
        break;
      }

      if input.peek::<Colon>() {
        if index > 1 {
          return Err(ParseError::new(TooManyColons::new(input.span())));
        }

        let colon = Colon::parse(input)?;
        pre_fields[index] = Some(IndexOperator::from(colon));
        index += 1;
        ready_for_expr = true;
      } else if input.peek::<DoubleColon>() {
        if index > 0 {
          return Err(ParseError::new(TooManyColons::new(input.span())));
        }

        let colon = DoubleColon::parse(input)?;
        pre_fields[1] = Some(IndexOperator::from(colon));
        index += 2;
        ready_for_expr = true;
      } else if ready_for_expr {
        fields[index] = Some(Expr::parse(input)?);
        ready_for_expr = false;
      } else {
        return Err(match index {
          1 => ParseError::expected_token2(input.span(), Colon::NAME, BracketR::NAME),
          _ => ParseError::expected_token(input.span(), BracketR::NAME),
        });
      }
    }

    if index == 0 {
      if let Some(member) = fields[0].take() {
        return Ok(
          ExprComputedFieldAccess {
            target: lhs,
            left_bracket_token: group.open(),
            expr: member,
            right_bracket_token: group.close()?,
          }
          .into(),
        );
      } else {
        return Err(ParseError::new(EmptySlice::new(group.full_span())));
      }
    }

    Ok(
      ExprSlice {
        target: lhs,
        left_bracket_token: group.open(),
        begin_index: fields[0].take(),
        end_op: pre_fields[0].take(),
        end_index: fields[1].take(),
        step_op: pre_fields[1].take(),
        step: fields[2].take(),
        right_bracket_token: group.close()?,
      }
      .into(),
    )
  }

  fn parse_array_or_comp(input: ParseStream) -> Result<Expr> {
    let group = parse_brackets(input)?;

    if group.content.is_empty() {
      return Ok(
        ExprArray {
          left_bracket_token: group.open(),
          items: Punctuated::new(),
          right_bracket_token: group.close()?,
        }
        .into(),
      );
    }

    let expr: Expr = group.content.parse()?;
    if group.content.peek::<For>() || group.content.peek::<Comma>() && group.content.peek2::<For>()
    {
      parse_array_comp_rest(group, expr).map(Expr::from)
    } else {
      parse_array_rest(group, expr).map(Expr::from)
    }
  }

  fn parse_array_comp_rest(group: Group<Brackets>, expr: Expr) -> Result<ExprArrayComp> {
    Ok(ExprArrayComp {
      left_bracket_token: group.open(),
      expr,
      comma_token: group.content.parse()?,
      for_spec: group.content.parse()?,
      tail_spec: {
        let mut spec = Vec::new();
        while !group.content.is_empty() {
          if group.content.peek::<For>() || group.content.peek::<If>() {
            spec.push(group.content.parse()?);
          } else if !group.content.is_empty() {
            return Err(ParseError::unexpected_token(group.content.span()));
          }
        }

        spec
      },
      right_bracket_token: group.close()?,
    })
  }

  fn parse_array_rest(group: Group<Brackets>, expr: Expr) -> Result<ExprArray> {
    let mut items = Punctuated::new();
    items.push(expr);

    Ok(ExprArray {
      left_bracket_token: group.open(),
      items: Punctuated::parse_terminated_cont(&group.content, items)?,
      right_bracket_token: group.close()?,
    })
  }

  fn validate_args(args: Punctuated<Argument, Comma>) -> Result<Punctuated<Argument, Comma>> {
    define_error! {
      /// positional argument after named arguments
      struct PositionalAfterNamedArg;
    }

    let mut named_arg = false;
    for arg in args.iter() {
      if arg.is_named() {
        named_arg = true;
      } else if named_arg {
        return Err(ParseError::new(PositionalAfterNamedArg::new(arg.span())));
      }
    }

    Ok(args)
  }

  macro_rules! impl_single_token_parse {
    ($ty:ident, $fld:ident) => {
      impl Parse for $ty {
        #[inline]
        fn parse(input: ParseStream) -> Result<Self> {
          Ok(Self {
            $fld: input.parse()?,
          })
        }
      }
    };
  }

  impl_single_token_parse!(ExprNull, null_token);
  impl_single_token_parse!(ExprTrue, true_token);
  impl_single_token_parse!(ExprFalse, false_token);
  impl_single_token_parse!(ExprSelf, self_token);
  impl_single_token_parse!(ExprRoot, dollar_token);
  impl_single_token_parse!(ExprString, value);
  impl_single_token_parse!(ExprNumber, value);
  impl_single_token_parse!(ExprIdent, name);
  impl_single_token_parse!(ArgPositional, value);

  impl Parse for Expr {
    #[inline]
    fn parse(input: ParseStream) -> Result<Self> {
      let lhs = parse_expr_unary(input)?;
      parse_expr_bp(input, lhs, Precedence::Any)
    }
  }

  impl Parse for ObjectOrObjectComp {
    fn parse(input: ParseStream) -> Result<Self> {
      parse_obj_remainder(input)
    }
  }

  impl Parse for ExprGroup {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(ExprGroup {
        left_paren_token: parentheses!(input => group),
        expr: group.content.parse()?,
        right_paren_token: group.close()?,
      })
    }
  }

  impl Parse for Param {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(Param {
        name: input.parse()?,
        default_value: {
          if input.peek::<Assign>() {
            let assign_token: Assign = input.parse()?;
            let default_value: Expr = input.parse()?;
            Some((assign_token, default_value))
          } else {
            None
          }
        },
      })
    }
  }

  impl Parse for Argument {
    fn parse(input: ParseStream) -> Result<Self> {
      if input.peek::<Ident>() && input.peek2::<Assign>() {
        ArgNamed::parse(input).map(Argument::from)
      } else {
        ArgPositional::parse(input).map(Argument::from)
      }
    }
  }

  impl Parse for ArgNamed {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ArgNamed {
        name: input.parse()?,
        assign_token: input.parse()?,
        value: input.parse()?,
      })
    }
  }

  impl Parse for IfSpec {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(IfSpec {
        if_token: input.parse()?,
        expr: input.parse()?,
      })
    }
  }

  impl Parse for ForSpec {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ForSpec {
        for_token: input.parse()?,
        id: input.parse()?,
        in_token: input.parse()?,
        expr: input.parse()?,
      })
    }
  }

  impl Parse for CompSpec {
    fn parse(input: ParseStream) -> Result<Self> {
      if input.peek::<For>() {
        ForSpec::parse(input).map(CompSpec::from)
      } else if input.peek::<If>() {
        IfSpec::parse(input).map(CompSpec::from)
      } else {
        return Err(ParseError::unexpected_token(input.span()));
      }
    }
  }

  impl Parse for ExprAssert {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprAssert {
        assert_token: input.parse()?,
        cond: input.parse()?,
        msg: {
          if input.peek::<Colon>() {
            Some((input.parse()?, input.parse()?))
          } else {
            None
          }
        },
        semi_colon_token: input.parse()?,
        rest: input.parse()?,
      })
    }
  }

  impl Parse for ExprError {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprError {
        error_token: input.parse()?,
        expr: input.parse()?,
      })
    }
  }

  impl Parse for ExprFunction {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(ExprFunction {
        function_token: input.parse()?,
        left_paren_token: parentheses!(input => group),
        params: group.content.parse_terminated(Param::parse)?,
        right_paren_token: group.close()?,
        body: input.parse()?,
      })
    }
  }

  impl Parse for ExprIf {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprIf {
        if_token: input.parse()?,
        cond: input.parse()?,
        then_token: input.parse()?,
        if_true: input.parse()?,
        if_false: {
          if input.peek::<Else>() {
            Some((input.parse()?, input.parse()?))
          } else {
            None
          }
        },
      })
    }
  }

  fn parse_import_file(input: ParseStream) -> Result<ExprString> {
    define_error! {
      /// block string literals not allowed in imports
      struct BlockStringLiteralInImport;
    }

    define_error! {
      /// computed imports are not allowed
      struct ComputedValueExprInImport;
    }

    let expr: Expr = input.parse()?;

    match expr {
      Expr::String(s) if s.kind() == StringKind::Block => {
        Err(ParseError::new(BlockStringLiteralInImport::new(s.span())))
      }
      Expr::String(s) => Ok(*s),
      e => Err(ParseError::new(ComputedValueExprInImport::new(e.span()))),
    }
  }

  impl Parse for ExprImport {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprImport {
        import_token: input.parse()?,
        file: input.call(parse_import_file)?,
      })
    }
  }

  impl Parse for ExprImportStr {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprImportStr {
        import_str_token: input.parse()?,
        file: input.call(parse_import_file)?,
      })
    }
  }

  impl Parse for ExprUnary {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprUnary {
        op: input.parse()?,
        expr: input.call(parse_expr_unary)?,
      })
    }
  }

  impl Parse for ExprLocal {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ExprLocal {
        local_token: input.parse()?,
        binds: input.call(Punctuated::parse_separated_nonempty)?,
        semi_colon_token: input.parse()?,
        body: input.parse()?,
      })
    }
  }

  impl Parse for Bind {
    fn parse(input: ParseStream) -> Result<Self> {
      if input.peek2::<Parentheses>() {
        BindFunction::parse(input).map(Bind::from)
      } else {
        BindValue::parse(input).map(Bind::from)
      }
    }
  }

  impl Parse for BindValue {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(BindValue {
        name: input.parse()?,
        assign_token: input.parse()?,
        body: input.parse()?,
      })
    }
  }

  impl Parse for BindFunction {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(BindFunction {
        name: input.parse()?,
        left_paren_token: parentheses!(input => group),
        params: group.content.parse_terminated(Param::parse)?,
        right_paren_token: group.close()?,
        assign_token: input.parse()?,
        body: input.parse()?,
      })
    }
  }

  impl Parse for ExprSuper {
    fn parse(input: ParseStream) -> Result<Self> {
      let first_is_super = input.peek::<Super>();

      if first_is_super && input.peek2::<Dot>() {
        SuperField::parse(input).map(ExprSuper::from)
      } else if first_is_super && input.peek2::<Brackets>() {
        SuperComputed::parse(input).map(ExprSuper::from)
      } else {
        let forked = input.fork();

        // this will report error on missing "super" token if that is indeed the case
        let _: Super = forked.parse()?;

        // report actual error
        Err(ParseError::expected_tokens(
          forked.span(),
          &[Dot::NAME, BracketL::NAME],
        ))
      }
    }
  }

  impl Parse for SuperField {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(SuperField {
        super_token: input.parse()?,
        dot_token: input.parse()?,
        field_name: input.parse()?,
      })
    }
  }

  impl Parse for SuperComputed {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(SuperComputed {
        super_token: input.parse()?,
        left_bracket_token: brackets!(input => group),
        field: group.content.parse()?,
        right_bracket_token: group.close()?,
      })
    }
  }

  impl Parse for FieldNameIdent {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(FieldNameIdent {
        name: input.parse()?,
      })
    }
  }

  impl Parse for FieldNameString {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(FieldNameString {
        name: input.parse()?,
      })
    }
  }

  impl Parse for FieldNameComputed {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(FieldNameComputed {
        left_bracket_token: brackets!(input => group),
        name: group.content.parse()?,
        right_bracket_token: group.close()?,
      })
    }
  }

  impl Parse for ObjectFieldName {
    fn parse(input: ParseStream) -> Result<Self> {
      if input.peek::<Ident>() {
        FieldNameIdent::parse(input).map(ObjectFieldName::from)
      } else if input.peek::<String>() {
        FieldNameString::parse(input).map(ObjectFieldName::from)
      } else if input.peek::<Brackets>() {
        FieldNameComputed::parse(input).map(ObjectFieldName::from)
      } else {
        Err(ParseError::expected_tokens(
          input.span(),
          &[Ident::NAME, String::NAME, BracketL::NAME],
        ))
      }
    }
  }

  impl Parse for ObjectFieldValue {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ObjectFieldValue {
        name: input.parse()?,
        op: input.parse()?,
        value: input.parse()?,
      })
    }
  }

  impl Parse for ObjectFieldLocal {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ObjectFieldLocal {
        local_token: input.parse()?,
        bind: input.parse()?,
      })
    }
  }

  impl Parse for ObjectFieldAssert {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(ObjectFieldAssert {
        assert_token: input.parse()?,
        cond: input.parse()?,
        msg: {
          if input.peek::<Colon>() {
            let colon: Colon = input.parse()?;
            let msg: Expr = input.parse()?;
            Some((colon, msg))
          } else {
            None
          }
        },
      })
    }
  }

  impl Parse for ObjectFieldFunction {
    fn parse(input: ParseStream) -> Result<Self> {
      let group;
      Ok(ObjectFieldFunction {
        name: input.parse()?,
        left_paren_token: parentheses!(input => group),
        params: group.content.parse_terminated(Param::parse)?,
        right_paren_token: group.close()?,
        op: input.parse()?,
        value: input.parse()?,
      })
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use test_case::test_case;

  #[test]
  fn parse_param_without_default_value() {
    let content = "paramName";

    let file = FileId::UNKNOWN;
    let expected = Param {
      name: Ident::from_range(content, 0..content.len()),
      default_value: None,
    };
    let parsed: Param = crate::parse::parse(content, file).expect("parse");
    assert_eq!(parsed, expected);
  }

  #[test_case("null" => matches Expr::Null(_))]
  #[test_case("true" => matches Expr::True(_))]
  #[test_case("false" => matches Expr::False(_))]
  #[test_case("self" => matches Expr::SelfValue(_))]
  #[test_case("$" => matches Expr::Root(_))]
  #[test_case("'test'" => matches Expr::String(_))]
  #[test_case("42" => matches Expr::Number(_))]
  #[test_case("x" => matches Expr::Ident(_))]
  #[test_case("(null)" => matches Expr::Group(box ExprGroup { expr: Expr::Null(_), .. }))]
  #[test_case("(true)" => matches Expr::Group(box ExprGroup { expr: Expr::True(_), .. }))]
  #[test_case("(false)" => matches Expr::Group(box ExprGroup { expr: Expr::False(_), .. }))]
  #[test_case("(self)" => matches Expr::Group(box ExprGroup { expr: Expr::SelfValue(_), .. }))]
  #[test_case("($)" => matches Expr::Group(box ExprGroup { expr: Expr::Root(_), .. }))]
  #[test_case("('test')" => matches Expr::Group(box ExprGroup { expr: Expr::String(_), .. }))]
  #[test_case("(42)" => matches Expr::Group(box ExprGroup { expr: Expr::Number(_), .. }))]
  #[test_case("(x)" => matches Expr::Group(box ExprGroup { expr: Expr::Ident(_), .. }))]
  fn parse_expr_atom_simple(content: &str) -> Expr {
    let file = FileId::UNKNOWN;
    let parsed: Expr = crate::parse::parse(content, file).expect("parse");
    parsed
  }

  // taken from go-jsonnet parser tests
  #[test_case("true" ; "go_00")]
  #[test_case("1" ; "go_01")]
  #[test_case("1.2e3" ; "go_02")]
  #[test_case("!true" ; "go_03")]
  #[test_case("null" ; "go_04")]
  #[test_case("$.foo.bar" ; "go_05")]
  #[test_case("self.foo.bar" ; "go_06")]
  #[test_case("super.foo.bar" ; "go_07")]
  #[test_case("super[1]" ; "go_08")]
  #[test_case("error \"Error!\"" ; "go_09")]
  #[test_case("\"world\"" ; "go_10")]
  #[test_case("'world'" ; "go_11")]
  #[test_case("|||
    world
  |||" ; "go_12")]
  #[test_case("foo(bar)" ; "go_13")]
  #[test_case("foo(bar,)" ; "go_14")]
  #[test_case("foo(bar) tailstrict" ; "go_15")]
  #[test_case("foo(bar=42)" ; "go_16")]
  #[test_case("foo(bar=42,)" ; "go_17")]
  #[test_case("foo(bar, baz=42)" ; "go_18")]
  #[test_case("foo.bar" ; "go_19")]
  #[test_case("foo[bar]" ; "go_20")]
  #[test_case("true || false" ; "go_21")]
  #[test_case("0 && 1 || 0" ; "go_22")]
  #[test_case("0 && (1 || 0)" ; "go_23")]
  #[test_case("function(x) x" ; "go_24")]
  #[test_case("function(x=5) x" ; "go_25")]
  #[test_case("function(x, y=5) x" ; "go_26")]
  #[test_case("function(a=5, b) [a, b]" ; "go_27")]
  #[test_case("local foo = \"bar\"; foo" ; "go_28")]
  #[test_case("local foo(bar) = bar; foo(1)" ; "go_29")]
  #[test_case("{ local foo = \"bar\", baz: 1}" ; "go_30")]
  #[test_case("{ local foo(bar) = bar, baz: foo(1)}" ; "go_31")]
  #[test_case("{ foo(bar, baz): bar+baz }" ; "go_32")]
  #[test_case("{ [\"foo\" + \"bar\"]: 3 }" ; "go_33")]
  #[test_case("{ [\"field\" + x]: x for x in [1, 2, 3] }" ; "go_34")]
  #[test_case("{ local y = x, [\"field\" + x]: x for x in [1, 2, 3] }" ; "go_35")]
  #[test_case("{ [\"field\" + x]: x for x in [1, 2, 3] if x <= 2 }" ; "go_36")]
  #[test_case("{ [\"field\" + x + y]: x + y for x in [1, 2, 3] if x <= 2 for y in [4, 5, 6]}" ; "go_37")]
  #[test_case("[]" ; "go_38")]
  #[test_case("[a, b, c]" ; "go_39")]
  #[test_case("[x for x in [1,2,3] ]" ; "go_40")]
  #[test_case("[x for x in [1,2,3] if x <= 2]" ; "go_41")]
  #[test_case("[x+y for x in [1,2,3] if x <= 2 for y in [4, 5, 6]]" ; "go_42")]
  #[test_case("{}" ; "go_43")]
  #[test_case("{ hello: \"world\" }" ; "go_44")]
  #[test_case("{ hello +: \"world\" }" ; "go_45")]
  #[test_case("{
    hello: \"world\",
    \"name\":: joe,
    'mood'::: \"happy\",
    |||
      key type
  |||: \"block\",
  }" ; "go_46")]
  #[test_case("assert true: 'woah!'; true" ; "go_47")]
  #[test_case("{ assert true: 'woah!', foo: bar }" ; "go_48")]
  #[test_case("if n > 1 then 'foos' else 'foo'" ; "go_49")]
  #[test_case("local foo = function(x) x + 1; true" ; "go_50")]
  #[test_case("local foo = function(x=5) x + 1; true" ; "go_51")]
  #[test_case("local foo = function(x=5) x + 1; x(x=3)" ; "go_52")]
  #[test_case("import 'foo.jsonnet'" ; "go_53")]
  #[test_case("importstr 'foo.text'" ; "go_54")]
  #[test_case("{a: b} + {c: d}" ; "go_55")]
  #[test_case("{a: b}{c: d}" ; "go_56")]
  #[test_case("[][0]" ; "go_57")]
  #[test_case("[][:]" ; "go_58")]
  #[test_case("[][1:]" ; "go_59")]
  #[test_case("[][:1]" ; "go_60")]
  #[test_case("[][1:2]" ; "go_61")]
  #[test_case("[][::]" ; "go_62")]
  #[test_case("[][1::]" ; "go_63")]
  #[test_case("[][:1:]" ; "go_64")]
  #[test_case("[][::1]" ; "go_65")]
  #[test_case("[][1:1:]" ; "go_66")]
  #[test_case("[][:1:1]" ; "go_67")]
  #[test_case("[][1::1]" ; "go_68")]
  #[test_case("[][1:1:1]" ; "go_69")]
  #[test_case("a in b" ; "go_70")]
  #[test_case("{ x: if \"opt\" in super then \"x\" else \"y\" }" ; "go_71")]
  // custom cases added
  #[test_case("{\"foo\"(): 'bar'}" ; "custom_0")]
  #[test_case("{[\"foo\"]()::: 'bar'}" ; "custom_1")]
  fn exprs(content: &str) {
    let file = FileId::UNKNOWN;
    let _: Expr =
      crate::parse::parse(content, file).expect(&format!("parses successfully: {:?}", content));
  }

  #[test_case(",", "test:1:1-2 Unexpected: \",\" while parsing terminal" ; "go_0")]
  #[test_case("function(a, b c)", "test:1:15-16 Expected a comma before next function parameter, got (IDENTIFIER, \"c\")" ; "go_1")]
  #[test_case("function(a, 1)", "test:1:13-14 Expected token IDENTIFIER but got (NUMBER, \"1\") while parsing parameter" ; "go_2")]
  #[test_case("function(,)", "test:1:10-11 Expected token IDENTIFIER but got \",\" while parsing parameter" ; "go_3")]
  #[test_case("function(a=)", "test:1:12-13 Unexpected: \")\" while parsing terminal" ; "go_4")]
  #[test_case("function(a=,)", "test:1:12-13 Unexpected: \",\" while parsing terminal" ; "go_5")]
  #[test_case("a b", "test:1:3-4 Did not expect: (IDENTIFIER, \"b\")" ; "go_6")]
  #[test_case("foo(a, bar(a b))", "test:1:14-15 Expected a comma before next function argument, got (IDENTIFIER, \"b\")" ; "go_7")]
  #[test_case("local", "test:1:6 Expected token IDENTIFIER but got end of file" ; "go_8")]
  #[test_case("local foo(a b) = a; true", "test:1:13-14 Expected a comma before next function parameter, got (IDENTIFIER, \"b\")" ; "go_10")]
  #[test_case("local foo(a): a; true", "test:1:13-14 Expected operator = but got (OPERATOR, \":\")" ; "go_11")]
  #[test_case("local foo(a) = bar(a b); true", "test:1:22-23 Expected a comma before next function argument, got (IDENTIFIER, \"b\")" ; "go_12")]
  #[test_case("local foo: 1; true", "test:1:10-11 Expected operator = but got (OPERATOR, \":\")" ; "go_13")]
  #[test_case("local foo = bar(a b); true", "test:1:19-20 Expected a comma before next function argument, got (IDENTIFIER, \"b\")" ; "go_14")]
  #[test_case("{a b}", "test:1:4-5 Expected token OPERATOR but got (IDENTIFIER, \"b\")" ; "go_15")]
  #[test_case("{a = b}", "test:1:4-5 Expected one of :, ::, :::, +:, +::, +:::, got: =" ; "go_16")]
  #[test_case("{a :::: b}", "test:1:4-8 Expected one of :, ::, :::, +:, +::, +:::, got: ::::" ; "go_17")]
  #[test_case("{assert x for x in [1, 2, 3]}", "test:1:11-14 Object comprehension cannot have asserts" ; "go_18")]
  #[test_case("{['foo' + x]: true, [x]: x for x in [1, 2, 3]}", "test:1:28-31 Object comprehension can only have one field" ; "go_19")]
  #[test_case("{foo: x for x in [1, 2, 3]}", "test:1:9-12 Object comprehensions can only have [e] fields" ; "go_20")]
  #[test_case("{[x]:: true for x in [1, 2, 3]}", "test:1:13-16 Object comprehensions cannot have hidden fields" ; "go_21")]
  #[test_case("{[x]: true for 1 in [1, 2, 3]}", "test:1:16-17 Expected token IDENTIFIER but got (NUMBER, \"1\")" ; "go_22")]
  #[test_case("{[x]: true for x at [1, 2, 3]}", "test:1:18-20 Expected token in but got (IDENTIFIER, \"at\")" ; "go_23")]
  #[test_case("{[x]: true for x in [1, 2 3]}", "test:1:27-28 Expected a comma before next array element" ; "go_24")]
  #[test_case("{[x]: true for x in [1, 2, 3] if (a b)}", "test:1:37-38 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_25")]
  #[test_case("{[x]: true for x in [1, 2, 3] if a b}", "test:1:36-37 Expected for, if or \"}\" after for clause, got: (IDENTIFIER, \"b\")" ; "go_26")]
  #[test_case("{a: b c:d}", "test:1:7-8 Expected a comma before next field" ; "go_27")]
  #[test_case("{[(x y)]: z}", "test:1:6-7 Expected token \")\" but got (IDENTIFIER, \"y\")" ; "go_28")]
  #[test_case("{[x y]: z}", "test:1:5-6 Expected token \"]\" but got (IDENTIFIER, \"y\")" ; "go_29")]
  #[test_case("{foo(x y): z}", "test:1:8-9 Expected a comma before next method parameter, got (IDENTIFIER, \"y\")" ; "go_30")]
  #[test_case("{foo(x)+: z}", "test:1:2-5 Cannot use +: syntax sugar in a method: foo" ; "go_31")]
  #[test_case("{foo: (1 2)}", "test:1:10-11 Expected token \")\" but got (NUMBER, \"2\")" ; "go_33")]
  #[test_case("{local 1 = 3, true}", "test:1:8-9 Expected token IDENTIFIER but got (NUMBER, \"1\")" ; "go_34")]
  #[test_case("{local foo(a b) = 1, a: true}", "test:1:14-15 Expected a comma before next function parameter, got (IDENTIFIER, \"b\")" ; "go_36")]
  #[test_case("{local foo(a): 1, a: true}", "test:1:14-15 Expected operator = but got (OPERATOR, \":\")" ; "go_37")]
  #[test_case("{local foo(a) = (a b), a: true}", "test:1:20-21 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_38")]
  #[test_case("{assert (a b), a: true}", "test:1:12-13 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_39")]
  #[test_case("{assert a: (a b), a: true}", "test:1:15-16 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_40")]
  #[test_case("{function(a, b) a+b: true}", "test:1:2-10 Unexpected: \"function\" while parsing field definition" ; "go_41")]
  #[test_case("[(a b), 2, 3]", "test:1:5-6 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_42")]
  #[test_case("[1, (a b), 2, 3]", "test:1:8-9 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_43")]
  #[test_case("[a for b in [1 2 3]]", "test:1:16-17 Expected a comma before next array element" ; "go_44")]
  #[test_case("for", "test:1:1-4 Unexpected: \"for\" while parsing terminal" ; "go_45")]
  #[test_case("", "test:1:1 Unexpected end of file" ; "go_46")]
  #[test_case("((a b))", "test:1:5-6 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_47")]
  #[test_case("a.1", "test:1:3-4 Expected token IDENTIFIER but got (NUMBER, \"1\")" ; "go_48")]
  #[test_case("super.1", "test:1:7-8 Expected token IDENTIFIER but got (NUMBER, \"1\")" ; "go_49")]
  #[test_case("super[(a b)]", "test:1:10-11 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_50")]
  #[test_case("super[a b]", "test:1:9-10 Expected token \"]\" but got (IDENTIFIER, \"b\")" ; "go_51")]
  #[test_case("super", "test:1:1-6 Expected . or [ after super" ; "go_52")]
  #[test_case("assert (a b); true", "test:1:11-12 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_53")]
  #[test_case("assert a: (a b); true", "test:1:14-15 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_54")]
  #[test_case("assert a: 'foo', true", "test:1:16-17 Expected token \";\" but got \",\"" ; "go_55")]
  #[test_case("assert a: 'foo'; (a b)", "test:1:21-22 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_56")]
  #[test_case("error (a b)", "test:1:10-11 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_57")]
  #[test_case("if (a b) then c", "test:1:7-8 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_58")]
  #[test_case("if a b c", "test:1:6-7 Expected token then but got (IDENTIFIER, \"b\")" ; "go_59")]
  #[test_case("if a then (b c)", "test:1:14-15 Expected token \")\" but got (IDENTIFIER, \"c\")" ; "go_60")]
  #[test_case("if a then b else (c d)", "test:1:21-22 Expected token \")\" but got (IDENTIFIER, \"d\")" ; "go_61")]
  #[test_case("function(a) (a b)", "test:1:16-17 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_62")]
  #[test_case("function a a", "test:1:10-11 Expected ( but got (IDENTIFIER, \"a\")" ; "go_63")]
  #[test_case("import (a b)", "test:1:11-12 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_64")]
  #[test_case("import (a+b)", "test:1:8-13 Computed imports are not allowed" ; "go_65")]
  #[test_case("importstr (a b)", "test:1:14-15 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_66")]
  #[test_case("importstr (a+b)", "test:1:11-16 Computed imports are not allowed" ; "go_67")]
  #[test_case("local a = b ()", "test:1:15 Expected , or ; but got end of file" ; "go_68")]
  #[test_case("local a = b; (a b)", "test:1:17-18 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_69")]
  #[test_case("1+ <<", "test:1:4-6 Not a unary operator: <<" ; "go_70")]
  #[test_case("-(a b)", "test:1:5-6 Expected token \")\" but got (IDENTIFIER, \"b\")" ; "go_71")]
  #[test_case("1~2", "test:1:2-3 Not a binary operator: ~" ; "go_72")]
  #[test_case("a[(b c)]", "test:1:6-7 Expected token \")\" but got (IDENTIFIER, \"c\")" ; "go_73")]
  #[test_case("a[b c]", "test:1:5-6 Expected token \"]\" but got (IDENTIFIER, \"c\")" ; "go_74")]
  #[test_case("a[]", "test:1:3-4 ast.Index requires an expression" ; "go_75")]
  #[test_case("a[42:42:42:42]", "test:1:11-12 Invalid slice: too many colons" ; "go_76")]
  #[test_case("a[42:42::42]", "test:1:8-10 Invalid slice: too many colons" ; "go_77")]
  #[test_case("a{b c}", "test:1:5-6 Expected token OPERATOR but got (IDENTIFIER, \"c\")" ; "go_78")]
  fn errors(content: &str, _: &str) {
    let file = FileId::UNKNOWN;
    crate::parse::parse::<Expr>(content, file)
      .expect_err(&format!("does not parse successfully: {:?}", content));
  }
}
