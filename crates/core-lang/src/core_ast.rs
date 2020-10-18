use crate::TextRange;
use core::num::NonZeroU32;
use derive_more::{From, TryInto};
use jsonnet_syntax::{ast, SmolStr};

mod private {
  pub trait Sealed {}
}

/// Common trait implemented for all core language nodes.
pub trait CoreNode: private::Sealed {
  fn range(&self) -> Option<TextRange>;
}

/// Types that can be converted into a `CoreExpr`.
pub trait IntoCoreExpr: private::Sealed + Sized {
  fn into_expr(self) -> CoreExpr;

  #[inline]
  fn into_boxed_expr(self) -> Box<CoreExpr> {
    Box::from(self.into_expr())
  }
}

// Makes blanket impl cover CoreExpr
impl private::Sealed for CoreExpr {}
impl<T> IntoCoreExpr for T
where
  T: private::Sealed + Sized + Into<CoreExpr>,
{
  #[inline]
  fn into_expr(self) -> CoreExpr {
    self.into()
  }
}

impl private::Sealed for Box<CoreExpr> {}
impl IntoCoreExpr for Box<CoreExpr> {
  #[inline]
  fn into_expr(self) -> CoreExpr {
    *self
  }

  #[inline]
  fn into_boxed_expr(self) -> Box<CoreExpr> {
    self
  }
}

macro_rules! ast_ctor_param {
  (impl Box<CoreExpr>) => {impl IntoCoreExpr};
  (return Box<CoreExpr>) => {&CoreExpr};
  ($this:ident $fld:ident => Box<CoreExpr>) => {&$this.$fld};
  ($arg:ident Box<CoreExpr>) => {$arg.into_boxed_expr()};
  (impl Vec<$t:ty>) => {impl IntoIterator<Item = $t>};
  (return Vec<$t:ty>) => {&[$t]};
  ($this:ident $fld:ident => Vec<$t:ty>) => {&$this.$fld};
  ($arg:ident Vec<$t:ty>) => {$arg.into_iter().collect()};
  (return bool) => {bool};
  ($this:ident $fld:ident => bool) => {$this.$fld};
  (return SmolStr) => {&str};
  ($this:ident $fld:ident => SmolStr) => {&$this.$fld};
  (return String) => {&str};
  ($this:ident $fld:ident => String) => {&$this.$fld};
  (impl $t:ty) => {impl Into<$t>};
  (return $t:ty) => {&$t};
  ($this:ident $fld:ident => $t:ty) => {&$this.$fld};
  ($arg:ident $t:ty) => {$arg.into()};
}

macro_rules! ast_node {
  (
    $(#[$($m:tt)*])*
    pub struct $name:ident {
      $(
        $(#[$($fld_m:tt)*])*
        $fld:ident: ($($t:tt)*),
      )*
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone)]
    pub struct $name {
      /// Original text range (if any)
      pub(crate) text_range: Option<TextRange>,
      $(
        $(#[$($fld_m)*])*
        pub(crate) $fld: $($t)*,
      )*
    }

    impl $name {
      pub fn new(
        $(
          $fld: ast_ctor_param!(impl $($t)*),
        )*
      ) -> Self {
        $name {
          text_range: None,
          $(
            $fld: ast_ctor_param!($fld $($t)*),
          )*
        }
      }

      pub(crate) fn new_from(
        text_range: TextRange,
        $(
          $fld: ast_ctor_param!(impl $($t)*),
        )*
      ) -> Self {
        $name {
          text_range: Some(text_range),
          $(
            $fld: ast_ctor_param!($fld $($t)*),
          )*
        }
      }

      #[allow(unused)]
      pub(crate) fn with_range(mut self, text_range: TextRange) -> Self {
        self.text_range = Some(text_range);
        self
      }

      $(
        #[inline]
        pub fn $fld(&self) -> ast_ctor_param!(return $($t)*) {
          ast_ctor_param!(self $fld => $($t)*)
        }
      )*
    }

    impl private::Sealed for $name {}
    impl CoreNode for $name {
      #[inline]
      fn range(&self) -> Option<TextRange> {
        self.text_range
      }
    }
  };

  (
    $(#[$($m:tt)*])*
    pub struct $name:ident;
  ) => {
    ast_node! {
      $(#[$($m)*])*
      pub struct $name {}
    }
  };
}

macro_rules! ast_op {
  (
    $(#[$($m:tt)*])*
    pub enum $name:ident($tok:path) {
      $(
        $(#[$($variant_m:tt)*])*
        $variant:ident,
      )+
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone, Copy)]
    pub enum $name {
      $($(#[$($variant_m)*])* $variant(Option<TextRange>),)*
    }

    impl private::Sealed for $name {}
    impl CoreNode for $name {
      #[inline]
      fn range(&self) -> Option<TextRange> {
        match self {
          $(
            $name::$variant(r) => *r,
          )*
        }
      }
    }

    impl $name {
      pub fn from_token(tok: $tok) -> Option<Self> {
        use $tok::*;
        #[allow(unreachable_patterns)]
        match tok {
          $(
            $variant(it) => Some($name::$variant(Some(it.text_range()))),
          )*
          _ => None,
        }
      }

      $(
        paste::item! {
          $(#[$($variant_m)*])*
          #[allow(dead_code)]
          pub(crate) fn [< $variant:snake:lower >]() -> Self {
            $name::$variant(None)
          }
        }
      )*
    }
  };
}

/// Identifier
#[derive(Debug, Clone)]
pub struct CoreIdent {
  pub(crate) name: SmolStr,
  /// Identifier id. Unique per document. This makes it so that
  /// when there are two identifiers with the same name in in
  /// different contexts (different functions for instance), they
  /// each get their own unique identifier.
  pub(crate) id: Option<NonZeroU32>,
  pub(crate) text_range: Option<TextRange>,
}

impl private::Sealed for CoreIdent {}
impl CoreNode for CoreIdent {
  fn range(&self) -> Option<TextRange> {
    self.text_range
  }
}

impl CoreIdent {
  #[doc(hidden)]
  pub unsafe fn new_unchecked(name: &str, id: u32) -> Self {
    CoreIdent {
      name: name.into(),
      id: Some(NonZeroU32::new_unchecked(id)),
      text_range: None,
    }
  }

  pub fn id(&self) -> Option<NonZeroU32> {
    self.id
  }

  pub fn name(&self) -> &str {
    &self.name
  }
}

#[derive(Debug, Clone)]
pub enum LiteralToken {
  Null,
  True,
  False,
  String(String),
  Number(f64),
}

/// Literal value
#[derive(Debug, Clone)]
pub enum CoreLiteral<'a> {
  Null,
  Bool(bool),
  String(&'a str),
  Number(f64),
}

/// Literal expression
#[derive(Debug, Clone)]
pub struct LiteralCoreExpr {
  pub text_range: Option<TextRange>,
  pub token: LiteralToken,
}

impl private::Sealed for LiteralCoreExpr {}
impl CoreNode for LiteralCoreExpr {
  fn range(&self) -> Option<TextRange> {
    self.text_range
  }
}

impl LiteralCoreExpr {
  pub(crate) fn new(token: LiteralToken) -> Self {
    LiteralCoreExpr {
      text_range: None,
      token,
    }
  }

  pub(crate) fn new_from(text_range: TextRange, token: LiteralToken) -> Self {
    LiteralCoreExpr {
      text_range: Some(text_range),
      token,
    }
  }

  pub fn new_str(s: impl Into<String>) -> Self {
    LiteralCoreExpr::new(LiteralToken::String(s.into()))
  }

  pub fn new_str_from(text_range: TextRange, s: impl Into<String>) -> Self {
    LiteralCoreExpr::new_from(text_range, LiteralToken::String(s.into()))
  }

  pub fn new_number(number: f64) -> Self {
    LiteralCoreExpr::new(LiteralToken::Number(number))
  }

  pub fn new_number_from(text_range: TextRange, number: f64) -> Self {
    LiteralCoreExpr::new_from(text_range, LiteralToken::Number(number))
  }

  pub fn new_int(s: u32) -> Self {
    LiteralCoreExpr::new_number(s.into())
  }

  pub fn new_null() -> Self {
    LiteralCoreExpr::new(LiteralToken::Null)
  }

  pub fn new_null_from(text_range: TextRange) -> Self {
    LiteralCoreExpr::new_from(text_range, LiteralToken::Null)
  }

  pub fn new_true() -> Self {
    LiteralCoreExpr::new(LiteralToken::True)
  }

  pub fn new_true_from(text_range: TextRange) -> Self {
    LiteralCoreExpr::new_from(text_range, LiteralToken::True)
  }

  pub fn new_false() -> Self {
    LiteralCoreExpr::new(LiteralToken::False)
  }

  pub fn new_false_from(text_range: TextRange) -> Self {
    LiteralCoreExpr::new_from(text_range, LiteralToken::False)
  }

  pub(crate) fn with_range(mut self, text_range: TextRange) -> Self {
    self.text_range = Some(text_range);
    self
  }
}

impl LiteralCoreExpr {
  /// Get literal value
  pub fn value(&self) -> CoreLiteral {
    match &self.token {
      LiteralToken::Null => CoreLiteral::Null,
      LiteralToken::True => CoreLiteral::Bool(true),
      LiteralToken::False => CoreLiteral::Bool(false),
      LiteralToken::String(v) => CoreLiteral::String(v),
      LiteralToken::Number(v) => CoreLiteral::Number(*v),
    }
  }
}

ast_node! {
  /// Self expression
  pub struct SelfCoreExpr;
}

ast_node! {
  /// Super expression
  pub struct SuperCoreExpr;
}

/// Import kind
#[derive(Debug, Clone, Copy)]
pub enum CoreImportKind {
  /// Import file as jsonnet file (and evaluate it)
  Jsonnet,

  /// Import file as string (same as a string literal)
  String,
}

ast_node! {
  /// Import expression
  pub struct ImportCoreExpr {
    file: (String),
    kind: (CoreImportKind),
  }
}

ast_node! {
  /// Error expression
  pub struct ErrorCoreExpr {
    expr: (Box<CoreExpr>),
  }
}

impl ErrorCoreExpr {
  pub(crate) fn new_str(s: impl Into<String>) -> Self {
    ErrorCoreExpr::new(LiteralCoreExpr::new_str(s))
  }
}

ast_op! {
  /// Object field assignment operator
  pub enum CoreObjectFieldOperator(ast::ObjectFieldAssignmentOp) {
    Default,
    Hidden,
    Visible,
    MergeDefault,
    MergeHidden,
    MergeVisible,
  }
}

ast_node! {
  /// Object field
  pub struct CoreObjectField {
    name: (CoreExpr),
    op: (CoreObjectFieldOperator),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Object expression
  pub struct ObjectCoreExpr {
    asserts: (Vec<CoreExpr>),
    fields: (Vec<CoreObjectField>),
  }
}

ast_node! {
  /// Object comprehension expression
  pub struct ObjectCompCoreExpr {
    field_name: (Box<CoreExpr>),
    field_value: (Box<CoreExpr>),
    loop_var_ident: (CoreIdent),
    list: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Member access expression
  pub struct MemberAccessCoreExpr {
    target: (Box<CoreExpr>),
    field_name: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Local binding
  pub struct CoreLocalBind {
    ident: (CoreIdent),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Local expression
  pub struct LocalCoreExpr {
    binds: (Vec<CoreLocalBind>),
    rest: (Box<CoreExpr>),
  }
}

ast_node! {
  /// If expression
  pub struct IfCoreExpr {
    cond: (Box<CoreExpr>),
    if_true: (Box<CoreExpr>),
    if_false: (Box<CoreExpr>),
  }
}

ast_op! {
  /// Binary operator
  pub enum CoreBinaryOperator(ast::BinaryOp) {
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
}

ast_node! {
  /// Binary expression
  pub struct BinaryCoreExpr {
    lhs: (Box<CoreExpr>),
    op: (CoreBinaryOperator),
    rhs: (Box<CoreExpr>),
  }
}

ast_op! {
  /// Unary operator
  pub enum CoreUnaryOperator(ast::UnaryOp) {
    Plus,
    Minus,
    Not,
    BitNeg,
  }
}

ast_node! {
  /// Unary expression
  pub struct UnaryCoreExpr {
    op: (CoreUnaryOperator),
    expr: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Function param
  pub struct CoreFunctionParam {
    name: (CoreIdent),
    default_value: (CoreExpr),
  }
}

ast_node! {
  /// Function expression
  pub struct FunctionCoreExpr {
    params: (Vec<CoreFunctionParam>),
    expr: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Function param
  pub struct CoreNamedArg {
    name: (SmolStr),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Apply expression
  pub struct ApplyCoreExpr {
    target: (Box<CoreExpr>),
    positionals: (Vec<CoreExpr>),
    named: (Vec<CoreNamedArg>),
    is_tailstrict: (bool),
  }
}

ast_node! {
  /// Array expression
  pub struct ArrayCoreExpr {
    items: (Vec<CoreExpr>),
  }
}

impl ArrayCoreExpr {
  pub fn new_empty() -> Self {
    ArrayCoreExpr::new(Vec::new())
  }
}

ast_node! {
  /// Ident expression
  pub struct IdentCoreExpr {
    ident: (CoreIdent),
  }
}

/// An expression in the core language
#[derive(Debug, Clone, From, TryInto)]
pub enum CoreExpr {
  Literal(LiteralCoreExpr),
  SelfValue(SelfCoreExpr),
  Super(SuperCoreExpr),
  Object(ObjectCoreExpr),
  ObjectComp(ObjectCompCoreExpr),
  Array(ArrayCoreExpr),
  MemberAccess(MemberAccessCoreExpr),
  Ident(IdentCoreExpr),
  Local(LocalCoreExpr),
  If(IfCoreExpr),
  Binary(BinaryCoreExpr),
  Unary(UnaryCoreExpr),
  Function(FunctionCoreExpr),
  Apply(ApplyCoreExpr),
  Error(ErrorCoreExpr),
  Import(ImportCoreExpr),
}

impl CoreExpr {
  pub(crate) fn with_range(self, text_range: TextRange) -> Self {
    match self {
      CoreExpr::Literal(it) => CoreExpr::Literal(it.with_range(text_range)),
      CoreExpr::SelfValue(it) => CoreExpr::SelfValue(it.with_range(text_range)),
      CoreExpr::Super(it) => CoreExpr::Super(it.with_range(text_range)),
      CoreExpr::Object(it) => CoreExpr::Object(it.with_range(text_range)),
      CoreExpr::ObjectComp(it) => CoreExpr::ObjectComp(it.with_range(text_range)),
      CoreExpr::Array(it) => CoreExpr::Array(it.with_range(text_range)),
      CoreExpr::MemberAccess(it) => CoreExpr::MemberAccess(it.with_range(text_range)),
      CoreExpr::Ident(it) => CoreExpr::Ident(it.with_range(text_range)),
      CoreExpr::Local(it) => CoreExpr::Local(it.with_range(text_range)),
      CoreExpr::If(it) => CoreExpr::If(it.with_range(text_range)),
      CoreExpr::Binary(it) => CoreExpr::Binary(it.with_range(text_range)),
      CoreExpr::Unary(it) => CoreExpr::Unary(it.with_range(text_range)),
      CoreExpr::Function(it) => CoreExpr::Function(it.with_range(text_range)),
      CoreExpr::Apply(it) => CoreExpr::Apply(it.with_range(text_range)),
      CoreExpr::Error(it) => CoreExpr::Error(it.with_range(text_range)),
      CoreExpr::Import(it) => CoreExpr::Import(it.with_range(text_range)),
    }
  }
}
