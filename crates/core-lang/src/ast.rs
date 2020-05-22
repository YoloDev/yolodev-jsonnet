use crate::TextRange;
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
  ($arg:ident Box<CoreExpr>) => {$arg.into_boxed_expr()};
  (impl $t:ty) => {impl Into<$t>};
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
        $variant:ident,
      )+
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone, Copy)]
    pub enum $name {
      $($variant(Option<TextRange>),)*
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
      pub fn from_token(tok: $tok) -> Self {
        use $tok::*;
        match tok {
          $(
            $variant(it) => $name::$variant(Some(it.text_range())),
          )*
        }
      }
    }
  };
}

/// Identifier
#[derive(Debug, Clone)]
pub struct Ident {
  pub(crate) name: SmolStr,
  /// Identifier id. Unique per document. This makes it so that
  /// when there are two identifiers with the same name in in
  /// different contexts (different functions for instance), they
  /// each get their own unique identifier.
  pub(crate) id: u32,
  pub(crate) text_range: Option<TextRange>,
}

impl private::Sealed for Ident {}
impl CoreNode for Ident {
  fn range(&self) -> Option<TextRange> {
    self.text_range
  }
}

#[derive(Debug, Clone)]
pub(crate) enum LiteralToken {
  Null,
  True,
  False,
  String(String),
  Number(f64),
}

/// Literal value
#[derive(Debug, Clone)]
pub enum Literal<'a> {
  Null,
  Bool(bool),
  String(&'a str),
  Number(f64),
}

/// Literal expression
#[derive(Debug, Clone)]
pub struct LiteralCoreExpr {
  pub(crate) text_range: Option<TextRange>,
  pub(crate) token: LiteralToken,
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

  pub fn new_str(s: impl Into<String>) -> Self {
    LiteralCoreExpr::new(LiteralToken::String(s.into()))
  }
}

impl LiteralCoreExpr {
  /// Get literal value
  pub fn value(&self) -> Literal {
    match &self.token {
      LiteralToken::Null => Literal::Null,
      LiteralToken::True => Literal::Bool(true),
      LiteralToken::False => Literal::Bool(false),
      LiteralToken::String(v) => Literal::String(v),
      LiteralToken::Number(v) => Literal::Number(*v),
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
pub enum ImportKind {
  /// Import file as jsonnet file (and evaluate it)
  Jsonnet,

  /// Import file as string (same as a string literal)
  String,
}

ast_node! {
  /// Import expression
  pub struct ImportCoreExpr {
    file: (String),
    kind: (ImportKind),
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
  pub enum ObjectFieldOperator(ast::ObjectFieldAssignmentOp) {
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
  pub struct ObjectField {
    name: (CoreExpr),
    op: (ObjectFieldOperator),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Object expression
  pub struct ObjectCoreExpr {
    asserts: (Vec<CoreExpr>),
    fields: (Vec<ObjectField>),
  }
}

ast_node! {
  /// Object comprehension expression
  pub struct ObjectCompCoreExpr {
    field_name: (Box<CoreExpr>),
    field_value: (Box<CoreExpr>),
    loop_var_ident: (Ident),
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
  pub struct LocalBind {
    ident: (Ident),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Local expression
  pub struct LocalCoreExpr {
    binds: (Vec<LocalBind>),
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
  pub enum BinaryOperator(ast::BinaryOp) {
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
  }
}

ast_node! {
  /// Binary expression
  pub struct BinaryCoreExpr {
    lhs: (Box<CoreExpr>),
    op: (BinaryOperator),
    rhs: (Box<CoreExpr>),
  }
}

ast_op! {
  /// Unary operator
  pub enum UnaryOperator(ast::UnaryOp) {
    Plus,
    Minus,
    Not,
    BitNeg,
  }
}

ast_node! {
  /// Unary expression
  pub struct UnaryCoreExpr {
    op: (UnaryOperator),
    expr: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Function param
  pub struct FunctionParam {
    name: (Ident),
    default_value: (CoreExpr),
  }
}

ast_node! {
  /// Function expression
  pub struct FunctionCoreExpr {
    params: (Vec<FunctionParam>),
    expr: (Box<CoreExpr>),
  }
}

ast_node! {
  /// Function param
  pub struct NamedArg {
    name: (Ident),
    value: (CoreExpr),
  }
}

ast_node! {
  /// Apply expression
  pub struct ApplyCoreExpr {
    target: (Box<CoreExpr>),
    positionals: (Vec<CoreExpr>),
    named: (Vec<NamedArg>),
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
    ident: (Ident),
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
