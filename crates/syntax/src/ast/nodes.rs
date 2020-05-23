use crate::{
  ast::{support, AstChildren, AstNode, AstToken, Ident, Number, String},
  SyntaxKind, SyntaxNode, SyntaxToken, T,
};

trait ConcreteNode: AstNode {
  const SYNTAX_KIND: SyntaxKind;
}

macro_rules! ast_node_member {
  ($name:ident, $(#[$($m:tt)*])* $fld:ident, $node:ident) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> Option<$node> { support::child(&self.syntax) }
  };

  ($name:ident, $(#[$($m:tt)*])* $fld:ident, [$node:ident]) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> AstChildren<$node> { support::children(&self.syntax) }
  };

  ($name:ident, $(#[$($m:tt)*])* $fld:ident, {$($tok:tt)*}) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![$($tok)*]) }
  };

  ($name:ident, $(#[$($m:tt)*])* $fld:ident, ( $( {$($tok:tt)*} )|+ )) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> Option<SyntaxToken> { support::token_any_of(&self.syntax, &[
      $(T![$($tok)*],)*
    ]) }
  };

  ($name:ident, $(#[$($m:tt)*])* $fld:ident, ( $ast_token:ident )) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> Option<$ast_token> { support::token_kind(&self.syntax) }
  };

  ($name:ident, $(#[$($m:tt)*])* $fld:ident, ( $( $syntax:ident ).+ => $node:ident )) => {
    $(#[$($m)*])*
    pub fn $fld(&self) -> Option<$node> { support::nested_child(&self.syntax, &[
      $(SyntaxKind::$syntax,)*
    ]) }
  };
}

macro_rules! ast_node {
  (
    $(#[$($m:tt)*])*
    pub struct $name:ident($kind:ident) {
      $(
        $(#[$($fld_m:tt)*])*
        $fld:ident: $t:tt,
      )*
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct $name {
      pub(crate) syntax: SyntaxNode,
    }

    impl $name {
      $(
        ast_node_member!($name, $(#[$($fld_m)*])* $fld, $t);
      )*
    }

    impl AstNode for $name {
      #[inline]
      fn can_cast(kind: SyntaxKind) -> bool { kind == SyntaxKind::$kind }

      fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
          Some(Self { syntax })
        } else {
          None
        }
      }
      fn syntax(&self) -> &SyntaxNode { &self.syntax }
    }

    impl ConcreteNode for $name {
      const SYNTAX_KIND: SyntaxKind = SyntaxKind::$kind;
    }
  };
}

macro_rules! ast_kind {
  (
    $(#[$($m:tt)*])*
    pub enum $name:ident {
      $(
        $(#[$($variant_m:tt)*])*
        $variant:ident($inner:ident),
      )*
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum $name {
      $(
        $(#[$($variant_m)*])*
        $variant($inner),
      )*
    }

    impl AstNode for $name {
      fn can_cast(kind: SyntaxKind) -> bool {
        match kind {
          $(
            <$inner as ConcreteNode>::SYNTAX_KIND => true,
          )*
          _ => false,
        }
      }

      fn cast(syntax: SyntaxNode) -> Option<Self> {
        match syntax.kind() {
          $(
            <$inner as ConcreteNode>::SYNTAX_KIND => Some($name::$variant($inner { syntax })),
          )*
          _ => None,
        }
      }

      fn syntax(&self) -> &SyntaxNode {
        match self {
          $(
            $name::$variant(it) => &it.syntax,
          )*
        }
      }
    }
  };
}

macro_rules! op_kind {
  (
    $(#[$($m:tt)*])*
    pub enum $name:ident {
      $(
        $(#[$($variant_m:tt)*])*
        $variant:ident($($tok:tt)*),
      )*
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum $name {
      $(
        $(#[$($variant_m)*])*
        $variant(SyntaxToken),
      )*
    }

    impl AstToken for $name {
      fn can_cast(token: SyntaxKind) -> bool
      where
        Self: Sized
      {
        match token {
          $(
            T![$($tok)*] => true,
          )*
          _ => false,
        }
      }

      fn cast(syntax: SyntaxToken) -> Option<Self>
      where
        Self: Sized
      {
        match syntax.kind() {
          $(
            T![$($tok)*] => Some($name::$variant(syntax)),
          )*
          _ => None,
        }
      }

      fn syntax(&self) -> &SyntaxToken {
        match self {
          $(
            $name::$variant(s) => s,
          )*
        }
      }
    }
  }
}

ast_node! {
  /// The entire jsonnet source file. Includes the entire root expression.
  pub struct SourceFile(SOURCE_FILE) {
    root: Expr,
  }
}

ast_node! {
  /// An error expressions: `error "foo"`.
  pub struct ErrorExpr(ERROR_EXPR) {
    error_token: {error},
    expr: Expr,
  }
}

ast_node! {
  /// A string expression: `"foo"`.
  pub struct StringExpr(STRING_EXPR) {
    token: (String),
  }
}

ast_node! {
  /// An assert expression: `assert "foo" : "message" ; <rest>`.
  pub struct AssertExpr(ASSERT_EXPR) {
    assert_token: {assert},
    cond: (COND => Expr),
    colon_token: {:},
    message: (ASSERT_MESSAGE => Expr),
    semicolon_token: {;},
    rest: (REST => Expr),
  }
}

ast_node! {
  /// An if expression.
  pub struct IfExpr(IF_EXPR) {
    if_token: {if},
    cond: (COND => Expr),
    then_token: {then},
    true_branch: (TRUE_BRANCH => Expr),
    else_token: {else},
    false_branch: (FALSE_BRANCH => Expr),
  }
}

ast_node! {
  /// A function expression.
  pub struct FunctionExpr(FUNCTION_EXPR) {
    function_token: {function},
    params: ParamList,
    body: Expr,
  }
}

ast_node! {
  /// Function parameter list.
  pub struct ParamList(PARAM_LIST) {
    l_paren_token: {'('},
    params: [Param],
    r_paren_token: {')'},
  }
}

ast_node! {
  /// Function parameter.
  pub struct Param(PARAM) {
    name: (Ident),
    assign_token: {=},
    default_value: Expr,
  }
}

ast_node! {
  /// Positional argument.
  pub struct PositionalArg(POSITIONAL_ARGUMENT) {
    expr: Expr,
  }
}

ast_node! {
  /// Named argument.
  pub struct NamedArg(NAMED_ARGUMENT) {
    name: (Ident),
    assign_token: {=},
    expr: Expr,
  }
}

ast_kind! {
  /// Function argument, either named or positional.
  pub enum Arg {
    Positional(PositionalArg),
    Named(NamedArg),
  }
}

ast_node! {
  /// Object field assert.
  pub struct AssertObjField(ASSERT_OBJ_FIELD) {
    assert_token: {assert},
    cond: (COND => Expr),
    colon_token: {:},
    message: (ASSERT_MESSAGE => Expr),
  }
}

ast_node! {
  /// Object ident field name.
  pub struct IdentFieldName(IDENT_FIELD_NAME) {
    name: (Ident),
  }
}

ast_node! {
  /// Object string field name.
  pub struct StringFieldName(STRING_FIELD_NAME) {
    name: (String),
  }
}

ast_node! {
  /// Object computed field name.
  pub struct ComputedFieldName(COMPUTED_FIELD_NAME) {
    l_brack_token: {'['},
    expr: Expr,
    r_brack_token: {']'},
  }
}

ast_kind! {
  /// Object field name.
  pub enum ObjectFieldName {
    Ident(IdentFieldName),
    String(StringFieldName),
    Computed(ComputedFieldName),
  }
}

op_kind! {
  /// Object field assignment operator
  pub enum ObjectFieldAssignmentOp {
    Default(:),
    Hidden(::),
    Visible(:::),
    MergeDefault(+:),
    MergeHidden(+::),
    MergeVisible(+:::),
  }
}

ast_node! {
  /// Object field value.
  pub struct ValueObjField(VALUE_OBJ_FIELD) {
    name: ObjectFieldName,
    op: (ObjectFieldAssignmentOp),
    expr: Expr,
  }
}

ast_node! {
  /// Object field function.
  pub struct FunctionObjField(FUNCTION_OBJ_FIELD) {
    name: ObjectFieldName,
    params: ParamList,
    op: (ObjectFieldAssignmentOp),
    expr: Expr,
  }
}

ast_node! {
  /// Object field local.
  pub struct LocalObjField(LOCAL_OBJ_FIELD) {
    local_token: {local},
    bind: Bind,
  }
}

ast_kind! {
  /// Object field.
  pub enum ObjectField {
    Assert(AssertObjField),
    Function(FunctionObjField),
    Local(LocalObjField),
    Value(ValueObjField),
  }
}

ast_node! {
  /// Value binding.
  pub struct ValueBind(VALUE_BIND) {
    name: (Ident),
    assign_token: {=},
    expr: Expr,
  }
}

ast_node! {
  /// Function binding.
  pub struct FunctionBind(FUNCTION_BIND) {
    name: (Ident),
    params: ParamList,
    assign_token: {=},
    expr: Expr,
  }
}

ast_kind! {
  /// Binding.
  pub enum Bind {
    Function(FunctionBind),
    Value(ValueBind),
  }
}

ast_node! {
  /// Import expression.
  pub struct ImportExpr(IMPORT_EXPR) {
    import_token: {import},
    // TODO: Different token type? (block_string not allowed here)
    value: (String),
  }
}

ast_node! {
  /// Importstr expression.
  pub struct ImportStrExpr(IMPORTSTR_EXPR) {
    importstr_token: {importstr},
    // TODO: Different token type? (block_string not allowed here)
    value: (String),
  }
}

ast_node! {
  /// A local expression.
  pub struct LocalExpr(LOCAL_EXPR) {
    local_token: {local},
    binds: BindList,
    semicolon_token: {;},
    rest: (REST => Expr),
  }
}

ast_node! {
  /// A binding list.
  pub struct BindList(BIND_LIST) {
    bindings: [Bind],
  }
}

op_kind! {
  /// Unary operator
  pub enum UnaryOp {
    Plus(+),
    Minus(-),
    Not(!),
    BitNeg(~),
  }
}

ast_node! {
  /// An unary expression.
  pub struct UnaryExpr(UNARY_EXPR) {
    op: (UnaryOp),
    expr: Expr,
  }
}

op_kind! {
  /// Unary operator
  pub enum BinaryOp {
    Mult(*),
    Div(/),
    Modulo(%),
    Plus(+),
    Minus(-),
    ShiftL(<<),
    ShiftR(>>),
    GreaterThan(>),
    GreaterThanOrEquals(>=),
    LessThan(<),
    LessThanOrEquals(<=),
    InObject(in),
    Equals(==),
    NotEquals(!=),
    BitAnd(&),
    BitXor(^),
    BitOr(|),
    And(&&),
    Or(||),
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get lhs & rhs
  /// A binary expression.
  pub struct BinaryExpr(BINARY_EXPR) {
    op: (BinaryOp),
  }
}

impl BinaryExpr {
  pub fn lhs(&self) -> Option<Expr> {
    support::children(&self.syntax).next()
  }

  pub fn rhs(&self) -> Option<Expr> {
    support::children(&self.syntax).nth(1)
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// A slice expression.
  pub struct SliceExpr(SLICE_EXPR) {
    target: Expr,
    l_brack_token: {'['},
    from_expr: (SLICE_FROM => Expr),
    to_expr: (SLICE_TO => Expr),
    step_expr: (SLICE_STEP => Expr),
    r_brack_token: {']'},
  }
}

ast_node! {
  /// A computed field access expression.
  pub struct ComputedFieldAccessExpr(COMPUTED_FIELD_ACCESS_EXPR) {
    l_brack_token: {'['},
    r_brack_token: {']'},
  }
}

impl ComputedFieldAccessExpr {
  pub fn target(&self) -> Option<Expr> {
    support::children(&self.syntax).next()
  }

  pub fn expr(&self) -> Option<Expr> {
    support::children(&self.syntax).nth(1)
  }
}

ast_node! {
  /// A identifier field access expression.
  pub struct IdentFieldAccessExpr(IDENT_FIELD_ACCESS_EXPR) {
    target: Expr,
    dot_token: {.},
    field_name: (Ident),
  }
}

ast_node! {
  /// An apply expression.
  pub struct ApplyExpr(APPLY_EXPR) {
    target: Expr,
    args: ArgList,
    tailstrict_token: {tailstrict},
  }
}

ast_node! {
  /// An argument list.
  pub struct ArgList(ARG_LIST) {
    l_paren_token: {'('},
    args: [Arg],
    r_paren_token: {')'},
  }
}

ast_node! {
  /// Object apply expression.
  pub struct ObjApplyExpr(OBJECT_APPLY_EXPR) {}
}

impl ObjApplyExpr {
  pub fn target(&self) -> Option<Expr> {
    support::children(&self.syntax).next()
  }

  // TODO: This should not be Expr, but a subset of Exprs
  pub fn expr(&self) -> Option<Expr> {
    support::children(&self.syntax).nth(1)
  }
}

ast_node! {
  /// In-super expression.
  pub struct InSuperExpr(IN_SUPER_EXPR) {
    expr: Expr,
    in_token: {in},
    super_token: {super},
  }
}

ast_node! {
  /// Group expression.
  pub struct GroupExpr(GROUP_EXPR) {
    l_paren_token: {'('},
    expr: Expr,
    r_paren_token: {')'},
  }
}

ast_node! {
  /// Null expression.
  pub struct NullExpr(NULL_EXPR) {
    null_token: {null},
  }
}

ast_node! {
  /// True expression.
  pub struct TrueExpr(TRUE_EXPR) {
    true_token: {true},
  }
}

ast_node! {
  /// False expression.
  pub struct FalseExpr(FALSE_EXPR) {
    false_token: {false},
  }
}

ast_node! {
  /// Self expression.
  pub struct SelfExpr(SELF_EXPR) {
    self_token: {self},
  }
}

ast_node! {
  /// Root object expression.
  pub struct RootObjExpr(ROOT_EXPR) {
    root_token: {$},
  }
}

ast_node! {
  /// Number expression.
  pub struct NumberExpr(NUMBER_EXPR) {
    number_token: (Number),
  }
}

ast_node! {
  /// Ident expression.
  pub struct IdentExpr(IDENT_EXPR) {
    ident_token: (Ident),
  }
}

ast_node! {
  /// Super field expression.
  pub struct SuperFieldExpr(SUPER_FIELD_EXPR) {
    super_token: {super},
    dot_token: {.},
    field_name: (Ident),
  }
}

ast_node! {
  /// Super computed field expression.
  pub struct SuperComputedExpr(SUPER_COMPUTED_EXPR) {
    super_token: {super},
    l_brack_token: {'['},
    expr: Expr,
    r_brack_token: {']'},
  }
}

ast_node! {
  /// Array literal expression.
  pub struct ArrayExpr(ARRAY_EXPR) {
    l_brack_token: {'['},
    items: [Expr],
    r_brack_token: {']'},
  }
}

ast_node! {
  /// For spec.
  pub struct ForCompSpec(FOR_COMP_SPEC) {
    for_token: {for},
    id: (Ident),
    in_token: {in},
    expr: Expr,
  }
}

ast_node! {
  /// If spec.
  pub struct IfCompSpec(IF_COMP_SPEC) {
    if_token: {if},
    expr: Expr,
  }
}

ast_kind! {
  /// Comprehension spec part.
  pub enum CompSpec {
    For(ForCompSpec),
    If(IfCompSpec),
  }
}

ast_node! {
  /// Comprehension spec list.
  pub struct CompSpecList(COMP_SPEC_LIST) {
    comp_specs: [CompSpec],
  }
}

ast_node! {
  /// Array comprehension expression.
  pub struct ArrayCompExpr(ARRAY_COMP_EXPR) {
    l_brack_token: {'['},
    expr: Expr,
    comma_token: {,},
    specs: CompSpecList,
    r_brack_token: {']'},
  }
}

ast_node! {
  /// Object expression.
  pub struct ObjectExpr(OBJECT_EXPR) {
    l_curly_token: {'{'},
    fields: [ObjectField],
    r_curly_token: {'}'},
  }
}

ast_node! {
  /// Object comprehension expression.
  pub struct ObjectCompExpr(OBJECT_COMP_EXPR) {
    l_curly_token: {'{'},
    locals: [LocalObjField],
    field: ValueObjField,
    specs: CompSpecList,
    r_curly_token: {'}'},
  }
}

ast_kind! {
  /// Expression.
  pub enum Expr {
    Apply(ApplyExpr),
    Array(ArrayExpr),
    ArrayComp(ArrayCompExpr),
    Assert(AssertExpr),
    Binary(BinaryExpr),
    ComputedFieldAccess(ComputedFieldAccessExpr),
    Error(ErrorExpr),
    False(FalseExpr),
    IdentFieldAccess(IdentFieldAccessExpr),
    Function(FunctionExpr),
    Group(GroupExpr),
    Ident(IdentExpr),
    If(IfExpr),
    Import(ImportExpr),
    ImportStr(ImportStrExpr),
    InSuper(InSuperExpr),
    Local(LocalExpr),
    Null(NullExpr),
    Number(NumberExpr),
    Object(ObjectExpr),
    ObjectApply(ObjApplyExpr),
    ObjectComp(ObjectCompExpr),
    RootObj(RootObjExpr),
    SelfValue(SelfExpr),
    Slice(SliceExpr),
    String(StringExpr),
    SuperField(SuperFieldExpr),
    SuperComputed(SuperComputedExpr),
    True(TrueExpr),
    Unary(UnaryExpr),
  }
}
