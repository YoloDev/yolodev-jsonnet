use crate::{
  ast::{self, support, AstChildren, AstNode},
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
}

#[cfg(feature = "node-description")]
struct DescriptionList<T: ast::AstDescribe + AstNode>(AstChildren<T>);

#[cfg(feature = "node-description")]
impl<T: ast::AstDescribe + AstNode + 'static> Iterator for DescriptionList<T> {
  type Item = Box<dyn ast::AstDescribe>;

  fn next(&mut self) -> Option<Self::Item> {
    match self.0.next() {
      None => None,
      Some(n) => Some(Box::new(n)),
    }
  }
}

#[cfg(feature = "node-description")]
macro_rules! ast_node_describe_members {
  ($node:ident, $current:ident, $idx:expr, $name:ident,) => {};

  ($node:ident, $current:ident, $idx:expr, $name:ident, [$fld:ident, $node_type:ident] $($rest:tt)*) => {
    if *$current <= $idx {
      *$current = $idx + 1;
      if let Some(node) = $name::$fld($node) {
        return Some((stringify!($fld), Some(ast::AstDescription::Node(Box::from(node)))));
      } else {
        return Some((stringify!($fld), None));
      }
    }

    ast_node_describe_members! {
      $node,
      $current,
      $idx + 1,
      $name,
      $($rest)*
    }
  };

  ($node:ident, $current:ident, $idx:expr, $name:ident, [$fld:ident, [$node_type:ident]] $($rest:tt)*) => {
    if *$current <= $idx {
      *$current = $idx + 1;
      let list = $name::$fld($node);
      return Some((stringify!($fld), Some(ast::AstDescription::List(Box::from(DescriptionList(list))))));
    }

    ast_node_describe_members! {
      $node,
      $current,
      $idx + 1,
      $name,
      $($rest)*
    }
  };

  ($node:ident, $current:ident, $idx:expr, $name:ident, [$fld:ident, {$($tok:tt)*}] $($rest:tt)*) => {
    ast_node_describe_members! {
      $node,
      $current,
      $idx + 1,
      $name,
      $($rest)*
    }
  };

  ($node:ident, $current:ident, $idx:expr, $name:ident, [$fld:ident, ( $( {$($tok:tt)*} )|+ )] $($rest:tt)*) => {
    ast_node_describe_members! {
      $node,
      $current,
      $idx + 1,
      $name,
      $($rest)*
    }
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

    #[cfg(feature = "node-description")]
    impl ast::AstDescribe for $name {
      fn describe_kind(&self) -> &str {
        stringify!($name)
      }

      fn describe_span(&self) -> (u32, u32) {
        let range = self.syntax.text_range();
        (range.start().into(), range.end().into())
      }

      fn describe_children<'a>(&'a self) -> Box<dyn Iterator<Item = (&'static str, Option<ast::AstDescription>)> + 'a> {
        struct DescribeChildren<'a>(&'a $name, u8);

        impl<'a> Iterator for DescribeChildren<'a> {
          type Item = (&'static str, Option<ast::AstDescription>);

          fn next(&mut self) -> Option<Self::Item> {
            #[allow(unused)]
            let node = &self.0;

            #[allow(unused)]
            let current = &mut self.1;

            ast_node_describe_members!{
              node,
              current,
              0,
              $name,
              $(
                [$fld, $t]
              )*
            }

            None
          }
        }

        Box::from(DescribeChildren(self, 0))
      }
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

    #[cfg(feature = "node-description")]
    impl ast::AstDescribe for $name {
      fn describe_kind(&self) -> &str {
        match self {
          $(
            $name::$variant(it) => ast::AstDescribe::describe_kind(it),
          )*
        }
      }

      fn describe_span(&self) -> (u32, u32) {
        match self {
          $(
            $name::$variant(it) => ast::AstDescribe::describe_span(it),
          )*
        }
      }

      fn describe_children<'a>(&'a self) -> Box<dyn Iterator<Item = (&'static str, Option<ast::AstDescription>)> + 'a> {
        match self {
          $(
            $name::$variant(it) => ast::AstDescribe::describe_children(it),
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
  /// The remainder on a statement-like expression.
  pub struct Rest(REST) {
    expr: Expr,
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
    token: ( {STRING} | {VERBATIM_STRING} | {BLOCK_STRING} ),
  }
}

ast_node! {
  /// An assert expression: `assert "foo" : "message" ; <rest>`.
  pub struct AssertExpr(ASSERT_EXPR) {
    assert_token: {assert},
    cond: Cond,
    colon_token: {:},
    message: AssertMessage,
    semicolon_token: {;},
    rest: Rest,
  }
}

ast_node! {
  /// The condition part of an assert expression or member.
  pub struct Cond(COND) {
    expr: Expr,
  }
}

ast_node! {
  /// The message part of an assert expression or member.
  pub struct AssertMessage(ASSERT_MESSAGE) {
    expr: Expr,
  }
}

ast_node! {
  /// An if expression.
  pub struct IfExpr(IF_EXPR) {
    if_token: {if},
    cond: Cond,
    then_token: {then},
    true_branch: TrueBranch,
    else_token: {else},
    false_branch: FalseBranch,
  }
}

ast_node! {
  /// The true branch in an if expression.
  pub struct TrueBranch(TRUE_BRANCH) {
    expr: Expr,
  }
}

ast_node! {
  /// The true branch in an if expression.
  pub struct FalseBranch(FALSE_BRANCH) {
    expr: Expr,
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
    name: {IDENT},
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
    name: {IDENT},
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
    cond: Cond,
    colon_token: {:},
    message: AssertMessage,
  }
}

ast_node! {
  /// Object ident field name.
  pub struct IdentFieldName(IDENT_FIELD_NAME) {
    name: {IDENT},
  }
}

ast_node! {
  /// Object string field name.
  pub struct StringFieldName(STRING_FIELD_NAME) {
    name: ( {STRING} | {VERBATIM_STRING} | {BLOCK_STRING} ),
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

ast_node! {
  /// Object field value.
  pub struct ValueObjField(VALUE_OBJ_FIELD) {
    name: ObjectFieldName,
    op: ( {:} | {::} | {:::} | {+:} | {+::} | {+:::} ),
    expr: Expr,
  }
}

ast_node! {
  /// Object field function.
  pub struct FunctionObjField(FUNCTION_OBJ_FIELD) {
    name: ObjectFieldName,
    params: ParamList,
    op: ( {:} | {::} | {:::} | {+:} | {+::} | {+:::} ),
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
    name: {IDENT},
    assign_token: {=},
    expr: Expr,
  }
}

ast_node! {
  /// Function binding.
  pub struct FunctionBind(FUNCTION_BIND) {
    name: {IDENT},
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
    value: ( {STRING} | {VERBATIM_STRING} ),
  }
}

ast_node! {
  /// Importstr expression.
  pub struct ImportStrExpr(IMPORTSTR_EXPR) {
    importstr_token: {importstr},
    value: ( {STRING} | {VERBATIM_STRING} ),
  }
}

ast_node! {
  /// A local expression.
  pub struct LocalExpr(LOCAL_EXPR) {
    local_token: {local},
    binds: BindList,
    semicolon_token: {;},
    rest: Rest,
  }
}

ast_node! {
  /// A binding list.
  pub struct BindList(BIND_LIST) {
    bindings: [Bind],
  }
}

ast_node! {
  /// An unary expression.
  pub struct UnaryExpr(UNARY_EXPR) {
    op: ( {+} | {-} | {!} | {~} ),
    expr: Expr,
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get lhs & rhs
  /// A binary expression.
  pub struct BinaryExpr(BINARY_EXPR) {
    op: ( {*} | {/} | {%} | {+} | {-} | {<<} | {>>} | {>} | {>=} | {<} | {<=} | {in} | {==} | {!=} | {&} | {^} | {|} | {&&} | {||} ),
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// A slice expression.
  pub struct SliceExpr(SLICE_EXPR) {
    l_brack_token: {'['},
    r_brack_token: {']'},
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// A computed field access expression.
  pub struct ComputedFieldAccessExpr(COMPUTED_FIELD_ACCESS_EXPR) {
    l_brack_token: {'['},
    r_brack_token: {']'},
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// A identifier field access expression.
  pub struct IdentFieldAccessExpr(IDENT_FIELD_ACCESS_EXPR) {
    dot_token: {.},
    field_name: {IDENT},
  }
}

ast_node! {
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// An apply expression.
  pub struct ApplyExpr(APPLY_EXPR) {
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
  // TODO: this one probably needs some manual impls to get the slice expressions
  /// Object apply expression.
  pub struct ObjApplyExpr(OBJECT_APPLY_EXPR) {}
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
    number_token: {NUMBER},
  }
}

ast_node! {
  /// Ident expression.
  pub struct IdentExpr(IDENT_EXPR) {
    ident_token: {IDENT},
  }
}

ast_node! {
  /// Super field expression.
  pub struct SuperFieldExpr(SUPER_FIELD_EXPR) {
    super_token: {super},
    dot_token: {.},
  }
}

ast_node! {
  /// Super computed field expression.
  pub struct SuperComputedExpr(SUPER_COMPUTED_EXPR) {
    super_token: {super},
    l_brack_token: {'['},
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
    id: {IDENT},
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
    // TODO: expr here needs to be nested in a named group
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
