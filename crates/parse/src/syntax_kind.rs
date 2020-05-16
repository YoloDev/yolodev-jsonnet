macro_rules! define_syntax_kind {
  (@ ($name:ident) [$($acc:tt)*] [$($m_acc:tt)*]) => {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    #[repr(u16)]
    #[allow(non_camel_case_types)]
    pub enum $name {
      $($acc)*
    }

    #[macro_export]
    macro_rules! T {
      $($m_acc)*
    }
  };

  (@ $ctx:tt [$($acc:tt)*] $m_acc:tt $name:ident #hidden $($rest:tt)*) => {
    define_syntax_kind! {
      @ $ctx [$($acc)* #[doc(hidden)] $name,] $m_acc $($rest)*
    }
  };

  (@ $ctx:tt [$($acc:tt)*] $m_acc:tt $name:ident #[$($m:tt)*] $($rest:tt)*) => {
    define_syntax_kind! {
      @ $ctx [$($acc)* #[$($m)*] $name,] $m_acc $($rest)*
    }
  };

  (@ $ctx:tt [$($acc:tt)*] [$($m_acc:tt)*] $name:ident [$($tok:tt)*] #[$($m:tt)*] $($rest:tt)*) => {
    define_syntax_kind! {
      @ $ctx [$($acc)* #[$($m)*] $name,] [$($m_acc)* [$($tok)*] => { $crate::SyntaxKind::$name };] $($rest)*
    }
  };

  (pub enum $name:ident { $($body:tt)* }) => {
    define_syntax_kind! {
      @ ($name) [] [] $($body)*
    }
  };
}

define_syntax_kind! {
  pub enum SyntaxKind {
    // special
    TOMBSTONE                   #hidden
    EOF                         #hidden

    // operators
    NOT_OP                      [!] /// `!`
    ASSIGN_OP                   [=] /// `=`
    COLON_OP                    [:] /// `:`
    DOUBLE_COLON_OP             [::] /// `::`
    TRIPLE_COLON_OP             [:::] /// `:::`
    PLUS_COLON_OP               [+:] /// `+:`
    PLUS_DOUBLE_COLON_OP        [+::] /// `+::`
    PLUS_TRIPLE_COLON_OP        [+:::] /// `+:::`
    MUL_OP                      [*] /// `*`
    DIV_OP                      [/] /// `/`
    MOD_OP                      [%] /// `%`
    PLUS_OP                     [+] /// `+`
    MINUS_OP                    [-] /// `-`
    SHIFT_LEFT_OP               [<<] /// `<<`
    SHIFT_RIGHT_OP              [>>] /// `>>`
    LESS_THAN_OP                [<] /// `<`
    GREATER_THAN_OP             [>] /// `>`
    LESS_THAN_OR_EQUAL_OP       [<=] /// `<=`
    GREATER_THAN_OR_EQUAL_OP    [>=] /// `>=`
    EQUAL_OP                    [==] /// `==`
    NOT_EQUAL_OP                [!=] /// `!=`
    BIT_AND_OP                  [&] /// `&`
    BIT_XOR_OP                  [^] /// `^`
    BIT_OR_OP                   [|] /// `|`
    AND_OP                      [&&] /// `&&`
    OR_OP                       [||] /// `||`
    BIT_NEG_OP                  [~] /// `~`

    // keywords
    ASSERT_KW                   [assert] /// `assert`
    ELSE_KW                     [else] /// `else`
    ERROR_KW                    [error] /// `error`
    FALSE_KW                    [false] /// `false`
    FOR_KW                      [for] /// `for`
    FUNCTION_KW                 [function] /// `function`
    IF_KW                       [if] /// `if`
    IMPORT_KW                   [import] /// `import`
    IMPORTSTR_KW                [importstr] /// `importstr`
    IN_KW                       [in] /// `in`
    LOCAL_KW                    [local] /// `local`
    NULL_KW                     [null] /// `null`
    TAILSTRICT_KW               [tailstrict] /// `tailstrict`
    THEN_KW                     [then] /// `then`
    SELF_KW                     [self] /// `self`
    SUPER_KW                    [super] /// `super`
    TRUE_KW                     [true] /// `true`

    // symbols
    L_PAREN                     ['('] /// `(`
    R_PAREN                     [')'] /// `)`
    L_CURLY                     ['{'] /// `{`
    R_CURLY                     ['}'] /// `}`
    L_BRACK                     ['['] /// `[`
    R_BRACK                     [']'] /// `]`
    COMMA                       [,] /// `,`
    DOT                         [.] /// `.`
    SEMICOLON                   [;] /// `;`
    DOLLAR                      [$] /// `$`

    // other tokens
    IDENT                       /// Identifier
    NUMBER                      /// Literal number
    STRING                      /// Literal string
    WHITESPACE                  /// Whitespace
    COMMENT                     /// Comment
    SHEBANG                     [#!] /// `#!`
    PARSE_ERR                   /// Error syntax (either token or compound)

    // expressions
    APPLY_EXPR                  /// Apply expression
    ARRAY_COMP_EXPR             /// ArrayComp expression
    ARRAY_EXPR                  /// Array expression
    ASSERT_EXPR                 /// Assert expression
    BINARY_EXPR                 /// Binary expression
    COMPUTED_FIELD_ACCESS_EXPR  /// ComputedFieldAccess expression
    ERROR_EXPR                  /// Error expression
    FALSE_EXPR                  /// False expression
    FUNCTION_EXPR               /// Function expression
    GROUP_EXPR                  /// Group expression
    IDENT_EXPR                  /// Ident expression
    IDENT_FIELD_ACCESS_EXPR     /// FieldAccess expression
    IF_EXPR                     /// If expression
    IMPORT_EXPR                 /// Import expression
    IMPORTSTR_EXPR              /// ImportStr expression
    IN_SUPER_EXPR               /// InSuper expression
    LOCAL_EXPR                  /// Local expression
    NULL_EXPR                   /// Null expression
    NUMBER_EXPR                 /// Number expression
    OBJECT_APPLY_EXPR           /// ObjectApply expression
    OBJECT_COMP_EXPR            /// ObjectComp expression
    OBJECT_EXPR                 /// Object expression
    ROOT_EXPR                   /// Root expression
    SELF_EXPR                   /// Self expression
    SLICE_EXPR                  /// Slice expression
    STRING_EXPR                 /// String expression
    SUPER_COMPUTED_EXPR         /// Super computed expression
    SUPER_FIELD_EXPR            /// Super field expression
    TRUE_EXPR                   /// True expression
    UNARY_EXPR                  /// Unary expression

    // object fields
    ASSERT_OBJ_FIELD            /// Assert object field
    FUNCTION_OBJ_FIELD          /// Function object field
    LOCAL_OBJ_FIELD             /// Local object field
    VALUE_OBJ_FIELD             /// Value object field

    // field names
    IDENT_FIELD_NAME            /// Identifier field name
    STRING_FIELD_NAME           /// String field name
    COMPUTED_FIELD_NAME         /// Computed field name

    // function arguments
    POSITIONAL_ARGUMENT         /// Positional argument
    NAMED_ARGUMENT              /// Named argument
    ARG_LIST                    /// Argument list

    // completion specs
    FOR_COMP_SPEC               /// For spec (part of object/array composition)
    IF_COMP_SPEC                /// If spec (part of object/array composition)

    // other nodes
    OBJCOMP_FIELD               /// ObjectComp field
    FUNCTION_BIND               /// Function binding
    VALUE_BIND                  /// Value binding
    PARAM_LIST                  /// Function parameter list
    PARAM                       /// Function parameter
    SOURCE_FILE                 /// Source file

    // special
    __LAST                      #hidden
  }
}

use SyntaxKind::*;

impl SyntaxKind {
  pub fn is_op(self) -> bool {
    match self {
      NOT_OP
      | ASSIGN_OP
      | COLON_OP
      | DOUBLE_COLON_OP
      | TRIPLE_COLON_OP
      | PLUS_COLON_OP
      | PLUS_DOUBLE_COLON_OP
      | PLUS_TRIPLE_COLON_OP
      | MUL_OP
      | DIV_OP
      | MOD_OP
      | PLUS_OP
      | MINUS_OP
      | SHIFT_LEFT_OP
      | SHIFT_RIGHT_OP
      | LESS_THAN_OP
      | GREATER_THAN_OP
      | LESS_THAN_OR_EQUAL_OP
      | GREATER_THAN_OR_EQUAL_OP
      | EQUAL_OP
      | NOT_EQUAL_OP
      | BIT_AND_OP
      | BIT_XOR_OP
      | BIT_OR_OP
      | AND_OP
      | OR_OP
      | BIT_NEG_OP => true,
      _ => false,
    }
  }

  pub fn is_kw(self) -> bool {
    match self {
      ASSERT_KW | ELSE_KW | ERROR_KW | FALSE_KW | FOR_KW | FUNCTION_KW | IF_KW | IMPORT_KW
      | IMPORTSTR_KW | IN_KW | LOCAL_KW | NULL_KW | TAILSTRICT_KW | THEN_KW | SELF_KW
      | SUPER_KW | TRUE_KW => true,
      _ => false,
    }
  }

  pub fn is_sym(self) -> bool {
    match self {
      L_PAREN | R_PAREN | L_CURLY | R_CURLY | L_BRACK | R_BRACK | COMMA | DOT | SEMICOLON
      | DOLLAR => true,
      _ => false,
    }
  }

  pub fn from_kw(ident: &str) -> Option<SyntaxKind> {
    match ident {
      "assert" => Some(ASSERT_KW),
      "else" => Some(ELSE_KW),
      "error" => Some(ERROR_KW),
      "false" => Some(FALSE_KW),
      "for" => Some(FOR_KW),
      "function" => Some(FUNCTION_KW),
      "if" => Some(IF_KW),
      "import" => Some(IMPORT_KW),
      "importstr" => Some(IMPORTSTR_KW),
      "in" => Some(IN_KW),
      "local" => Some(LOCAL_KW),
      "null" => Some(NULL_KW),
      "tailstrict" => Some(TAILSTRICT_KW),
      "then" => Some(THEN_KW),
      "self" => Some(SELF_KW),
      "super" => Some(SUPER_KW),
      "true" => Some(TRUE_KW),
      _ => None,
    }
  }

  pub fn from_op(op: &str) -> Option<SyntaxKind> {
    match op {
      "!" => Some(NOT_OP),
      "=" => Some(ASSIGN_OP),
      ":" => Some(COLON_OP),
      "::" => Some(DOUBLE_COLON_OP),
      ":::" => Some(TRIPLE_COLON_OP),
      "+:" => Some(PLUS_COLON_OP),
      "+::" => Some(PLUS_DOUBLE_COLON_OP),
      "+:::" => Some(PLUS_TRIPLE_COLON_OP),
      "*" => Some(MUL_OP),
      "/" => Some(DIV_OP),
      "%" => Some(MOD_OP),
      "+" => Some(PLUS_OP),
      "-" => Some(MINUS_OP),
      "<<" => Some(SHIFT_LEFT_OP),
      ">>" => Some(SHIFT_RIGHT_OP),
      "<" => Some(LESS_THAN_OP),
      ">" => Some(GREATER_THAN_OP),
      "<=" => Some(LESS_THAN_OR_EQUAL_OP),
      ">=" => Some(GREATER_THAN_OR_EQUAL_OP),
      "==" => Some(EQUAL_OP),
      "!=" => Some(NOT_EQUAL_OP),
      "&" => Some(BIT_AND_OP),
      "^" => Some(BIT_XOR_OP),
      "|" => Some(BIT_OR_OP),
      "&&" => Some(AND_OP),
      "||" => Some(OR_OP),
      "~" => Some(BIT_NEG_OP),
      _ => None,
    }
  }

  pub fn from_sym(sym: &str) -> Option<SyntaxKind> {
    match sym {
      "(" => Some(L_PAREN),
      ")" => Some(R_PAREN),
      "{" => Some(L_CURLY),
      "}" => Some(R_CURLY),
      "[" => Some(L_BRACK),
      "]" => Some(R_BRACK),
      "," => Some(COMMA),
      "." => Some(DOT),
      ";" => Some(SEMICOLON),
      "$" => Some(DOLLAR),
      _ => None,
    }
  }

  pub fn is_trivia(self) -> bool {
    match self {
      WHITESPACE | COMMENT => true,
      _ => false,
    }
  }
}

impl From<u16> for SyntaxKind {
  fn from(d: u16) -> SyntaxKind {
    assert!(d <= (SyntaxKind::__LAST as u16));
    unsafe { std::mem::transmute::<u16, SyntaxKind>(d) }
  }
}

impl From<SyntaxKind> for u16 {
  fn from(k: SyntaxKind) -> u16 {
    k as u16
  }
}
