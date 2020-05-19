#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::collections::VecDeque;
use logos::Logos;

mod op;
mod str_block;

use op::{lex_operator, Operator};
use str_block::{lex_str_block, StringBlockToken};

pub mod unescape;

#[derive(Logos, Debug, PartialEq)]
enum RawToken {
  #[token("assert")]
  KeywordAssert,

  #[token("else")]
  KeywordElse,

  #[token("error")]
  KeywordError,

  #[token("false")]
  KeywordFalse,

  #[token("for")]
  KeywordFor,

  #[token("function")]
  KeywordFunction,

  #[token("if")]
  KeywordIf,

  #[token("import")]
  KeywordImport,

  #[token("importstr")]
  KeywordImportStr,

  #[token("in")]
  KeywordIn,

  #[token("local")]
  KeywordLocal,

  #[token("null")]
  KeywordNull,

  #[token("tailstrict")]
  KeywordTailStrict,

  #[token("then")]
  KeywordThen,

  #[token("self")]
  KeywordSelf,

  #[token("super")]
  KeywordSuper,

  #[token("true")]
  KeywordTrue,

  #[regex(r"[_a-zA-Z][_a-zA-Z0-9]*")]
  Ident,

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?")]
  Number,

  #[regex(r"(?:0|[1-9][0-9]*)\.[^0-9]")]
  ErrorNumJunkAfterDecimalPoint,

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?[eE][^+\-0-9]")]
  ErrorNumJunkAfterExponent,

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?[eE][+-][^0-9]")]
  ErrorNumJunkAfterExponentSign,

  #[token("{")]
  SymbolLeftBrace,

  #[token("}")]
  SymbolRightBrace,

  #[token("[")]
  SymbolLeftBracket,

  #[token("]")]
  SymbolRightBracket,

  #[token(",")]
  SymbolComma,

  #[token(".")]
  SymbolDot,

  #[token("(")]
  SymbolLeftParen,

  #[token(")")]
  SymbolRightParen,

  #[token(";")]
  SymbolSemi,

  #[token("$")]
  SymbolDollar,

  #[regex(r"[!\$:~\+\-&\|\^=<>\*/%]+", lex_operator)]
  Op(Operator),

  #[regex("\"(?s:[^\"\\\\]|\\\\.)*\"")]
  StringDoubleQuoted,

  #[regex("'(?s:[^'\\\\]|\\\\.)*'")]
  StringSingleQuoted,

  #[regex("@\"(?:[^\"]|\"\")*\"")]
  StringDoubleVerbatim,

  #[regex("@'(?:[^']|'')*'")]
  StringSingleVerbatim,

  #[regex(r"\|\|\|", lex_str_block)]
  StringBlock(StringBlockToken),

  #[regex("\"(?s:[^\"\\\\]|\\\\.)*")]
  ErrorStringDoubleQuotedUnterminated,

  #[regex("'(?s:[^'\\\\]|\\\\.)*")]
  ErrorStringSingleQuotedUnterminated,

  #[regex("@\"(?:[^\"]|\"\")*")]
  ErrorStringDoubleVerbatimUnterminated,

  #[regex("@'(?:[^']|'')*")]
  ErrorStringSingleVerbatimUnterminated,

  #[regex("@[^\"'\\s]\\S+")]
  ErrorStringMissingQuotes,

  #[token("/*/")]
  ErrorCommentTooShort,

  #[regex(r"/\*([^*]|\*[^/])+")]
  ErrorCommentUnterminated,

  #[regex(r"[ \t\n\r]+")]
  Whitespace,

  #[regex(r"//[^\r\n]*(\r\n|\n)?")]
  SingelLineSlashComment,

  #[regex(r"#[^\r\n]*(\r\n|\n)?")]
  SingleLineHashComment,

  #[regex(r"/\*([^*]|\*[^/])*\*/")]
  MultiLineComment,

  #[error]
  Error,
}

macro_rules! token_enum {
  (
    $(#[$($enum_m:tt)*])*
    pub enum $name:ident {
      $($case:ident $(#[$($m:tt)*])*)*
    }
  ) => {
    $(#[$($enum_m)*])*
    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    pub enum $name {
      $(
        $(#[$($m)*])*
        $case,
      )*
    }
  };
}

token_enum! {
  /// Token kind.
  pub enum TokenKind {
    // keywords
    KeywordAssert                             /// `assert`
    KeywordElse                               /// `else`
    KeywordError                              /// `error`
    KeywordFalse                              /// `false`
    KeywordFor                                /// `for`
    KeywordFunction                           /// `function`
    KeywordIf                                 /// `if`
    KeywordImport                             /// `import`
    KeywordImportStr                          /// `importstr`
    KeywordIn                                 /// `in`
    KeywordLocal                              /// `local`
    KeywordNull                               /// `null`
    KeywordTailStrict                         /// `tailstrict`
    KeywordThen                               /// `then`
    KeywordSelf                               /// `self`
    KeywordSuper                              /// `super`
    KeywordTrue                               /// `true`

    // variable tokens
    Ident                                     /// identifier token
    Number                                    /// number token

    // symbols
    SymbolLeftBrace                           /// `{`
    SymbolRightBrace                          /// `}`
    SymbolLeftBracket                         /// `[`
    SymbolRightBracket                        /// `]`
    SymbolComma                               /// `,`
    SymbolDot                                 /// `.`
    SymbolLeftParen                           /// `(`
    SymbolRightParen                          /// `)`
    SymbolSemi                                /// `;`
    SymbolDollar                              /// `$`

    // operators
    OpNot                                     /// `!`
    OpAssign                                  /// `=`
    OpColon                                   /// `:`
    OpDoubleColon                             /// `::`
    OpTripleColon                             /// `:::`
    OpPlusColon                               /// `+:`
    OpPlusDoubleColon                         /// `+::`
    OpPlusTripleColon                         /// `+:::`
    OpMul                                     /// `*`
    OpDiv                                     /// `/`
    OpMod                                     /// `%`
    OpPlus                                    /// `+`
    OpMinus                                   /// `-`
    OpShiftLeft                               /// `<<`
    OpShiftRight                              /// `>>`
    OpLessThan                                /// `<`
    OpGreaterThan                             /// `>`
    OpLessThanOrEqual                         /// `<=`
    OpGreaterThanOrEqual                      /// `>=`
    OpEqual                                   /// `==`
    OpNotEqual                                /// `!=`
    OpBitAnd                                  /// `&`
    OpBitXor                                  /// `^`
    OpBitOr                                   /// `|`
    OpBitNeg                                  /// `~`
    OpAnd                                     /// `&&`
    OpOr                                      /// `||`

    // strings
    StringDoubleQuoted                        /// `"foo"`
    StringSingleQuoted                        /// `'foo'`
    StringDoubleVerbatim                      /// `@"foo"`
    StringSingleVerbatim                      /// `@'foo'`
    StringBlock                               /// ```jsonnet
                                              /// |||
                                              ///   foo
                                              /// |||
                                              /// ```

    Whitespace                                /// any whitespace
    SingelLineSlashComment                    /// `// comment`
    SingleLineHashComment                     /// `# comment`
    BlockComment                              /// `/* comment */`

    // string errors
    ErrorStringDoubleQuotedUnterminated       /// unterminated double quoted string
    ErrorStringSingleQuotedUnterminated       /// unterminated single quoted string
    ErrorStringDoubleVerbatimUnterminated     /// unterminated double quoted verbatim string
    ErrorStringSingleVerbatimUnterminated     /// unterminated single quoted verbatim string
    ErrorStringBlockUnerminated               /// unterminated block string
    ErrorStringMissingQuotes                  /// verbatim string missing quotes
    ErrorStringBlockMissingNewLine            /// block string missing newline
    ErrorStringBlockMissingTermination        /// block string missing termination sequence
    ErrorStringBlockMissingIndent             /// block string missing indentation

    // number errors
    ErrorNumJunkAfterDecimalPoint             /// unexpected character after decimal point
    ErrorNumJunkAfterExponent                 /// unexpected character after exponent
    ErrorNumJunkAfterExponentSign             /// unexpected character after exponent sign

    // comment errors
    ErrorCommentTooShort                      /// multiline comment too short (`/*/`)
    ErrorCommentUnterminated                  /// unterminated comment

    // other
    ErrorUnknownOperator                      /// unknown operator
    ErrorInvalidToken                         /// invalid token
  }
}

impl TokenKind {
  pub fn is_error(self) -> bool {
    use TokenKind::*;

    match self {
      ErrorStringDoubleQuotedUnterminated
      | ErrorStringSingleQuotedUnterminated
      | ErrorStringDoubleVerbatimUnterminated
      | ErrorStringSingleVerbatimUnterminated
      | ErrorStringBlockUnerminated
      | ErrorStringMissingQuotes
      | ErrorStringBlockMissingNewLine
      | ErrorStringBlockMissingTermination
      | ErrorStringBlockMissingIndent
      | ErrorNumJunkAfterDecimalPoint
      | ErrorNumJunkAfterExponent
      | ErrorNumJunkAfterExponentSign
      | ErrorCommentTooShort
      | ErrorCommentUnterminated
      | ErrorUnknownOperator
      | ErrorInvalidToken => true,
      _ => false,
    }
  }
}

/// A token of jsonnet source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token {
  /// The kind of token.
  pub kind: TokenKind,

  /// The token value.
  pub len: u32,
}

/// A lexer of jsonnet source.
pub struct Lexer<'a> {
  inner: logos::Lexer<'a, RawToken>,
  done: bool,
  peeked: VecDeque<Token>,
  #[cfg(debug_assertions)]
  len: u32,
}

impl<'a> Lexer<'a> {
  pub fn new(content: &'a str) -> Self {
    Self {
      inner: RawToken::lexer(content),
      done: false,
      peeked: VecDeque::new(),
      #[cfg(debug_assertions)]
      len: 0,
    }
  }

  fn read_token(&mut self) -> Option<Token> {
    if self.done {
      return None;
    }

    match self.inner.next() {
      None => {
        self.done = true;
        None
      }

      Some(raw) => {
        let len = self.inner.slice().len() as u32;

        #[cfg(debug_assertions)]
        {
          self.len += len;
          assert_eq!(self.len, self.inner.span().end as u32);
        }

        Some(self.to_token(raw, len))
      }
    }
  }

  fn to_token(&self, raw: RawToken, len: u32) -> Token {
    let kind = match raw {
      RawToken::KeywordAssert => TokenKind::KeywordAssert,
      RawToken::KeywordElse => TokenKind::KeywordElse,
      RawToken::KeywordError => TokenKind::KeywordError,
      RawToken::KeywordFalse => TokenKind::KeywordFalse,
      RawToken::KeywordFor => TokenKind::KeywordFor,
      RawToken::KeywordFunction => TokenKind::KeywordFunction,
      RawToken::KeywordIf => TokenKind::KeywordIf,
      RawToken::KeywordImport => TokenKind::KeywordImport,
      RawToken::KeywordImportStr => TokenKind::KeywordImportStr,
      RawToken::KeywordIn => TokenKind::KeywordIn,
      RawToken::KeywordLocal => TokenKind::KeywordLocal,
      RawToken::KeywordNull => TokenKind::KeywordNull,
      RawToken::KeywordTailStrict => TokenKind::KeywordTailStrict,
      RawToken::KeywordThen => TokenKind::KeywordThen,
      RawToken::KeywordSelf => TokenKind::KeywordSelf,
      RawToken::KeywordSuper => TokenKind::KeywordSuper,
      RawToken::KeywordTrue => TokenKind::KeywordTrue,
      RawToken::Ident => TokenKind::Ident,
      RawToken::Number => TokenKind::Number,
      RawToken::SymbolLeftBrace => TokenKind::SymbolLeftBrace,
      RawToken::SymbolRightBrace => TokenKind::SymbolRightBrace,
      RawToken::SymbolLeftBracket => TokenKind::SymbolLeftBracket,
      RawToken::SymbolRightBracket => TokenKind::SymbolRightBracket,
      RawToken::SymbolComma => TokenKind::SymbolComma,
      RawToken::SymbolDot => TokenKind::SymbolDot,
      RawToken::SymbolLeftParen => TokenKind::SymbolLeftParen,
      RawToken::SymbolRightParen => TokenKind::SymbolRightParen,
      RawToken::SymbolSemi => TokenKind::SymbolSemi,
      RawToken::SymbolDollar => TokenKind::SymbolDollar,
      RawToken::Op(Operator::Not) => TokenKind::OpNot,
      RawToken::Op(Operator::Assign) => TokenKind::OpAssign,
      RawToken::Op(Operator::Colon) => TokenKind::OpColon,
      RawToken::Op(Operator::DoubleColon) => TokenKind::OpDoubleColon,
      RawToken::Op(Operator::TripleColon) => TokenKind::OpTripleColon,
      RawToken::Op(Operator::PlusColon) => TokenKind::OpPlusColon,
      RawToken::Op(Operator::PlusDoubleColon) => TokenKind::OpPlusDoubleColon,
      RawToken::Op(Operator::PlusTripleColon) => TokenKind::OpPlusTripleColon,
      RawToken::Op(Operator::Mul) => TokenKind::OpMul,
      RawToken::Op(Operator::Div) => TokenKind::OpDiv,
      RawToken::Op(Operator::Mod) => TokenKind::OpMod,
      RawToken::Op(Operator::Plus) => TokenKind::OpPlus,
      RawToken::Op(Operator::Minus) => TokenKind::OpMinus,
      RawToken::Op(Operator::ShiftLeft) => TokenKind::OpShiftLeft,
      RawToken::Op(Operator::ShiftRight) => TokenKind::OpShiftRight,
      RawToken::Op(Operator::LessThan) => TokenKind::OpLessThan,
      RawToken::Op(Operator::GreaterThan) => TokenKind::OpGreaterThan,
      RawToken::Op(Operator::LessThanOrEqual) => TokenKind::OpLessThanOrEqual,
      RawToken::Op(Operator::GreaterThanOrEqual) => TokenKind::OpGreaterThanOrEqual,
      RawToken::Op(Operator::Equal) => TokenKind::OpEqual,
      RawToken::Op(Operator::NotEqual) => TokenKind::OpNotEqual,
      RawToken::Op(Operator::BitAnd) => TokenKind::OpBitAnd,
      RawToken::Op(Operator::BitXor) => TokenKind::OpBitXor,
      RawToken::Op(Operator::BitOr) => TokenKind::OpBitOr,
      RawToken::Op(Operator::BitNeg) => TokenKind::OpBitNeg,
      RawToken::Op(Operator::And) => TokenKind::OpAnd,
      RawToken::Op(Operator::Or) => TokenKind::OpOr,
      RawToken::StringDoubleQuoted => TokenKind::StringDoubleQuoted,
      RawToken::StringSingleQuoted => TokenKind::StringSingleQuoted,
      RawToken::StringDoubleVerbatim => TokenKind::StringDoubleVerbatim,
      RawToken::StringSingleVerbatim => TokenKind::StringSingleVerbatim,
      RawToken::StringBlock(StringBlockToken::Valid) => TokenKind::StringBlock,
      RawToken::Whitespace => TokenKind::Whitespace,
      RawToken::SingelLineSlashComment => TokenKind::SingelLineSlashComment,
      RawToken::SingleLineHashComment => TokenKind::SingleLineHashComment,
      RawToken::MultiLineComment => TokenKind::BlockComment,
      RawToken::ErrorNumJunkAfterDecimalPoint => TokenKind::ErrorNumJunkAfterDecimalPoint,
      RawToken::ErrorNumJunkAfterExponent => TokenKind::ErrorNumJunkAfterExponent,
      RawToken::ErrorNumJunkAfterExponentSign => TokenKind::ErrorNumJunkAfterExponentSign,
      RawToken::ErrorStringDoubleQuotedUnterminated => {
        TokenKind::ErrorStringDoubleQuotedUnterminated
      }
      RawToken::ErrorStringSingleQuotedUnterminated => {
        TokenKind::ErrorStringSingleQuotedUnterminated
      }
      RawToken::ErrorStringDoubleVerbatimUnterminated => {
        TokenKind::ErrorStringDoubleVerbatimUnterminated
      }
      RawToken::ErrorStringSingleVerbatimUnterminated => {
        TokenKind::ErrorStringSingleVerbatimUnterminated
      }
      RawToken::ErrorStringMissingQuotes => TokenKind::ErrorStringMissingQuotes,
      RawToken::StringBlock(StringBlockToken::UnexpectedEndOfString) => {
        TokenKind::ErrorStringBlockUnerminated
      }
      RawToken::StringBlock(StringBlockToken::MissingTextBlockIndent) => {
        TokenKind::ErrorStringBlockMissingIndent
      }
      RawToken::StringBlock(StringBlockToken::MissingTextBlockNewLine) => {
        TokenKind::ErrorStringBlockMissingNewLine
      }
      RawToken::StringBlock(StringBlockToken::MissingTextBlockTermination) => {
        TokenKind::ErrorStringBlockMissingTermination
      }
      RawToken::ErrorCommentTooShort => TokenKind::ErrorCommentTooShort,
      RawToken::ErrorCommentUnterminated => TokenKind::ErrorCommentUnterminated,
      RawToken::Op(Operator::Unknown) => TokenKind::ErrorUnknownOperator,
      RawToken::Error => TokenKind::ErrorInvalidToken,
    };

    Token { kind, len }
  }

  #[inline]
  pub fn peek(&mut self) -> Option<Token> {
    self.peek_nth(0)
  }

  pub fn peek_nth(&mut self, n: usize) -> Option<Token> {
    while self.peeked.len() <= n && !self.done {
      if let Some(tok) = self.read_token() {
        self.peeked.push_back(tok);
      }
    }

    self.peeked.get(n).copied()
  }
}

impl<'a> Iterator for Lexer<'a> {
  type Item = Token;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    match self.peeked.pop_front() {
      Some(v) => Some(v),
      None => self.read_token(),
    }
  }
}

/// Tokenize a string of jsonnet into a list of tokens.
pub fn tokenize<'a>(content: &'a str) -> impl Iterator<Item = Token> + 'a {
  Lexer::new(content)
}

#[cfg(test)]
mod tests {
  use super::{TokenKind::*, *};
  use test_case::test_case;

  macro_rules! test_tokens {
    ($src:expr, [$(
      $tok:expr
      $(=> $val:expr)?
    ),*$(,)?]) => {{
      let src: &str = $src;
      let mut lex = Lexer::new(src);
      #[allow(unused_mut)]
      let mut index = 0;
      #[allow(unused_mut)]
      let mut offset = 0;
      $({
        let actual = lex.next().expect(&format!("Expected token {}", index + 1));
        let expected = $tok;
        assert_eq!(actual.kind, expected, "index: {}", index);
        $(
          let val = &src[offset as usize..(offset + actual.len) as usize];
          assert_eq!(val, $val, "index: {}", index);
        )?

        index += 1;
        offset += actual.len;
      })*

      match lex.next() {
        None => (),
        Some(t) => panic!("Expected exactly {} tokens, but got {:#?} when expecting EOF", index, t),
      }
    }};
  }

  #[test]
  fn empty() {
    test_tokens!("", []);
  }

  #[test]
  fn whitespace() {
    test_tokens!("  \t\n\r\r\n", [Whitespace]);
  }

  #[test_case("{", SymbolLeftBrace)]
  #[test_case("}", SymbolRightBrace)]
  #[test_case("[", SymbolLeftBracket)]
  #[test_case("]", SymbolRightBracket)]
  #[test_case("(", SymbolLeftParen)]
  #[test_case(")", SymbolRightParen)]
  #[test_case(",", SymbolComma)]
  #[test_case(".", SymbolDot)]
  #[test_case(";", SymbolSemi)]
  #[test_case("$", SymbolDollar)]
  fn symbol(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test_case(":", OpColon)]
  #[test_case("::", OpDoubleColon)]
  #[test_case("!", OpNot)]
  #[test_case("==", OpEqual)]
  #[test_case("!=", OpNotEqual)]
  #[test_case("~", OpBitNeg)]
  #[test_case("+", OpPlus)]
  #[test_case("-", OpMinus)]
  #[test_case("*", OpMul)]
  #[test_case("/", OpDiv)]
  #[test_case("%", OpMod)]
  #[test_case("&", OpBitAnd)]
  #[test_case("|", OpBitOr)]
  #[test_case("^", OpBitXor)]
  #[test_case("=", OpAssign)]
  #[test_case("<", OpLessThan)]
  #[test_case(">", OpGreaterThan)]
  #[test_case("<=", OpLessThanOrEqual)]
  #[test_case(">=", OpGreaterThanOrEqual)]
  fn operator(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test_case("->" ; "arrow_right")]
  #[test_case("<-" ; "arrow_left")]
  #[test_case(">==|" ; "junk")]
  fn bad_op(src: &str) {
    test_tokens!(src, [ErrorUnknownOperator]);
  }

  #[test_case("1")]
  #[test_case("1.0")]
  #[test_case("0.10")]
  #[test_case("0e100")]
  #[test_case("1e100")]
  #[test_case("1.1e100")]
  #[test_case("1.2e-100")]
  #[test_case("1.3e+100")]
  fn number(src: &str) {
    test_tokens!(src, [Number]);
  }

  #[test]
  fn number_0100() {
    test_tokens!("0100", [Number=>"0", Number=>"100",]);
  }

  #[test]
  fn number_10_p_10() {
    test_tokens!(
      "10+11",
      [
        Number=>"10",
        OpPlus,
        Number=>"11",
      ]
    );
  }

  #[test_case("1.+", ErrorNumJunkAfterDecimalPoint)]
  #[test_case("1e!", ErrorNumJunkAfterExponent)]
  #[test_case("1e+!", ErrorNumJunkAfterExponentSign)]
  fn bad_number(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test_case("\"hi\"", StringDoubleQuoted ; "double_1")]
  #[test_case("\"hi\n\"", StringDoubleQuoted ; "double_2")]
  #[test_case("\"hi\\\"\"", StringDoubleQuoted ; "double_3")]
  #[test_case("'hi'", StringSingleQuoted ; "single_1")]
  #[test_case("'hi\n'", StringSingleQuoted ; "single_2")]
  #[test_case("'hi\\''", StringSingleQuoted ; "single_3")]
  #[test_case("|||\n  test\n    more\n  |||\n    foo\n|||", StringBlock ; "block_1")]
  #[test_case("|||\n\ttest\n\t  more\n\t|||\n\t  foo\n|||", StringBlock ; "block_2")]
  #[test_case("|||\n\t  \ttest\n\t  \t  more\n\t  \t|||\n\t  \t  foo\n|||", StringBlock ; "block_3")]
  #[test_case("|||\n\n  test\n\n\n    more\n  |||\n    foo\n|||", StringBlock ; "block_4")]
  #[test_case("@\"\"", StringDoubleVerbatim ; "verbatim_double_1")]
  #[test_case("@''", StringSingleVerbatim ; "verbatim_single_1")]
  #[test_case("@\"\"\"\"", StringDoubleVerbatim ; "verbatim_double_2")]
  #[test_case("@''''", StringSingleVerbatim ; "verbatim_single_2")]
  #[test_case("@\"\\n\"", StringDoubleVerbatim ; "verbatim_double_3")]
  #[test_case("@\"''\"", StringDoubleVerbatim ; "verbatim_double_4")]
  fn string(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test_case("\"hi", ErrorStringDoubleQuotedUnterminated ; "double_unterm")]
  #[test_case("'hi", ErrorStringSingleQuotedUnterminated ; "single_unterm")]
  #[test_case("@\"hi", ErrorStringDoubleVerbatimUnterminated ; "double_verb_unterm")]
  #[test_case("@'hi", ErrorStringSingleVerbatimUnterminated ; "single_verb_unterm")]
  fn string_unterminated(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test_case("assert", KeywordAssert)]
  #[test_case("else", KeywordElse)]
  #[test_case("error", KeywordError)]
  #[test_case("false", KeywordFalse)]
  #[test_case("for", KeywordFor)]
  #[test_case("function", KeywordFunction)]
  #[test_case("if", KeywordIf)]
  #[test_case("import", KeywordImport)]
  #[test_case("importstr", KeywordImportStr)]
  #[test_case("in", KeywordIn)]
  #[test_case("local", KeywordLocal)]
  #[test_case("null", KeywordNull)]
  #[test_case("self", KeywordSelf)]
  #[test_case("super", KeywordSuper)]
  #[test_case("tailstrict", KeywordTailStrict)]
  #[test_case("then", KeywordThen)]
  #[test_case("true", KeywordTrue)]
  fn keyword(src: &str, tok: TokenKind) {
    test_tokens!(src, [tok]);
  }

  #[test]
  fn identifier() {
    test_tokens!("foobar123", [Ident=>"foobar123"]);
  }

  #[test]
  fn identifiers() {
    test_tokens!(
      "foo bar123",
      [
        Ident=>"foo",
        Whitespace,
        Ident=>"bar123",
      ]
    );
  }

  #[test]
  fn c_comment() {
    test_tokens!("// hi", [SingelLineSlashComment]);
  }

  #[test]
  fn py_comment() {
    test_tokens!("# hi", [SingleLineHashComment]);
  }

  #[test]
  fn c_multiline_comment() {
    test_tokens!("/* hi \n bye */", [BlockComment]);
  }

  #[test]
  fn c_comment_too_short() {
    test_tokens!("/*/", [ErrorCommentTooShort]);
  }

  #[test]
  fn c_comment_minimal() {
    test_tokens!("/**/", [BlockComment]);
  }

  #[test]
  fn c_comment_just_slack() {
    test_tokens!("/*/*/", [BlockComment]);
  }

  #[test]
  fn c_comment_space_slack() {
    test_tokens!("/* /*/", [BlockComment]);
  }

  #[test]
  fn c_comment_many_lines() {
    test_tokens!("/*\n\n*/", [BlockComment]);
  }

  #[test]
  fn c_comment_no_term() {
    test_tokens!("/* hi", [ErrorCommentUnterminated]);
  }

  // TODO: Figure out
  // #[test]
  // fn str_block_bad_indent() {
  //   test_tokens!("|||\n  test\n foo\n|||", [ErrorStringBlockMissingIndent]);
  // }

  #[test]
  fn str_block_eof() {
    test_tokens!("|||\n  test", [ErrorStringBlockUnerminated]);
  }

  #[test]
  fn str_block_not_term() {
    test_tokens!("|||\n  test\n", [ErrorStringBlockUnerminated]);
  }

  #[test]
  fn str_block_no_ws() {
    test_tokens!("|||\ntest\n|||", [ErrorStringBlockMissingIndent]);
  }

  #[test]
  fn str_verbatim_unterminated() {
    test_tokens!("@\"blah blah", [ErrorStringDoubleVerbatimUnterminated]);
  }

  #[test]
  fn str_verbatim_junk_after_at() {
    test_tokens!(
      "@blah blah",
      [
        ErrorStringMissingQuotes,
        Whitespace,
        Ident=>"blah",
      ]
    );
  }

  #[test]
  fn junk() {
    let src = "💩";
    test_tokens!(src, [ErrorInvalidToken]);
  }

  mod golden {
    use super::*;
    use core::fmt;

    #[derive(PartialEq, Eq, Clone, Copy)]
    struct PrettyString<'a>(&'a str);

    impl<'a> PrettyString<'a> {
      #[inline]
      fn new<S: AsRef<str> + ?Sized>(value: &'a S) -> Self {
        PrettyString(value.as_ref())
      }
    }

    impl<'a> fmt::Debug for PrettyString<'a> {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.0)
      }
    }

    macro_rules! assert_eq {
      ($left:expr, $right:expr $(,$($rest:tt)*)?) => {
        pretty_assertions::assert_eq!(
          PrettyString::new($left),
          PrettyString::new($right)
          $(,$($rest)*)?
        );
      }
    }

    #[test_gen::test_golden("test_data/inline/ok/*.jsonnet")]
    fn golden_ok(content: &str, _: &str) -> String {
      use core::fmt::Write;
      let lex = Lexer::new(content);
      let mut result = String::new();

      let mut offset = 0;
      for token in lex {
        let val = &content[offset as usize..(offset + token.len) as usize];
        assert!(!token.kind.is_error());
        writeln!(
          result,
          "{:?}@{}:{} {:?}",
          token.kind,
          offset,
          offset + token.len,
          val
        )
        .unwrap();

        offset += token.len;
      }

      result
    }
  }
}
