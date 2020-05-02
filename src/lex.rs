pub(crate) mod error;
pub(crate) mod span;
pub(crate) mod token;

use crate::lex::{
  error::ErrorToken,
  span::{FileId, Span},
  token::{private, Spanned, StringKind, Token},
};
use logos::Logos;
use std::collections::VecDeque;

pub trait IntoToken: private::Sealed {
  fn into_token(self) -> Result<Token, ErrorToken>;
}

impl<T: Spanned> token::private::Sealed for Result<T, ErrorToken> {}
impl<T: Spanned> Spanned for Result<T, ErrorToken> {
  fn span(&self) -> Span {
    match self {
      Ok(t) => t.span(),
      Err(e) => e.span(),
    }
  }
}

impl<T: IntoToken + Spanned> IntoToken for Result<T, ErrorToken> {
  fn into_token(self) -> Result<Token, ErrorToken> {
    self.and_then(IntoToken::into_token)
  }
}

fn lex_str_block<'a>(lex: &mut logos::Lexer<'a, RawToken<'a>>) -> Result<String, ErrorToken> {
  struct Context<'a> {
    file: FileId,
    source: &'a str,
    index: usize,
    // offset from global source
    offset: usize,
  }

  impl<'a> Context<'a> {
    fn rest(&self) -> &'a str {
      &self.source[self.index..]
    }

    fn next(&mut self) -> Option<char> {
      if self.index == self.source.len() {
        return None;
      }

      match self.rest().chars().next() {
        None => None,
        Some(c) => {
          self.index += c.len_utf8();
          Some(c)
        }
      }
    }

    fn peek(&self) -> Option<char> {
      if self.index == self.source.len() {
        return None;
      }

      self.rest().chars().next()
    }

    fn eat_while(&mut self, f: impl Fn(char) -> bool) -> usize {
      if self.index == self.source.len() {
        return 0;
      }

      let next_char = self.rest().char_indices().skip_while(|(_, c)| f(*c)).next();

      match next_char {
        None => {
          let diff = self.source.len() - self.index;
          self.index = self.source.len();
          diff
        }
        Some((idx, _)) => {
          self.index += idx;
          idx
        }
      }
    }

    fn skip(&mut self, len: usize) {
      self.index = match self.index + len {
        n if n > self.source.len() => self.source.len(),
        n => n,
      };
    }

    fn pos(&self) -> Span {
      if self.index == self.source.len() {
        self
          .file
          .span(self.offset + self.index..self.offset + self.index)
      } else {
        // TODO: char size
        self
          .file
          .span(self.offset + self.index..self.offset + self.index + 1)
      }
    }

    fn pos_next(&self) -> Span {
      if self.index + 1 == self.source.len() {
        self
          .file
          .span(self.offset + self.index..self.offset + self.index)
      } else {
        // TODO: char size
        self
          .file
          .span(self.offset + self.index + 1..self.offset + self.index + 2)
      }
    }
  }

  // Check that b has at least the same whitespace prefix as a and returns the
  // amount of this whitespace, otherwise returns 0.  If a has no whitespace
  // prefix than return 0.
  fn check_whitespace(a: &str, b: &str) -> usize {
    let a = a.as_bytes();
    let b = b.as_bytes();

    for i in 0..a.len() {
      if a[i] != b' ' && a[i] != b'\t' {
        // a has run out of whitespace and b matched up to this point. Return result.
        return i;
      }

      if i >= b.len() {
        // We ran off the edge of b while a still has whitespace. Return 0 as failure.
        return 0;
      }

      if a[i] != b[i] {
        // a has whitespace but b does not. Return 0 as failure.
        return 0;
      }
    }

    // We ran off the end of a and b kept up
    a.len()
  }

  fn guess_token_end_and_bump<'a>(lex: &mut logos::Lexer<'a, RawToken<'a>>, ctx: &Context<'a>) {
    let end_index = ctx
      .rest()
      .find("|||")
      .map(|v| v + 3)
      .unwrap_or(ctx.rest().len());
    lex.bump(ctx.index + end_index);
  }

  debug_assert_eq!(lex.slice(), "|||");
  let mut buf = match lex.remainder().find("|||") {
    Some(n) => String::with_capacity(n),
    None => String::new(),
  };

  let mut ctx = Context {
    file: lex.extras.file,
    source: lex.remainder(),
    index: 0,
    offset: lex.span().end,
  };

  // Skip whitespaces
  ctx.eat_while(|r| r == ' ' || r == '\t' || r == '\r');

  // Skip \n
  match ctx.next() {
    Some('\n') => (),
    None => {
      let pos = ctx.pos();
      guess_token_end_and_bump(lex, &ctx);
      return Err(error::UnexpectedEndOfString::new(pos).into());
    }
    // Text block requires new line after |||.
    Some(_) => {
      let pos = ctx.pos();
      guess_token_end_and_bump(lex, &ctx);
      return Err(error::MissingTextBlockNewLine::new(pos).into());
    }
  }

  // Process leading blank lines before calculating string block indent
  while let Some('\n') = ctx.peek() {
    ctx.next();
    buf.push('\n');
  }

  let mut num_whitespace = check_whitespace(ctx.rest(), ctx.rest());
  let str_block_indent = &ctx.rest()[..num_whitespace];

  if num_whitespace == 0 {
    // Text block's first line must start with whitespace
    let pos = ctx.pos_next();
    guess_token_end_and_bump(lex, &ctx);
    return Err(error::MissingTextBlockIndent::new(pos).into());
  }

  loop {
    debug_assert_ne!(num_whitespace, 0, "Unexpected value for num_whitespace");
    ctx.skip(num_whitespace);

    loop {
      match ctx.next() {
        None => {
          let pos = ctx.pos();
          guess_token_end_and_bump(lex, &ctx);
          return Err(error::UnexpectedEndOfString::new(pos).into());
        }
        Some('\n') => break,
        Some(c) => buf.push(c),
      }
    }

    buf.push('\n');

    // Skip any blank lines
    while let Some('\n') = ctx.peek() {
      ctx.next();
      buf.push('\n');
    }

    // Look at the next line
    num_whitespace = check_whitespace(str_block_indent, ctx.rest());
    if num_whitespace == 0 {
      // End of the text block
      let mut term_indent = String::with_capacity(num_whitespace);
      loop {
        match ctx.peek() {
          Some(' ') | Some('\t') => {
            term_indent.push(ctx.next().unwrap());
          }
          _ => break,
        }
      }

      if !ctx.rest().starts_with("|||") {
        // Text block not terminated with |||
        let pos = ctx.pos();
        if pos.len() == 0 {
          // eof
          let pos = ctx.pos();
          lex.bump(ctx.index);
          return Err(error::UnexpectedEndOfString::new(pos).into());
        }

        guess_token_end_and_bump(lex, &ctx);
        return Err(error::MissingTextBlockTermination::new(pos).into());
      }

      // Skip '|||'
      ctx.skip(3);
      break;
    }
  }

  lex.bump(ctx.index);
  Ok(buf)
}

#[derive(Debug, Clone, Copy, Default)]
struct LexExtra {
  file: FileId,
}

#[derive(Logos, Debug, PartialEq)]
#[logos(extras = LexExtra)]
enum RawToken<'a> {
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
  Id(&'a str),

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?")]
  Number(&'a str),

  #[regex(r"(?:0|[1-9][0-9]*)\.[^0-9]")]
  ErrorNumJunkAfterDecimalPoint(&'a str),

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?[eE][^+-0-9]")]
  ErrorNumJunkAfterExponent(&'a str),

  #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]+)?[eE][+-][^0-9]")]
  ErrorNumJunkAfterExponentSign(&'a str),

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

  #[regex(r"[!\$:~\+\-&\|\^=<>\*/%]+")]
  Op(&'a str),

  #[regex("\"(?s:[^\"\\\\]|\\\\.)*\"")]
  StringDoubleQuoted(&'a str),

  #[regex("'(?s:[^'\\\\]|\\\\.)*'")]
  StringSingleQuoted(&'a str),

  #[regex("@\"(?:[^\"]|\"\")*\"")]
  StringDoubleVerbatim(&'a str),

  #[regex("@'(?:[^']|'')*'")]
  StringSingleVerbatim(&'a str),

  #[regex(r"\|\|\|", lex_str_block)]
  StringBlock(Result<String, ErrorToken>),

  #[regex("\"(?s:[^\"\\\\]|\\\\.)*")]
  #[regex("'(?s:[^'\\\\]|\\\\.)*")]
  #[regex("@\"(?:[^\"]|\"\")*")]
  #[regex("@'(?:[^']|'')*")]
  ErrorStringUnterminated(&'a str),

  #[regex("@[^\"'\\s]\\S+")]
  ErrorStringMissingQuotes(&'a str),

  #[token("/*/")]
  ErrorCommentTooShort,

  #[regex(r"/\*([^*]|\*[^/])+")]
  ErrorCommentUnterminated,

  #[error]
  #[regex(r"[ \t\n\r]+", logos::skip)] // whitespace
  #[regex(r"//[^\r\n]*(\r\n|\n)?", logos::skip)] // //-comments
  #[regex(r"#[^\r\n]*(\r\n|\n)?", logos::skip)] // #-comments
  #[regex(r"/\*([^*]|\*[^/])*\*/", logos::skip)] // /* comments */
  Error,
}

pub struct Lexer<'a> {
  lex: logos::Lexer<'a, RawToken<'a>>,
  done: bool,
  peeked: VecDeque<Result<Token, ErrorToken>>,
}

impl<'a> Lexer<'a> {
  pub(crate) fn new(content: &'a str, file: FileId) -> Self {
    let mut lex = RawToken::lexer(content);
    lex.extras.file = file;

    Self {
      lex: RawToken::lexer(content),
      done: false,
      peeked: VecDeque::with_capacity(4),
    }
  }

  fn op(op: &str, span: Span) -> Result<Token, ErrorToken> {
    token::Operator::get(op, span)
      .map(Token::from)
      .ok_or_else(|| error::InvalidOperator::new(span).into())
  }

  fn str(s: &'a str, kind: StringKind, span: Span) -> Result<Token, ErrorToken> {
    let delim = match kind {
      StringKind::DoubleQuoted => '"',
      StringKind::SingleQuoted => '\'',
      _ => panic!("Should never be called with {:?}", kind),
    };

    debug_assert_eq!(s.as_bytes().first().unwrap().clone() as char, delim);
    debug_assert_eq!(s.as_bytes().last().unwrap().clone() as char, delim);

    let s: &str = &s[1..s.len() - 1];
    let mut offset = span.start().to_usize() + 1;
    let mut ind = match s.find('\\') {
      None => return Ok(token::String::new(s, kind, span).into()),
      Some(ind) => Some(ind),
    };

    let mut rest = s;
    let mut buf = String::with_capacity(s.len());

    loop {
      match ind {
        None => {
          buf.push_str(rest);
          break;
        }

        Some(index) => {
          debug_assert_eq!(rest.as_bytes()[index], b'\\');
          if index >= rest.len() {
            return Err(error::UnexpectedEndOfString::new(span).into());
          }

          buf.push_str(&rest[..index]);
          let mut escaped_len = 1;
          match rest.as_bytes()[index + 1] {
            b'"' => buf.push('"'),
            b'\'' => buf.push('\''),
            b'\\' => buf.push('\\'),
            b'/' => buf.push('/'),
            b'b' => buf.push('\x08'),
            b'f' => buf.push('\x0c'),
            b'n' => buf.push('\n'),
            b'r' => buf.push('\r'),
            b't' => buf.push('\t'),
            b'u' => {
              escaped_len = 5;
              if index + 5 <= rest.len() {
                return Err(error::UnexpectedEndOfString::new(span).into());
              }

              let hex_str: &str = &rest[index + 2..index + 6];
              let hex_num = match u32::from_str_radix(hex_str, 16) {
                Ok(n) => n,
                Err(_) => {
                  return Err(
                    error::InvalidEscapeSequence::new(
                      // &rest[index..index + 6],
                      // offset + index..offset + index + 6,
                      span,
                    )
                    .into(),
                  );
                }
              };
              let chr = match std::char::from_u32(hex_num) {
                Some(c) => c,
                None => {
                  return Err(
                    error::InvalidUnicodeCodePoint::new(
                      // &rest[index..index + 6],
                      // offset + index..offset + index + 6,
                      span,
                    )
                    .into(),
                  );
                }
              };
              buf.push(chr)
            }

            _ => {
              return Err(
                error::InvalidEscapeSequence::new(
                  // &rest[index..index + 2],
                  // offset + index..offset + index + 2,
                  span,
                )
                .into(),
              );
            }
          }

          rest = &rest[index + 1 + escaped_len..];
          offset += index + 1 + escaped_len;
          ind = rest.find('\\');
        }
      }
    }

    Ok(token::String::new(buf, kind, span).into())
  }

  fn str_verbatim(s: &'a str, kind: StringKind, span: Span) -> Result<Token, ErrorToken> {
    let delim = match kind {
      StringKind::DoubleQuotedVerbatim => b'"',
      StringKind::SingleQuotedVerbatim => b'\'',
      _ => panic!("Should never be called with {:?}", kind),
    };

    debug_assert!(!s.is_empty());
    debug_assert_eq!(s.as_bytes()[0], b'@');
    debug_assert_eq!(s.as_bytes()[1], delim);
    debug_assert_eq!(*s.as_bytes().last().unwrap(), delim);

    let pat_bytes = [delim; 2];
    let pat = std::str::from_utf8(&pat_bytes).unwrap();

    let s: &str = &s[2..s.len() - 1];
    let mut ind = match s.find(pat) {
      None => return Ok(token::String::new(s, kind, span).into()),
      Some(ind) => Some(ind),
    };

    let mut rest = s;
    let mut buf = String::with_capacity(s.len());

    loop {
      match ind {
        None => {
          buf.push_str(rest);
          break;
        }

        Some(index) => {
          debug_assert_eq!(rest.as_bytes()[index], delim as u8);
          debug_assert_eq!(rest.as_bytes()[index + 1], delim as u8);

          buf.push_str(&rest[..index]);
          buf.push(delim as char);
          rest = &rest[index + 2..];
          ind = rest.find(pat);
        }
      }
    }

    Ok(token::String::new(buf, kind, span).into())
  }

  fn token(raw: RawToken, span: Span) -> Result<Token, ErrorToken> {
    match raw {
      RawToken::KeywordAssert => Ok(token::Assert::new(span).into()),
      RawToken::KeywordElse => Ok(token::Else::new(span).into()),
      RawToken::KeywordError => Ok(token::Error::new(span).into()),
      RawToken::KeywordFalse => Ok(token::False::new(span).into()),
      RawToken::KeywordFor => Ok(token::For::new(span).into()),
      RawToken::KeywordFunction => Ok(token::Function::new(span).into()),
      RawToken::KeywordIf => Ok(token::If::new(span).into()),
      RawToken::KeywordImport => Ok(token::Import::new(span).into()),
      RawToken::KeywordImportStr => Ok(token::ImportStr::new(span).into()),
      RawToken::KeywordIn => Ok(token::In::new(span).into()),
      RawToken::KeywordLocal => Ok(token::Local::new(span).into()),
      RawToken::KeywordNull => Ok(token::Null::new(span).into()),
      RawToken::KeywordTailStrict => Ok(token::TailStrict::new(span).into()),
      RawToken::KeywordThen => Ok(token::Then::new(span).into()),
      RawToken::KeywordSelf => Ok(token::SelfValue::new(span).into()),
      RawToken::KeywordSuper => Ok(token::Super::new(span).into()),
      RawToken::KeywordTrue => Ok(token::True::new(span).into()),
      RawToken::Id(name) => Ok(token::Ident::new(name, span).into()),
      RawToken::Number(value) => Ok(token::Number::new(value, span).into()),
      RawToken::ErrorNumJunkAfterDecimalPoint(s) => {
        Err(error::NumberJunkAfterDecimalPoint::new(span).into())
      }
      RawToken::ErrorNumJunkAfterExponent(s) => {
        Err(error::NumberJunkAfterExponent::new(span).into())
      }
      RawToken::ErrorNumJunkAfterExponentSign(s) => {
        Err(error::NumberJunkAfterExponentSign::new(span).into())
      }
      RawToken::SymbolLeftBrace => Ok(token::LeftBrace::new(span).into()),
      RawToken::SymbolRightBrace => Ok(token::RightBrace::new(span).into()),
      RawToken::SymbolLeftBracket => Ok(token::LeftBracket::new(span).into()),
      RawToken::SymbolRightBracket => Ok(token::RightBracket::new(span).into()),
      RawToken::SymbolComma => Ok(token::Comma::new(span).into()),
      RawToken::SymbolDot => Ok(token::Dot::new(span).into()),
      RawToken::SymbolLeftParen => Ok(token::LeftParen::new(span).into()),
      RawToken::SymbolRightParen => Ok(token::RightParen::new(span).into()),
      RawToken::SymbolSemi => Ok(token::SemiColon::new(span).into()),
      RawToken::SymbolDollar => Ok(token::Dollar::new(span).into()),
      RawToken::Op(op) => Lexer::op(op, span),
      RawToken::StringDoubleQuoted(value) => Lexer::str(value, StringKind::DoubleQuoted, span),
      RawToken::StringSingleQuoted(value) => Lexer::str(value, StringKind::SingleQuoted, span),
      RawToken::StringDoubleVerbatim(value) => {
        Lexer::str_verbatim(value, StringKind::DoubleQuotedVerbatim, span)
      }
      RawToken::StringSingleVerbatim(value) => {
        Lexer::str_verbatim(value, StringKind::SingleQuotedVerbatim, span)
      }
      RawToken::StringBlock(value) => {
        value.map(|value| token::String::new(value, StringKind::Block, span).into())
      }
      RawToken::ErrorStringUnterminated(s) => Err(error::StringUnterminated::new(span).into()),
      RawToken::ErrorStringMissingQuotes(s) => Err(error::MissingQuotesAfterAt::new(span).into()),
      RawToken::ErrorCommentTooShort => Err(error::CommentTooShort::new(span).into()),
      RawToken::ErrorCommentUnterminated => Err(error::CommentUnterminated::new(span).into()),
      RawToken::Error => Err(error::InvalidToken::new(span).into()),
    }
  }

  fn read(&mut self) -> Option<Result<Token, ErrorToken>> {
    if self.done {
      return None;
    }

    let lex = &mut self.lex;
    match lex.next() {
      None => {
        self.done = true;
        None
      }
      Some(tok) => {
        let span = lex.span();

        Some(Lexer::token(tok, lex.extras.file.span(span)))
      }
    }
  }

  #[inline]
  pub fn peek(&mut self) -> Option<&Result<Token, ErrorToken>> {
    self.peek_nth(0)
  }

  pub fn peek_nth(&mut self, n: usize) -> Option<&Result<Token, ErrorToken>> {
    while self.peeked.len() <= n && !self.done {
      if let Some(tok) = self.read() {
        self.peeked.push_back(tok);
      }
    }

    self.peeked.get(n)
  }

  pub fn span(&self) -> Span {
    self.lex.extras.file.span(self.lex.span())
  }
}

impl<'a> Iterator for Lexer<'a> {
  type Item = Result<Token, ErrorToken>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    match self.peeked.pop_front() {
      Some(v) => Some(v),
      None => self.read(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use error::*;
  use test_case::test_case;
  use token::*;

  macro_rules! test_tokens {
    ($src:expr, [$(
      $tok:expr
    ),*$(,)?]) => {{
      let mut lex = Lexer::new($src, Default::default());
      #[allow(unused_mut)]
      let mut index = 0;
      $({
        let actual = lex.next().expect(&format!("Expected token {}", index + 1));
        let expected = $tok.into_token();
        assert_eq!(actual, expected, "index: {}", index);
        assert_eq!(actual.span(), expected.span(), "index: {}", index);

        index += 1;
      })*

      lex.next().expect_none(&format!("Expected exactly {} tokens", index));
    }};
  }

  #[test]
  fn empty() {
    test_tokens!("", []);
  }

  #[test]
  fn whitespace() {
    test_tokens!("  \t\n\r\r\n", []);
  }

  #[test_case("{", LeftBrace::from_range(0..1))]
  #[test_case("}", RightBrace::from_range(0..1))]
  #[test_case("[", LeftBracket::from_range(0..1))]
  #[test_case("]", RightBracket::from_range(0..1))]
  #[test_case("(", LeftParen::from_range(0..1))]
  #[test_case(")", RightParen::from_range(0..1))]
  #[test_case(",", Comma::from_range(0..1))]
  #[test_case(".", Dot::from_range(0..1))]
  #[test_case(";", SemiColon::from_range(0..1))]
  #[test_case("$", Dollar::from_range(0..1))]
  fn symbol(src: &str, tok: impl IntoToken) {
    test_tokens!(src, [tok]);
  }

  #[test_case(":", Colon::from_range(0..1))]
  #[test_case("::", DoubleColon::from_range(0..2))]
  #[test_case("!", Not::from_range(0..1))]
  #[test_case("==", Equal::from_range(0..2))]
  #[test_case("!=", NotEqual::from_range(0..2))]
  #[test_case("~", BitNeg::from_range(0..1))]
  #[test_case("+", Plus::from_range(0..1))]
  #[test_case("-", Minus::from_range(0..1))]
  #[test_case("*", Mul::from_range(0..1))]
  #[test_case("/", Div::from_range(0..1))]
  #[test_case("%", Mod::from_range(0..1))]
  #[test_case("&", BitAnd::from_range(0..1))]
  #[test_case("|", BitOr::from_range(0..1))]
  #[test_case("^", BitXor::from_range(0..1))]
  #[test_case("=", Assign::from_range(0..1))]
  #[test_case("<", LessThan::from_range(0..1))]
  #[test_case(">", GreaterThan::from_range(0..1))]
  #[test_case("<=", LessThanOrEqual::from_range(0..2))]
  #[test_case(">=", GreaterThanOrEqual::from_range(0..2))]
  fn operator(src: &str, tok: impl IntoToken) {
    test_tokens!(src, [tok]);
  }

  #[test]
  fn not() {
    test_tokens!("! ", [Not::from_range(0..1)]);
  }

  #[test_case("->" ; "arrow_right")]
  #[test_case("<-" ; "arrow_left")]
  #[test_case(">==|" ; "junk")]
  fn bad_op(src: &str) {
    test_tokens!(src, [InvalidOperator::from_range(0..src.len())]);
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
    test_tokens!(src, [Number::from_range(src, 0..src.len())]);
  }

  #[test]
  fn number_0100() {
    test_tokens!(
      "0100",
      [
        Number::from_range("0", 0..1),
        Number::from_range("100", 1..4),
      ]
    );
  }

  #[test]
  fn number_10_p_10() {
    test_tokens!(
      "10+10",
      [
        Number::from_range("10", 0..2),
        Plus::from_range(2..3),
        Number::from_range("10", 3..5),
      ]
    );
  }

  #[test_case("1.+", NumberJunkAfterDecimalPoint::from_range(0..3))]
  #[test_case("1e!", NumberJunkAfterExponent::from_range(0..3))]
  #[test_case("1e+!", NumberJunkAfterExponentSign::from_range(0..4))]
  fn bad_number(src: &str, tok: impl IntoToken) {
    test_tokens!(src, [tok]);
  }

  #[test_case("\"hi\"", StringKind::DoubleQuoted, "hi" ; "double_1")]
  #[test_case("\"hi\n\"", StringKind::DoubleQuoted, "hi\n" ; "double_2")]
  #[test_case("\"hi\\\"\"", StringKind::DoubleQuoted, "hi\"" ; "double_3")]
  #[test_case("'hi'", StringKind::SingleQuoted, "hi" ; "single_1")]
  #[test_case("'hi\n'", StringKind::SingleQuoted, "hi\n" ; "single_2")]
  #[test_case("'hi\\''", StringKind::SingleQuoted, "hi'" ; "single_3")]
  #[test_case("|||\n  test\n    more\n  |||\n    foo\n|||", StringKind::Block, "test\n  more\n|||\n  foo\n" ; "block_1")]
  #[test_case("|||\n\ttest\n\t  more\n\t|||\n\t  foo\n|||", StringKind::Block, "test\n  more\n|||\n  foo\n" ; "block_2")]
  #[test_case("|||\n\t  \ttest\n\t  \t  more\n\t  \t|||\n\t  \t  foo\n|||", StringKind::Block, "test\n  more\n|||\n  foo\n" ; "block_3")]
  #[test_case("|||\n\n  test\n\n\n    more\n  |||\n    foo\n|||", StringKind::Block, "\ntest\n\n\n  more\n|||\n  foo\n" ; "block_4")]
  #[test_case("@\"\"", StringKind::DoubleQuotedVerbatim, "" ; "verbatim_double_1")]
  #[test_case("@''", StringKind::SingleQuotedVerbatim,  "" ; "verbatim_single_1")]
  #[test_case("@\"\"\"\"", StringKind::DoubleQuotedVerbatim, "\"" ; "verbatim_double_2")]
  #[test_case("@''''", StringKind::SingleQuotedVerbatim, "'" ; "verbatim_single_2")]
  #[test_case("@\"\\n\"", StringKind::DoubleQuotedVerbatim, "\\n" ; "verbatim_double_3")]
  #[test_case("@\"''\"", StringKind::DoubleQuotedVerbatim, "''" ; "verbatim_double_4")]
  fn string(src: &str, kind: StringKind, expected: &str) {
    test_tokens!(src, [String::from_range(expected, kind, 0..src.len())]);
  }

  #[test_case("\"hi\\\n\"" ; "double_4")]
  #[test_case("'hi\\\n'" ; "single_4")]
  fn string_invalid_escape_sequence(src: &str) {
    test_tokens!(src, [InvalidEscapeSequence::from_range(0..src.len())]);
  }

  #[test_case("\"hi" ; "double_5")]
  #[test_case("'hi" ; "single_5")]
  fn string_unterminated(src: &str) {
    test_tokens!(src, [StringUnterminated::from_range(0..src.len())]);
  }

  #[test_case("assert", Assert::from_range(0..6))]
  #[test_case("else", Else::from_range(0..4))]
  #[test_case("error", Error::from_range(0..5))]
  #[test_case("false", False::from_range(0..5))]
  #[test_case("for", For::from_range(0..3))]
  #[test_case("function", Function::from_range(0..8))]
  #[test_case("if", If::from_range(0..2))]
  #[test_case("import", Import::from_range(0..6))]
  #[test_case("importstr", ImportStr::from_range(0..9))]
  #[test_case("in", In::from_range(0..2))]
  #[test_case("local", Local::from_range(0..5))]
  #[test_case("null", Null::from_range(0..4))]
  #[test_case("self", SelfValue::from_range(0..4))]
  #[test_case("super", Super::from_range(0..5))]
  #[test_case("tailstrict", TailStrict::from_range(0..10))]
  #[test_case("then", Then::from_range(0..4))]
  #[test_case("true", True::from_range(0..4))]
  fn keyword(src: &str, tok: impl IntoToken) {
    test_tokens!(src, [tok]);
  }

  #[test]
  fn identifier() {
    test_tokens!("foobar123", [Ident::from_range("foobar123", 0..9)]);
  }

  #[test]
  fn identifiers() {
    test_tokens!(
      "foo bar123",
      [
        Ident::from_range("foo", 0..3),
        Ident::from_range("bar123", 4..10)
      ]
    );
  }

  #[test]
  fn c_comment() {
    test_tokens!("// hi", []);
  }

  #[test]
  fn py_comment() {
    test_tokens!("# hi", []);
  }

  #[test]
  fn c_multiline_comment() {
    test_tokens!("/* hi \n bye */", []);
  }

  #[test]
  fn c_comment_too_short() {
    test_tokens!("/*/", [CommentTooShort::from_range(0..3)]);
  }

  #[test]
  fn c_comment_minimal() {
    test_tokens!("/**/", []);
  }

  #[test]
  fn c_comment_just_slack() {
    test_tokens!("/*/*/", []);
  }

  #[test]
  fn c_comment_space_slack() {
    test_tokens!("/* /*/", []);
  }

  #[test]
  fn c_comment_many_lines() {
    test_tokens!("/*\n\n*/", []);
  }

  #[test]
  fn c_comment_no_term() {
    test_tokens!("/* hi", [CommentUnterminated::from_range(0..5)]);
  }

  #[test]
  fn str_block_bad_indent() {
    test_tokens!(
      "|||\n  test\n foo\n|||",
      [MissingTextBlockTermination::from_range(12..13)]
    );
  }

  #[test]
  fn str_block_eof() {
    test_tokens!("|||\n  test", [UnexpectedEndOfString::from_range(10..10)]);
  }

  #[test]
  fn str_block_not_term() {
    test_tokens!("|||\n  test\n", [UnexpectedEndOfString::from_range(11..11)]);
  }

  #[test]
  fn str_block_no_ws() {
    test_tokens!("|||\ntest\n|||", [MissingTextBlockIndent::from_range(5..6)]);
  }

  #[test]
  fn str_verbatim_unterminated() {
    test_tokens!("@\"blah blah", [StringUnterminated::from_range(0..11)]);
  }

  #[test]
  fn str_verbatim_junk_after_at() {
    test_tokens!(
      "@blah blah",
      [
        MissingQuotesAfterAt::from_range(0..5),
        Ident::from_range("blah", 6..10)
      ]
    );
  }

  #[test]
  fn junk() {
    let src = "💩";
    test_tokens!(src, [InvalidToken::from_range(0..4)]);
  }
}
