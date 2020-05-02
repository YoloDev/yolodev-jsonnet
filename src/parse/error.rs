use crate::{
  lex::{
    span::Span,
    token::{private, Spanned},
  },
  parse::buffer::Cursor,
};
use core::{
  fmt,
  fmt::{Debug, Display},
};

fn diag_msg(d: &(impl Diagnostic + ?Sized)) -> String {
  struct Wrapper<'a, T: Diagnostic + ?Sized>(&'a T);
  impl<'a, T: Diagnostic + ?Sized> Display for Wrapper<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      Diagnostic::fmt(self.0, f)
    }
  }

  format!("{}", Wrapper(d))
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Severity {
  Info,
  Warning,
  Error,
}

pub trait CloneDiagnostic {
  fn clone_diagnostic(&self) -> Box<dyn Diagnostic>;
}

pub trait Diagnostic: CloneDiagnostic + Spanned + Debug + 'static {
  fn severity(&self) -> Severity {
    Severity::Error
  }
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result;

  #[inline]
  fn message(&self) -> String {
    diag_msg(self)
  }
}

impl<D: Diagnostic + Clone> CloneDiagnostic for D {
  fn clone_diagnostic(&self) -> Box<dyn Diagnostic> {
    Box::new(self.clone())
  }
}

#[derive(Debug, Clone, Copy)]
pub struct UnexpectedEndOfFile<T: Diagnostic + Clone>(T);

impl<T: Diagnostic + Clone> private::Sealed for UnexpectedEndOfFile<T> {}
impl<T: Diagnostic + Clone> Spanned for UnexpectedEndOfFile<T> {
  #[inline]
  fn span(&self) -> Span {
    self.0.span()
  }
}

impl<T: Diagnostic + Clone> Diagnostic for UnexpectedEndOfFile<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "unexpected end of input, ")?;
    Diagnostic::fmt(&self.0, f)
  }
}

pub struct Error {
  messages: Vec<Box<dyn Diagnostic>>,
}

impl Clone for Error {
  fn clone(&self) -> Self {
    let messages = self.messages.iter().map(|d| d.clone_diagnostic()).collect();
    Error { messages }
  }
}

impl Error {
  pub fn new(diagnostic: impl Diagnostic + Clone) -> Error {
    let message: Box<dyn Diagnostic> = Box::new(diagnostic);

    Error {
      messages: vec![message],
    }
  }

  pub(crate) fn new_at(cursor: Cursor, diagnostic: impl Diagnostic + Clone) -> Error {
    if cursor.eof() {
      Error::new(UnexpectedEndOfFile(diagnostic))
    } else {
      Error::new(diagnostic)
    }
  }
}

pub type Result<T> = std::result::Result<T, Error>;

define_error! {
  /// unexpected end of input
  pub struct UnexpectedEndOfInput;
}

define_error! {
  /// unexpected token
  pub struct UnexpectedToken;
}

define_error! {
  /// expected {expected}
  pub struct ExpectedToken1 {
    expected: &'static str,
  }
}

define_error! {
  /// expected {first} or {second}
  pub struct ExpectedToken2 {
    first: &'static str,
    second: &'static str,
  }
}

define_error! {
  /// expected one of: {joined}
  pub struct ExpectedTokenMany {
    joined: String,
  }
}

impl Error {
  pub fn unexpected_end_of_input(span: Span) -> Error {
    Error::new(UnexpectedEndOfInput::new(span))
  }

  pub fn unexpected_token(span: Span) -> Error {
    Error::new(UnexpectedToken::new(span))
  }

  pub fn expected_token(span: Span, token: &'static str) -> Error {
    Error::new(ExpectedToken1::new(span, token))
  }

  pub fn expected_token2(span: Span, token1: &'static str, token2: &'static str) -> Error {
    Error::new(ExpectedToken2::new(span, token1, token2))
  }

  pub fn expected_tokens(span: Span, tokens: &[&'static str]) -> Error {
    match tokens.len() {
      0 => Error::unexpected_token(span),
      1 => Error::expected_token(span, tokens[0]),
      2 => Error::expected_token2(span, tokens[0], tokens[1]),
      _ => {
        let joined = tokens.join(", ");
        Error::new(ExpectedTokenMany::new(span, joined))
      }
    }
  }
}
