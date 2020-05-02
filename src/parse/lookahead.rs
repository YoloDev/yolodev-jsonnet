use crate::{
  lex::{
    span::Span,
    token::{private, Tok},
  },
  parse::{buffer::Cursor, error::Error},
};
use core::cell::RefCell;

/// Support for checking the next token in a stream to decide how to parse.
///
/// An important advantage over [`ParseStream::peek`] is that here we
/// automatically construct an appropriate error message based on the token
/// alternatives that get peeked. If you are producing your own error message,
/// go ahead and use `ParseStream::peek` instead.
pub struct Lookahead1<'a> {
  end: Span,
  cursor: Cursor<'a>,
  comparisons: RefCell<Vec<&'static str>>,
}

impl<'a> Lookahead1<'a> {
  pub(crate) fn new(end: Span, cursor: Cursor<'a>) -> Self {
    Self {
      end: end,
      cursor,
      comparisons: RefCell::new(Vec::new()),
    }
  }

  /// Looks at the next token in the parse stream to determine whether it
  /// matches the requested type of token.
  pub fn peek<T: Peek>(&self, token: T) -> bool {
    if T::Token::peek(self.cursor) {
      return true;
    }

    self.comparisons.borrow_mut().push(T::Token::NAME);
    false
  }

  /// Triggers an error at the current position of the parse stream.
  ///
  /// The error message will identify all of the expected token types that
  /// have been peeked against this lookahead instance.
  pub fn error(self) -> Error {
    let comparisons = self.comparisons.borrow();
    match comparisons.len() {
      0 => {
        if self.cursor.eof() {
          Error::unexpected_end_of_input(self.end)
        } else {
          Error::unexpected_token(self.cursor.span())
        }
      }

      _ => Error::expected_tokens(self.cursor.span(), &comparisons),
    }
  }
}

/// Types that can be parsed by looking at just one token.
///
/// Use [`ParseStream::peek`] to peek one of these types in a parse stream
/// without consuming it from the stream.
///
/// This trait is sealed and cannot be implemented for types outside of Syn.
///
/// [`ParseStream::peek`]: crate::parse::ParseBuffer::peek
pub trait Peek: private::Sealed {
  type Token: Tok;
}
