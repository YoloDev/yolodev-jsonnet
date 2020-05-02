pub(crate) mod buffer;
pub(crate) mod error;
pub(crate) mod lookahead;

use crate::{
  ast::punctuated::Punctuated,
  lex::{span::Span, token::Tok},
  parse::{
    buffer::Cursor,
    error::{Error, Result, Severity},
    lookahead::{Lookahead1, Peek},
  },
};
use alloc::rc::Rc;
use core::{cell::Cell, fmt, fmt::Debug, marker::PhantomData, mem, ops::Deref};
use error::Diagnostic;

/// Parsing interface implemented by all types that can be parsed in a default
/// way from a token stream.
pub trait Parse: Sized {
  fn parse(input: ParseStream) -> Result<Self>;
}

/// Input to a parser function.
pub type ParseStream<'a> = &'a ParseBuffer<'a>;

/// Cursor position within a buffered token stream.
///
/// This type is more commonly used through the type alias [`ParseStream`] which
/// is an alias for `&ParseBuffer`.
pub struct ParseBuffer<'a> {
  end: Span,
  // Instead of Cell<Cursor<'a>> so that ParseBuffer<'a> is covariant in 'a.
  // The rest of the code in this module needs to be careful that only a
  // cursor derived from this `cell` is ever assigned to this `cell`.
  //
  // Cell<Cursor<'a>> cannot be covariant in 'a because then we could take a
  // ParseBuffer<'a>, upcast to ParseBuffer<'short> for some lifetime shorter
  // than 'a, and then assign a Cursor<'short> into the Cell.
  //
  // By extension, it would not be safe to expose an API that accepts a
  // Cursor<'a> and trusts that it lives as long as the cursor currently in
  // the cell.
  cell: Cell<Cursor<'static>>,
  marker: PhantomData<Cursor<'a>>,
  unexpected: Cell<Option<Rc<Cell<Unexpected>>>>,
}

impl<'a> Drop for ParseBuffer<'a> {
  fn drop(&mut self) {
    if let Some(unexpected_span) = span_of_unexpected(self.cursor()) {
      let (inner, old_span) = inner_unexpected(self);
      if old_span.is_none() {
        inner.set(Unexpected::Some(unexpected_span));
      }
    }
  }
}

// impl<'a> Display for ParseBuffer<'a> {
//   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//     Display::fmt(&self.cursor().token_stream(), f)
//   }
// }

impl<'a> Debug for ParseBuffer<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    Debug::fmt(&self.cursor().as_ref(), f)
  }
}

/// Cursor state associated with speculative parsing.
///
/// This type is the input of the closure provided to [`ParseStream::step`].
///
/// [`ParseStream::step`]: ParseBuffer::step
#[derive(Copy, Clone)]
pub struct StepCursor<'c, 'a> {
  end: Span,

  // This field is covariant in 'c.
  cursor: Cursor<'c>,

  // This field is contravariant in 'c. Together these make StepCursor
  // invariant in 'c. Also covariant in 'a. The user cannot cast 'c to a
  // different lifetime but can upcast into a StepCursor with a shorter
  // lifetime 'a.
  //
  // As long as we only ever construct a StepCursor for which 'c outlives 'a,
  // this means if ever a StepCursor<'c, 'a> exists we are guaranteed that 'c
  // outlives 'a.
  marker: PhantomData<fn(Cursor<'c>) -> Cursor<'a>>,
}

impl<'c, 'a> Deref for StepCursor<'c, 'a> {
  type Target = Cursor<'c>;

  fn deref(&self) -> &Self::Target {
    &self.cursor
  }
}

impl<'c, 'a> StepCursor<'c, 'a> {
  /// Triggers an error at the current position of the parse stream.
  ///
  /// The `ParseStream::step` invocation will return this same error without
  /// advancing the stream state.
  pub fn error(self, diagnostic: impl Diagnostic + Clone) -> Error {
    debug_assert_eq!(diagnostic.severity(), Severity::Error);
    Error::new_at(self.cursor, diagnostic)
  }
}

pub(crate) fn advance_step_cursor<'c, 'a>(proof: StepCursor<'c, 'a>, to: Cursor<'c>) -> Cursor<'a> {
  // Refer to the comments within the StepCursor definition. We use the
  // fact that a StepCursor<'c, 'a> exists as proof that 'c outlives 'a.
  // Cursor is covariant in its lifetime parameter so we can cast a
  // Cursor<'c> to one with the shorter lifetime Cursor<'a>.
  let _ = proof;
  unsafe { mem::transmute::<Cursor<'c>, Cursor<'a>>(to) }
}

pub(crate) fn new_parse_buffer(
  scope: Span,
  cursor: Cursor,
  unexpected: Rc<Cell<Unexpected>>,
) -> ParseBuffer {
  ParseBuffer {
    end: scope,
    // See comment on `cell` in the struct definition.
    cell: Cell::new(unsafe { mem::transmute::<Cursor, Cursor<'static>>(cursor) }),
    marker: PhantomData,
    unexpected: Cell::new(Some(unexpected)),
  }
}

#[derive(Clone)]
pub(crate) enum Unexpected {
  None,
  Some(Span),
  Chain(Rc<Cell<Unexpected>>),
}

impl Default for Unexpected {
  fn default() -> Self {
    Unexpected::None
  }
}

// We call this on Cell<Unexpected> and Cell<Option<T>> where temporarily
// swapping in a None is cheap.
fn cell_clone<T: Default + Clone>(cell: &Cell<T>) -> T {
  let prev = cell.take();
  let ret = prev.clone();
  cell.set(prev);
  ret
}

fn inner_unexpected(buffer: &ParseBuffer) -> (Rc<Cell<Unexpected>>, Option<Span>) {
  let mut unexpected = get_unexpected(buffer);
  loop {
    match cell_clone(&unexpected) {
      Unexpected::None => return (unexpected, None),
      Unexpected::Some(span) => return (unexpected, Some(span)),
      Unexpected::Chain(next) => unexpected = next,
    }
  }
}

pub(crate) fn get_unexpected(buffer: &ParseBuffer) -> Rc<Cell<Unexpected>> {
  cell_clone(&buffer.unexpected).unwrap()
}

fn span_of_unexpected(mut cursor: Cursor) -> Option<Span> {
  if cursor.eof() {
    None
  } else {
    Some(cursor.span())
  }
}

impl<'a> ParseBuffer<'a> {
  /// Parses a syntax tree node of type `T`, advancing the position of our
  /// parse stream past it.
  pub fn parse<T: Parse>(&self) -> Result<T> {
    T::parse(self)
  }

  /// Calls the given parser function to parse a syntax tree node of type `T`
  /// from this stream.
  pub fn call<T>(&self, function: fn(ParseStream) -> Result<T>) -> Result<T> {
    function(self)
  }

  /// Looks at the next token in the parse stream to determine whether it
  /// matches the requested type of token.
  ///
  /// Does not advance the position of the parse stream.
  pub fn peek<T: Peek>(&self) -> bool {
    T::Token::peek(self.cursor())
  }

  /// Looks at the second-next token in the parse stream.
  ///
  /// This is commonly useful as a way to implement contextual keywords.
  pub fn peek2<T: Peek>(&self) -> bool {
    self.cursor().skip().map_or(false, T::Token::peek)
  }

  /// Parses zero or more occurrences of `T` separated by punctuation of type
  /// `P`, with optional trailing punctuation.
  ///
  /// Parsing continues until the end of this parse stream. The entire content
  /// of this parse stream must consist of `T` and `P`.
  pub fn parse_terminated<T, P: Parse>(
    &self,
    parser: fn(ParseStream) -> Result<T>,
  ) -> Result<Punctuated<T, P>> {
    Punctuated::parse_terminated_with(self, parser)
  }

  /// Returns whether there are tokens remaining in this stream.
  ///
  /// This method returns true at the end of the content of a set of
  /// delimiters, as well as at the very end of the complete macro input.
  pub fn is_empty(&self) -> bool {
    self.cursor().eof()
  }

  /// Constructs a helper for peeking at the next token in this stream and
  /// building an error message if it is not one of a set of expected tokens.
  pub fn lookahead1(&self) -> Lookahead1<'a> {
    Lookahead1::new(self.end, self.cursor())
  }

  /// Forks a parse stream so that parsing tokens out of either the original
  /// or the fork does not advance the position of the other.
  ///
  /// # Performance
  ///
  /// Forking a parse stream is a cheap fixed amount of work and does not
  /// involve copying token buffers. Where you might hit performance problems
  /// is if your macro ends up parsing a large amount of content more than
  /// once.
  pub fn fork(&self) -> Self {
    ParseBuffer {
      end: self.end,
      cell: self.cell.clone(),
      marker: PhantomData,
      // Not the parent's unexpected. Nothing cares whether the clone
      // parses all the way unless we `advance_to`.
      unexpected: Cell::new(Some(Rc::new(Cell::new(Unexpected::None)))),
    }
  }

  /// Triggers an error at the current position of the parse stream.
  pub fn error<T: Diagnostic + Clone>(&self, diagnostic: T) -> Error {
    Error::new_at(self.cursor(), diagnostic)
  }

  /// Speculatively parses tokens from this parse stream, advancing the
  /// position of this stream only if parsing succeeds.
  pub fn step<F, R>(&self, function: F) -> Result<R>
  where
    F: for<'c> FnOnce(StepCursor<'c, 'a>) -> Result<(R, Cursor<'c>)>,
  {
    // Since the user's function is required to work for any 'c, we know
    // that the Cursor<'c> they return is either derived from the input
    // StepCursor<'c, 'a> or from a Cursor<'static>.
    //
    // It would not be legal to write this function without the invariant
    // lifetime 'c in StepCursor<'c, 'a>. If this function were written only
    // in terms of 'a, the user could take our ParseBuffer<'a>, upcast it to
    // a ParseBuffer<'short> which some shorter lifetime than 'a, invoke
    // `step` on their ParseBuffer<'short> with a closure that returns
    // Cursor<'short>, and we would wrongly write that Cursor<'short> into
    // the Cell intended to hold Cursor<'a>.
    //
    // In some cases it may be necessary for R to contain a Cursor<'a>.
    // Within this crate we solve this using `advance_step_cursor` which uses the
    // existence of a StepCursor<'c, 'a> as proof that it is safe to cast
    // from Cursor<'c> to Cursor<'a>. If needed outside of this crate, it would be
    // safe to expose that API as a method on StepCursor.
    let (node, rest) = function(StepCursor {
      end: self.end,
      cursor: self.cell.get(),
      marker: PhantomData,
    })?;
    self.cell.set(rest);
    Ok(node)
  }

  /// Returns the `Span` of the next token in the parse stream.
  pub fn span(&self) -> Span {
    let cursor = self.cursor();
    if cursor.eof() {
      self.end
    } else {
      cursor.span()
    }
  }

  /// Provides low-level access to the token representation underlying this
  /// parse stream.
  ///
  /// Cursors are immutable so no operations you perform against the cursor
  /// will affect the state of this parse stream.
  pub fn cursor(&self) -> Cursor<'a> {
    self.cell.get()
  }

  fn check_unexpected(&self) -> Result<()> {
    match inner_unexpected(self).1 {
      Some(span) => Err(Error::unexpected_token(span)),
      None => Ok(()),
    }
  }
}

impl<T: Parse> Parse for Box<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    input.parse().map(Box::new)
  }
}

impl<T: Parse + Tok> Parse for Option<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    if T::peek(input.cursor()) {
      Ok(Some(input.parse()?))
    } else {
      Ok(None)
    }
  }
}
