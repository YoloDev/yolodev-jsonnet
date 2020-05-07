use crate::{
  lex::{span::Span, token::*, Lexer},
  parse::{error, error::Diagnostic, Peek},
};
use core::{
  convert::TryFrom,
  fmt::Debug,
  marker::{PhantomData, PhantomPinned},
  pin::Pin,
  ptr,
};
use derive_more::{From, TryInto};

pub trait Delimiter:
  private::Sealed + Clone + Copy + Eq + Default + Sized + TryFrom<DelimiterKind> + Peek + Debug
{
  type OpenToken: Tok + Eq + Clone + Copy;
  type CloseToken: Tok + Eq + Clone + Copy;

  const NAME: &'static str;

  fn open_token(span: Span) -> Self::OpenToken;
  fn close_token(span: Span) -> Self::CloseToken;
}

macro_rules! define_delimiter {
  ($name:ident, $open:ty, $close:ty, $display_name:expr) => {
    #[derive(Debug, Default, PartialEq, Eq, Hash, Clone, Copy)]
    pub struct $name;

    impl private::Sealed for $name {}

    impl Delimiter for $name {
      type OpenToken = $open;
      type CloseToken = $close;

      const NAME: &'static str = $display_name;

      #[inline]
      fn open_token(span: Span) -> $open {
        <$open>::new(span)
      }

      #[inline]
      fn close_token(span: Span) -> $close {
        <$close>::new(span)
      }
    }

    impl Peek for $name {
      type Token = $open;
    }
  };
}

define_delimiter!(Braces, BraceL, BraceR, "braces");
define_delimiter!(Brackets, BracketL, BracketR, "brackets");
define_delimiter!(Parentheses, ParenL, ParenR, "parentheses");

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DelimiterEnd {
  Open,
  Close,
}

#[derive(Clone, Copy, Debug, From, TryInto, PartialEq, Eq)]
pub enum DelimiterKind {
  Braces(Braces),
  Brackets(Brackets),
  Parentheses(Parentheses),
}

impl DelimiterKind {
  #[inline]
  pub const fn braces() -> Self {
    Self::Braces(Braces)
  }

  #[inline]
  pub const fn brackets() -> Self {
    Self::Brackets(Brackets)
  }

  #[inline]
  pub const fn parentheses() -> Self {
    Self::Parentheses(Parentheses)
  }

  /// Get delimiter kind for token (if any). Returns the delimiter kind,
  /// and whether or not it's the opening token.
  pub(crate) fn for_token(token: &Token) -> Option<(Self, DelimiterEnd)> {
    match token {
      Token::Symbol(Symbol::BraceL(..)) => Some((DelimiterKind::braces(), DelimiterEnd::Open)),
      Token::Symbol(Symbol::BraceR(..)) => Some((DelimiterKind::braces(), DelimiterEnd::Close)),
      Token::Symbol(Symbol::BracketL(..)) => Some((DelimiterKind::brackets(), DelimiterEnd::Open)),
      Token::Symbol(Symbol::BracketR(..)) => Some((DelimiterKind::brackets(), DelimiterEnd::Close)),
      Token::Symbol(Symbol::ParenL(..)) => Some((DelimiterKind::parentheses(), DelimiterEnd::Open)),
      Token::Symbol(Symbol::ParenR(..)) => {
        Some((DelimiterKind::parentheses(), DelimiterEnd::Close))
      }
      _ => None,
    }
  }

  pub fn open_token(self, span: Span) -> Token {
    match self {
      DelimiterKind::Braces(_) => Braces::open_token(span).into(),
      DelimiterKind::Brackets(_) => Brackets::open_token(span).into(),
      DelimiterKind::Parentheses(_) => Parentheses::open_token(span).into(),
    }
  }

  pub fn close_token(self, span: Span) -> Token {
    match self {
      DelimiterKind::Braces(_) => Braces::close_token(span).into(),
      DelimiterKind::Brackets(_) => Brackets::close_token(span).into(),
      DelimiterKind::Parentheses(_) => Parentheses::close_token(span).into(),
    }
  }
}

#[derive(Clone, Debug)]
struct Group {
  kind: DelimiterKind,
  open_token: Token,
  close_token: Token,
}

/// Internal type which is used instead of `TokenTree` to represent a token tree
/// within a `TokenBuffer`.
enum Entry {
  Group(Group, TokenBuffer),

  // A single token
  Token(Token),

  // End entries contain a raw pointer to the entry from the containing
  // token tree, or null if this is the outermost level.
  End(*const Entry, PhantomPinned),
}

impl Entry {
  fn is_end(&self) -> bool {
    match self {
      Entry::End(..) => true,
      _ => false,
    }
  }
}

/// A buffer that can be efficiently traversed multiple times, unlike
/// `TokenStream` which requires a deep copy in order to traverse more than
/// once.
pub struct TokenBuffer {
  // NOTE: Do not derive clone on this - there are raw pointers inside which
  // will be messed up. Moving the `TokenBuffer` itself is safe as the actual
  // backing slices won't be moved.
  data: Pin<Box<[Entry]>>,
}

/// A buffer that can be efficiently traversed multiple times, unlike
/// `TokenStream` which requires a deep copy in order to traverse more than
/// once.
impl TokenBuffer {
  fn new(mut data: Vec<Entry>) -> Self {
    debug_assert!(!data.iter().any(Entry::is_end));
    data.push(Entry::End(ptr::null(), PhantomPinned));

    let boxed: Box<[Entry]> = data.into();
    let mut pinned: Pin<Box<[Entry]>> = boxed.into();

    // SAFETY: See comment in set_end_ptr.
    unsafe {
      let data: &mut [Entry] = pinned.as_mut().get_unchecked_mut();
      for entry in data.iter_mut() {
        let address = entry as *const Entry;
        if let Entry::Group(g, inner) = entry {
          inner.set_end_ptr(address.offset(1));
        }
      }
    }

    TokenBuffer { data: pinned }
  }

  fn set_end_ptr(&mut self, ptr: *const Entry) {
    debug_assert!({
      let last = self.data.last();

      if let Some(Entry::End(ptr, ..)) = last {
        ptr.is_null()
      } else {
        false
      }
    });

    // SAFETY: No invariants are broken here. Even if some other end
    // entity points to the location of this end entity, we are still
    // keeping the location. Only the content is replaced, by a new,
    // stil valid end entry.
    unsafe {
      let data: &mut [Entry] = self.data.as_mut().get_unchecked_mut();
      *data.last_mut().unwrap() = Entry::End(ptr, PhantomPinned);
    }
  }

  /// Creates a cursor referencing the first token in the buffer and able to
  /// traverse until the end of the buffer.
  pub fn begin(&self) -> Cursor {
    unsafe { Cursor::create(&self.data[0], &self.data[self.data.len() - 1]) }
  }
}

/// A cheaply copyable cursor into a `TokenBuffer`.
///
/// This cursor holds a shared reference into the immutable data which is used
/// internally to represent a `TokenStream`, and can be efficiently manipulated
/// and copied around.
///
/// An empty `Cursor` can be created directly, or one may create a `TokenBuffer`
/// object and get a cursor to its first token with `begin()`.
///
/// Two cursors are equal if they have the same location in the same input
/// stream, and have the same end.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Cursor<'a> {
  // The current token which the `Cursor` is pointing at.
  ptr: *const Entry,

  // The end of the stream.
  end: *const Entry,

  // Cursor is covariant in 'a. This field ensures that our pointers are still
  // valid.
  marker: PhantomData<&'a Token>,
}

impl<'a> Cursor<'a> {
  const EMPTY: Cursor<'a> = {
    // It's safe in this situation for us to put an `Entry` object in global
    // storage, despite it not actually being safe to send across threads
    // (`Ident` and others holds an Rc). This is because this entry only ever
    // holds a `End` entry, with a null pointer`.
    struct UnsafeSyncEntry(Entry);
    unsafe impl Sync for UnsafeSyncEntry {}
    const EMPTY_TOKENS: UnsafeSyncEntry = UnsafeSyncEntry(Entry::End(ptr::null(), PhantomPinned));

    Cursor {
      ptr: &EMPTY_TOKENS.0,
      end: &EMPTY_TOKENS.0,
      marker: PhantomData,
    }
  };

  /// Creates a cursor referencing a static empty TokenStream.
  pub const fn empty() -> Self {
    Cursor::EMPTY
  }

  /// Create a new cursor from it's parts. This silently moves
  /// past Entry::End tokens unless `end` has been reached.
  ///
  /// Safety: Caller must ensure that both ptr and end points to
  /// tokens in the same contigous slice of memory (such that one
  /// can advance ptr and eventually reach end, and ptr will always
  /// point to a valid token) *or* that walking the entry tree, one
  /// will eventually end up at the `end` pointer.
  unsafe fn create(mut ptr: *const Entry, end: *const Entry) -> Self {
    // NOTE: If we're looking at a `End(..)`, we want to advance the cursor
    // past it, unless `ptr == end`, which means that we're at the edge of
    // our cursor's scope.
    while let Entry::End(exit, _) = *ptr {
      if ptr == end {
        break;
      }

      ptr = exit;
    }

    Cursor {
      ptr,
      end,
      marker: PhantomData,
    }
  }

  /// Get the current entry.
  fn entry(self) -> &'a Entry {
    unsafe { &*self.ptr }
  }

  /// Bump the cursor to point at the next token after the current one. This
  /// is undefined behavior if the cursor is currently looking at an
  /// `Token::EndOfFile`.
  unsafe fn bump(self) -> Cursor<'a> {
    Cursor::create(self.ptr.offset(1), self.end)
  }

  /// Checks whether the cursor is currently pointing at the end of its valid
  /// scope.
  pub fn eof(self) -> bool {
    // We're at eof if we're at the end of our scope.
    self.ptr == self.end
  }

  /// If the cursor is pointing at a `Group` with the given delimiter, returns
  /// a cursor into that group and one pointing to the next `TokenTree`.
  pub fn group<D: Delimiter>(
    self,
    _: D,
  ) -> Option<(Cursor<'a>, D::OpenToken, D::CloseToken, Cursor<'a>)> {
    if let Entry::Group(group, buf) = self.entry() {
      if let Ok(_) = D::try_from(group.kind) {
        // SAFETY: bumping should always be safe as long as we're not on an Entry::End.
        return Some((
          buf.begin(),
          D::open_token(group.open_token.span()),
          D::close_token(group.close_token.span()),
          unsafe { self.bump() },
        ));
      }
    }

    None
  }

  pub fn token<T>(self) -> Option<(T, Cursor<'a>)>
  where
    T: Clone,
    for<'tok> &'tok T: TryFrom<&'tok Token>,
  {
    // SAFETY: We have a non-end entry
    self
      .peek_token()
      .map(|t| (t.clone(), unsafe { self.bump() }))
  }

  pub(crate) fn peek_token<T>(self) -> Option<&'a T>
  where
    for<'tok> &'tok T: TryFrom<&'tok Token>,
  {
    let tok = match self.entry() {
      Entry::Token(t) => t,
      Entry::Group(g, ..) => &g.open_token,
      _ => return None,
    };

    match <&T>::try_from(tok) {
      Err(_) => None,
      Ok(t) => Some(t),
    }
  }

  /// Returns the `Span` of the current token.
  pub fn span(self) -> Span {
    match self.entry() {
      Entry::Group(group, _) => group.open_token.span(),
      Entry::Token(t) => t.span(),
      // TODO: find group by end pointer and get span?
      Entry::End(..) => Span::EMPTY,
    }
  }

  /// Skip over the next token without cloning it. Returns `None` if this
  /// cursor points to eof.
  pub(crate) fn skip(self) -> Option<Cursor<'a>> {
    match self.entry() {
      Entry::End(..) => None,
      _ => Some(unsafe { self.bump() }),
    }
  }

  pub(crate) fn iter(self) -> impl Iterator<Item = &'a Token> {
    Iter::new(self)
  }
}

struct Iter<'a> {
  cursor: Cursor<'a>,
  end: *const Entry,
}

impl<'a> Iter<'a> {
  fn new(cursor: Cursor<'a>) -> Self {
    Self {
      cursor,
      end: cursor.end,
    }
  }
}

impl<'a> Iterator for Iter<'a> {
  type Item = &'a Token;

  fn next(&mut self) -> Option<Self::Item> {
    if self.cursor.ptr == self.end {
      return None;
    }

    match self.cursor.entry() {
      Entry::Group(g, content) => {
        self.cursor = content.begin();
        Some(&g.open_token)
      }

      Entry::Token(t) => {
        // SAFETY: token buffers always ends at Entry::End.
        self.cursor = unsafe { self.cursor.bump() };
        Some(t)
      }

      Entry::End(ptr, _) => {
        assert!(!ptr.is_null(), "bad cursor, hit End(ptr::null())");
        let ptr = *ptr;

        // Find end pointer by walking the entries.
        let mut end = ptr;
        loop {
          // SAFETY: All TokenBuffers are guaranteed to end in Entry::End.
          unsafe {
            match &*end {
              Entry::End(..) => break,
              _ => end = end.offset(1),
            }
          }
        }

        // SAFETY: The end pointer of a group should always point to the next token
        // in the outer group, and the end pointer is stored from there.
        self.cursor = unsafe { Cursor::create(ptr, end) };

        // SAFETY: this should always be safe, because the end pointer in a group
        // should always point to the entry *after* the group entry, so going one
        // back should point back at the group.
        let group = unsafe { &*ptr.offset(-1) };
        if let Entry::Group(g, ..) = group {
          Some(&g.close_token)
        } else {
          panic!("bad cursor, end did not point to entry after group");
        }
      }
    }
  }
}

// To simplify parsing, it's split up into several steps.
// The first one is lexing, the second one is grouping (this
// one), in which we build a (very simple) AST that only cares
// about group delimiters. That is; it will only do anything
// with tokens such as `(`, `[` and `{`. This is usefulle,
// because it simplifies parsing in error situations later
// (since we already know where a "block" or "group" of code)
// ends.
pub(crate) fn parse_tree(lex: &mut Lexer, errors: &mut Vec<Box<dyn Diagnostic>>) -> TokenBuffer {
  let mut entries = Vec::new();
  let mut stack = Vec::new();

  while let Some(t) = lex.next() {
    match t {
      Err(e) => errors.push(Box::new(e)),
      Ok(t) => {
        match DelimiterKind::for_token(&t) {
          None => entries.push(Entry::Token(t)),
          Some((kind, DelimiterEnd::Open)) => {
            // opening a new group
            stack.push((kind, t.span(), entries));
            entries = Vec::new();
          }

          Some((kind, DelimiterEnd::Close)) => {
            if stack.iter().rev().any(|(k, ..)| k == &kind) {
              // we loop here in case of wrong closing token
              // example: ({)
              // when we see the end paren here, we assume that
              // the curly is missing, and fabricate it (while
              // producing an error).
              loop {
                let buf = TokenBuffer::new(entries);
                let (expected_kind, open_span, cont) = stack.pop().unwrap();
                let close_span = t.span();
                entries = cont;

                let start_token = expected_kind.open_token(open_span);
                let end_token = expected_kind.close_token(close_span);
                let group = Group {
                  kind: expected_kind,
                  open_token: start_token,
                  close_token: end_token,
                };

                let entry = Entry::Group(group, buf);
                entries.push(entry);

                if kind == expected_kind {
                  break;
                } else {
                  errors.push(Box::new(error::UnexpectedToken::new(close_span)));
                }
              }
            } else {
              // we closed a group that was never opened.
              // report an error, and continue
              errors.push(Box::new(error::UnexpectedToken::new(t.span())));
            }
          }
        }
      }
    }
  }

  while let Some((kind, open_span, cont)) = stack.pop() {
    // unclosed group - close it and report error
    let buf = TokenBuffer::new(entries);
    let close_span = lex.span();
    entries = cont;

    let start_token = kind.open_token(open_span);
    let end_token = kind.close_token(close_span);

    errors.push(Box::new(error::UnexpectedEndOfFile::new(
      error::ExpectedToken1::new(close_span, end_token.name()),
    )));

    let group = Group {
      kind: kind,
      open_token: start_token,
      close_token: end_token,
    };

    let entry = Entry::Group(group, buf);
    entries.push(entry);
  }

  TokenBuffer::new(entries)
}

pub(crate) fn same_scope(a: Cursor, b: Cursor) -> bool {
  a.end == b.end
}

pub(crate) fn open_span_of_group(cursor: Cursor) -> Span {
  match cursor.entry() {
    Entry::Group(group, _) => group.open_token.span(),
    _ => cursor.span(),
  }
}

pub(crate) fn close_span_of_group(cursor: Cursor) -> Span {
  match cursor.entry() {
    Entry::Group(group, _) => group.close_token.span(),
    _ => cursor.span(),
  }
}
