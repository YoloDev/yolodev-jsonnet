use crate::lex::{span::Span, token::*};
use core::{marker::PhantomData, mem, slice};
use static_assertions::{assert_impl_all, const_assert};
use std::convert::TryFrom;

/// A buffer that can be efficiently traversed multiple times, unlike
/// `TokenStream` which requires a deep copy in order to traverse more than
/// once.
pub struct TokenBuffer {
  data: Box<[Token]>,
}

/// A buffer that can be efficiently traversed multiple times, unlike
/// `TokenStream` which requires a deep copy in order to traverse more than
/// once.
impl TokenBuffer {
  pub fn new(data: impl Into<Box<[Token]>>) -> Self {
    let data = data.into();
    assert!(data.len() > 0);
    assert_eq!(
      data.last().unwrap(),
      &Token::EndOfFile(EndOfFile::new(Span::EMPTY))
    );
    Self { data: data.into() }
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
  ptr: *const Token,

  // The end of the stream.
  end: *const Token,

  // Cursor is covariant in 'a. This field ensures that our pointers are still
  // valid.
  marker: PhantomData<&'a Token>,
}

impl<'a> Cursor<'a> {
  /// Creates a cursor referencing a static empty TokenStream.
  pub fn empty() -> Self {
    // It's safe in this situation for us to put an `Token` object in global
    // storage, despite it not actually being safe to send across threads
    // (`Ident` and others holds an Rc). This is because this token only ever
    // holds a `EndOfFile` token, which is `Send + Sync`.
    assert_impl_all!(EndOfFile: Send, Sync);

    struct UnsafeSyncToken(Token);
    unsafe impl Sync for UnsafeSyncToken {}
    static EMPTY_TOKENS: UnsafeSyncToken =
      UnsafeSyncToken(Token::EndOfFile(EndOfFile::new(Span::EMPTY)));

    Cursor {
      ptr: &EMPTY_TOKENS.0,
      end: &EMPTY_TOKENS.0,
      marker: PhantomData,
    }
  }

  /// Create a new cursor from it's parts.
  ///
  /// Safety: Caller must ensure that both ptr and end points to
  /// tokens in the same contigous slice of memory (such that one
  /// can advance ptr and eventually reach end, and ptr will always
  /// point to a valid token). `end` has to point to a EndOfFile token,
  /// and that has to be the only EndOfFile token in the entire list.
  unsafe fn create(ptr: *const Token, end: *const Token) -> Self {
    const_assert!(mem::size_of::<Token>() > 0);
    debug_assert_eq!(*end, Token::EndOfFile(EndOfFile::new(Span::EMPTY)));

    Cursor {
      ptr,
      end,
      marker: PhantomData,
    }
  }

  /// Get the current entry.
  pub fn token(self) -> &'a Token {
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

  pub fn of_type<T>(self) -> Option<(T, Cursor<'a>)>
  where
    T: Tok + Clone,
    for<'tok> &'tok T: TryFrom<&'tok Token>,
  {
    let tok = self.token();
    match <&T>::try_from(tok) {
      Err(_) => None,
      Ok(t) => {
        let token = t.clone();
        let cursor = match T::EOF {
          Some(true) => self,
          // SAFETY: If T::EOF is false, we know that we're
          // not at the end of the tokens.
          Some(false) => unsafe { self.bump() },
          None if self.eof() => self,
          // SAFETY: We just checked that we're not at the end
          // of the tokens.
          None => unsafe { self.bump() },
        };
        Some((token, cursor))
      }
    }
  }

  /// Returns the `Span` of the current token.
  pub fn span(self) -> Span {
    self.token().span()
  }

  /// Skip over the next token without cloning it. Returns `None` if this
  /// cursor points to eof.
  pub(crate) fn skip(self) -> Option<Cursor<'a>> {
    match self.token() {
      Token::EndOfFile(_) => None,
      // SAFETY: We just checked that we're not at the end.
      _ => Some(unsafe { self.bump() }),
    }
  }
}

impl<'a> AsRef<[Token]> for Cursor<'a> {
  fn as_ref(&self) -> &[Token] {
    // SAFETY: As long as the invariants are upheld when the Cursor is constructed,
    // this should be safe.
    let len = unsafe { self.end.offset_from(self.ptr) };
    debug_assert!(len >= 0);

    // SAFETY: As long as the invariants are upheld when the Cursor is constructed,
    // this should be safe. We add +1 because we are at length = 1 when there is only
    // the EOF token left (ptr == end).
    unsafe { slice::from_raw_parts(self.ptr, len as usize + 1) }
  }
}
