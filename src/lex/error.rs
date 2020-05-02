use crate::{
  lex::{
    span::Span,
    token::{private, Spanned},
    IntoToken,
  },
  parse::error::Diagnostic,
};
use core::{
  fmt,
  fmt::{Debug, Display},
  hash::{Hash, Hasher},
};
use derive_more::From;
use displaydoc::Display;

macro_rules! define_errors {
  ($(pub struct $name:ident #[$doc:meta])*) => {
    #[derive(Copy, Clone, From, PartialEq, Eq, Hash)]
    #[non_exhaustive]
    pub enum ErrorToken {
      $(
        $name($name),
      )*
    }

    impl private::Sealed for ErrorToken {}

    impl Spanned for ErrorToken {
      fn span(&self) -> Span {
        match self {
          $(
            Self::$name(t) => t.span(),
          )*
        }
      }
    }

    impl Debug for ErrorToken {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    impl Display for ErrorToken {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Display::fmt(t, f),
          )*
        }
      }
    }

    impl Diagnostic for ErrorToken {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Diagnostic::fmt(t, f),
          )*
        }
      }
    }

    $(
      #[derive(Copy, Clone, From, Display)]
      #[$doc]
      pub struct $name {
        /// Token span
        pub span: Span,
      }

      impl $name {
        #[inline]
        pub const fn new(span: Span) -> Self {
          Self { span }
        }

        #[cfg(test)]
        #[inline]
        #[allow(dead_code)]
        pub const fn from_range(range: std::ops::Range<usize>) -> Self {
          Self::new(Span::from_range(range))
        }
      }

      impl Default for $name {
        #[inline]
        fn default() -> Self {
          Self::new(Span::default())
        }
      }

      impl Debug for $name {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
          f.write_str(stringify!($name))
        }
      }

      impl PartialEq for $name {
        #[inline]
        fn eq(&self, _other: &Self) -> bool {
          true
        }
      }

      impl Eq for $name {}

      impl Hash for $name {
        fn hash<H: Hasher>(&self, _state: &mut H) {}
      }

      impl private::Sealed for $name {}

      impl Spanned for $name {
        #[inline]
        fn span(&self) -> Span {
          self.span
        }
      }

      impl IntoToken for $name {
        #[inline]
        fn into_token(self) -> Result<super::token::Token, ErrorToken> {
          Err(self.into())
        }
      }

      impl Diagnostic for $name {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
          Display::fmt(self, f)
        }
      }
    )*
  }
}

define_errors! {
  // number errors
  pub struct NumberJunkAfterDecimalPoint        /// Junk after decimal point
  pub struct NumberJunkAfterExponent            /// Junk after exponent
  pub struct NumberJunkAfterExponentSign        /// Junk after exponent sign

  // string errors
  pub struct StringUnterminated                 /// String unterminated
  pub struct UnexpectedEndOfString              /// Unexpected end of string
  // TODO: Here we want data...
  pub struct InvalidEscapeSequence              /// Invalid escape sequence
  // TODO: Here we want data...
  pub struct InvalidUnicodeCodePoint            /// Invalid unicode code point
  pub struct MissingTextBlockTermination        /// Missing text block termination
  pub struct MissingTextBlockIndent             /// Missing text block indent
  pub struct MissingTextBlockNewLine            /// Missing text block newline
  pub struct MissingQuotesAfterAt               /// Missing quotes after @-symbol

  // comment errors
  pub struct CommentTooShort                    /// Comment too short (/*/ is not a valid comment)
  pub struct CommentUnterminated                /// Comment unterminated

  // operator errors
  pub struct InvalidOperator                    /// Invalid operator

  // other
  // TODO: Here we want data...
  pub struct InvalidToken                       /// Invalid token
}
