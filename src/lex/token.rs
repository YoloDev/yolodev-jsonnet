use crate::{
  lex::{span::Span, IntoToken},
  parse::{buffer::Cursor, error::Error as ParseError, lookahead::Peek, Parse, ParseStream},
};
use alloc::rc::Rc;
use core::{
  convert::TryFrom,
  fmt,
  fmt::Debug,
  hash::{Hash, Hasher},
};
use derive_more::From;

pub(crate) mod private {
  pub trait Sealed {}
}

pub trait Spanned: private::Sealed {
  fn span(&self) -> Span;
}

pub trait Tok: IntoToken + Spanned + 'static {
  /// Token display name - used for error messages.
  const NAME: &'static str;
  const EOF: Option<bool>;

  #[inline]
  fn name(&self) -> &'static str {
    Self::NAME
  }

  fn peek(cursor: Cursor) -> bool;
}

/// End of file token
#[derive(Clone, Copy)]
pub struct EndOfFile {
  span: Span,
}

impl PartialEq for EndOfFile {
  #[inline]
  fn eq(&self, _: &EndOfFile) -> bool {
    true
  }
}

impl Eq for EndOfFile {}

impl Hash for EndOfFile {
  #[inline]
  fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl Debug for EndOfFile {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "$EOF")
  }
}

impl private::Sealed for EndOfFile {}
impl Spanned for EndOfFile {
  #[inline]
  fn span(&self) -> Span {
    self.span
  }
}

impl Tok for EndOfFile {
  const EOF: Option<bool> = Some(true);
  const NAME: &'static str = "end of file";

  fn peek(cursor: Cursor) -> bool {
    match cursor.token() {
      Token::EndOfFile(_) => true,
      _ => false,
    }
  }
}

impl IntoToken for EndOfFile {
  #[inline]
  fn into_token(self) -> Result<Token, super::error::ErrorToken> {
    Ok(self.into())
  }
}

impl Peek for EndOfFile {
  type Token = Self;
}

impl Parse for EndOfFile {
  fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
    input.step(|cursor| {
      let cursor = *cursor;
      cursor
        .of_type::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl EndOfFile {
  pub const fn new(span: Span) -> Self {
    EndOfFile { span }
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(range: std::ops::Range<usize>) -> Self {
    Self::new(Span::from_range(range))
  }
}

/// Identifier token
#[derive(Clone)]
pub struct Ident {
  span: Span,
  name: Rc<str>,
}

impl PartialEq for Ident {
  #[inline]
  fn eq(&self, other: &Ident) -> bool {
    PartialEq::eq(&self.name, &other.name)
  }

  #[inline]
  fn ne(&self, other: &Ident) -> bool {
    PartialEq::ne(&self.name, &other.name)
  }
}

impl Eq for Ident {}

impl Hash for Ident {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    Hash::hash(&self.name, state)
  }
}

impl Debug for Ident {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_tuple("Ident").field(&self.name).finish()
  }
}

impl private::Sealed for Ident {}
impl Spanned for Ident {
  #[inline]
  fn span(&self) -> Span {
    self.span
  }
}

impl Tok for Ident {
  const EOF: Option<bool> = Some(false);
  const NAME: &'static str = "ident";

  fn peek(cursor: Cursor) -> bool {
    match cursor.token() {
      Token::Ident(_) => true,
      _ => false,
    }
  }
}

impl IntoToken for Ident {
  #[inline]
  fn into_token(self) -> Result<Token, super::error::ErrorToken> {
    Ok(self.into())
  }
}

impl Peek for Ident {
  type Token = Self;
}

impl Parse for Ident {
  fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
    input.step(|cursor| {
      let cursor = *cursor;
      cursor
        .of_type::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl Ident {
  pub fn new(name: impl Into<Rc<str>>, span: Span) -> Self {
    Ident {
      name: name.into(),
      span,
    }
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(value: impl Into<Rc<str>>, range: std::ops::Range<usize>) -> Self {
    Self::new(value, Span::from_range(range))
  }
}

/// Number token
#[derive(Clone)]
pub struct Number {
  span: Span,
  value: Rc<str>,
}

impl PartialEq for Number {
  #[inline]
  fn eq(&self, other: &Number) -> bool {
    PartialEq::eq(&self.value, &other.value)
  }

  #[inline]
  fn ne(&self, other: &Number) -> bool {
    PartialEq::ne(&self.value, &other.value)
  }
}

impl Eq for Number {}

impl Hash for Number {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    Hash::hash(&self.value, state)
  }
}

impl Debug for Number {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_tuple("Number").field(&self.value).finish()
  }
}

impl private::Sealed for Number {}

impl Spanned for Number {
  #[inline]
  fn span(&self) -> Span {
    self.span
  }
}

impl Tok for Number {
  const EOF: Option<bool> = Some(false);
  const NAME: &'static str = "number";

  fn peek(cursor: Cursor) -> bool {
    match cursor.token() {
      Token::Number(_) => true,
      _ => false,
    }
  }
}

impl IntoToken for Number {
  #[inline]
  fn into_token(self) -> Result<Token, super::error::ErrorToken> {
    Ok(self.into())
  }
}

impl Peek for Number {
  type Token = Self;
}

impl Parse for Number {
  fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
    input.step(|cursor| {
      let cursor = *cursor;
      cursor
        .of_type::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl Number {
  pub fn new(value: impl Into<Rc<str>>, span: Span) -> Self {
    Number {
      value: value.into(),
      span,
    }
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(value: impl Into<Rc<str>>, range: std::ops::Range<usize>) -> Self {
    Self::new(value, Span::from_range(range))
  }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum StringKind {
  DoubleQuoted,
  SingleQuoted,
  DoubleQuotedVerbatim,
  SingleQuotedVerbatim,
  Block,
}

/// String token
#[derive(Clone)]
pub struct String {
  span: Span,
  value: Rc<str>,
  kind: StringKind,
}

impl PartialEq for String {
  #[inline]
  fn eq(&self, other: &String) -> bool {
    PartialEq::eq(&self.value, &other.value) && PartialEq::eq(&self.kind, &other.kind)
  }

  #[inline]
  fn ne(&self, other: &String) -> bool {
    PartialEq::ne(&self.value, &other.value)
  }
}

impl Eq for String {}

impl Hash for String {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    Hash::hash(&self.value, state)
  }
}

impl Debug for String {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_tuple("String")
      .field(&self.value)
      .field(&self.kind)
      .finish()
  }
}

impl private::Sealed for String {}

impl Spanned for String {
  #[inline]
  fn span(&self) -> Span {
    self.span
  }
}

impl Tok for String {
  const EOF: Option<bool> = Some(false);
  const NAME: &'static str = "string";

  fn peek(cursor: Cursor) -> bool {
    match cursor.token() {
      Token::String(_) => true,
      _ => false,
    }
  }
}

impl IntoToken for String {
  #[inline]
  fn into_token(self) -> Result<Token, super::error::ErrorToken> {
    Ok(self.into())
  }
}

impl Peek for String {
  type Token = Self;
}

impl Parse for String {
  fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
    input.step(|cursor| {
      let cursor = *cursor;
      cursor
        .of_type::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl String {
  pub fn new(value: impl Into<Rc<str>>, kind: StringKind, span: Span) -> Self {
    String {
      value: value.into(),
      kind,
      span,
    }
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(
    value: impl Into<Rc<str>>,
    kind: StringKind,
    range: std::ops::Range<usize>,
  ) -> Self {
    Self::new(value, kind, Span::from_range(range))
  }

  #[inline]
  pub fn kind(&self) -> StringKind {
    self.kind
  }

  #[inline]
  pub fn value(&self) -> &str {
    &self.value
  }
}

#[derive(Clone, From, PartialEq, Eq, Hash)]
pub enum Token {
  Ident(Ident),
  Number(Number),
  String(String),
  Keyword(Keyword),
  Operator(Operator),
  Symbol(Symbol),
  EndOfFile(EndOfFile),
}

impl Debug for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str("Token::")?;
    match self {
      Token::Ident(t) => Debug::fmt(t, f),
      Token::Number(t) => Debug::fmt(t, f),
      Token::String(t) => Debug::fmt(t, f),
      Token::Keyword(t) => Debug::fmt(t, f),
      Token::Operator(t) => Debug::fmt(t, f),
      Token::Symbol(t) => Debug::fmt(t, f),
      Token::EndOfFile(t) => Debug::fmt(t, f),
    }
  }
}

impl private::Sealed for Token {}

impl Spanned for Token {
  fn span(&self) -> Span {
    match self {
      Token::Ident(t) => t.span(),
      Token::Number(t) => t.span(),
      Token::String(t) => t.span(),
      Token::Keyword(t) => t.span(),
      Token::Operator(t) => t.span(),
      Token::Symbol(t) => t.span(),
      Token::EndOfFile(t) => t.span(),
    }
  }
}

impl Tok for Token {
  const EOF: Option<bool> = None;
  const NAME: &'static str = "token";

  fn name(&self) -> &'static str {
    match self {
      Token::Ident(t) => t.name(),
      Token::Number(t) => t.name(),
      Token::String(t) => t.name(),
      Token::Keyword(t) => t.name(),
      Token::Operator(t) => t.name(),
      Token::Symbol(t) => t.name(),
      Token::EndOfFile(t) => t.name(),
    }
  }

  #[inline]
  fn peek(_: Cursor) -> bool {
    true
  }
}

impl IntoToken for Token {
  #[inline]
  fn into_token(self) -> Result<Token, super::error::ErrorToken> {
    Ok(self)
  }
}

impl Peek for Token {
  type Token = Self;
}

impl Parse for Token {
  fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
    input.step(|cursor| {
      let cursor = *cursor;
      cursor
        .of_type::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

macro_rules! impl_try_from_token {
  ($case:ident) => {
    impl TryFrom<Token> for $case {
      type Error = Token;

      #[inline]
      fn try_from(token: Token) -> Result<$case, Token> {
        match token {
          Token::$case(t) => Ok(t),
          token => Err(token),
        }
      }
    }

    impl<'a> TryFrom<&'a Token> for &'a $case {
      type Error = &'a Token;

      #[inline]
      fn try_from(token: &'a Token) -> Result<&'a $case, &'a Token> {
        match token {
          Token::$case(t) => Ok(t),
          token => Err(token),
        }
      }
    }
  };
}

impl_try_from_token!(Ident);
impl_try_from_token!(Number);
impl_try_from_token!(String);
impl_try_from_token!(Keyword);
impl_try_from_token!(Operator);
impl_try_from_token!(Symbol);
impl_try_from_token!(EndOfFile);

macro_rules! define_keywords {
  ($($token:tt pub struct $name:ident #[$doc:meta])*) => {
    #[derive(Copy, Clone, From, PartialEq, Eq, Hash)]
    pub enum Keyword {
      $(
        $name($name),
      )*
    }

    impl private::Sealed for Keyword {}

    impl Spanned for Keyword {
      fn span(&self) -> Span {
        match self {
          $(
            Self::$name(t) => t.span(),
          )*
        }
      }
    }

    impl Tok for Keyword {
      const EOF: Option<bool> = Some(false);
      const NAME: &'static str = "keyword";

      fn name(&self) -> &'static str {
        match self {
          $(
            Self::$name(t) => t.name(),
          )*
        }
      }

      fn peek(cursor: Cursor) -> bool {
        match cursor.token() {
          Token::Keyword(_) => true,
          _ => false,
        }
      }
    }

    impl IntoToken for Keyword {
      #[inline]
      fn into_token(self) -> Result<Token, super::error::ErrorToken> {
        Ok(self.into())
      }
    }

    impl Peek for Keyword {
      type Token = Self;
    }

    impl Parse for Keyword {
      fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
        input.step(|cursor| {
          let cursor = *cursor;
          cursor
            .of_type::<Self>()
            .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
        })
      }
    }

    impl Debug for Keyword {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    $(
      #[derive(Copy, Clone, From)]
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

      impl Tok for $name {
        const EOF: Option<bool> = Some(false);
        const NAME: &'static str = $token;

        fn peek(cursor: Cursor) -> bool {
          match cursor.token() {
            Token::Keyword(Keyword::$name(_)) => true,
            _ => false,
          }
        }
      }

      impl IntoToken for $name {
        #[inline]
        fn into_token(self) -> Result<Token, super::error::ErrorToken> {
          Ok(self.into())
        }
      }

      impl Peek for $name {
        type Token = Self;
      }

      impl Parse for $name {
        fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
          input.step(|cursor| {
            let cursor = *cursor;
            cursor
              .of_type::<Self>()
              .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
          })
        }
      }

      impl From<$name> for Token {
        #[inline]
        fn from(t: $name) -> Token {
          Token::Keyword(Keyword::$name(t))
        }
      }

      impl TryFrom<Keyword> for $name {
        type Error = Keyword;

        #[inline]
        fn try_from(keyword: Keyword) -> Result<$name, Keyword> {
          match keyword {
            Keyword::$name(t) => Ok(t),
            kw => Err(kw),
          }
        }
      }

      impl<'a> TryFrom<&'a Keyword> for &'a $name {
        type Error = &'a Keyword;

        #[inline]
        fn try_from(keyword: &'a Keyword) -> Result<&'a $name, &'a Keyword> {
          match keyword {
            Keyword::$name(t) => Ok(t),
            kw => Err(kw),
          }
        }
      }

      impl TryFrom<Token> for $name {
        type Error = Token;

        #[inline]
        fn try_from(token: Token) -> Result<$name, Token> {
          match token {
            Token::Keyword(Keyword::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }

      impl<'a> TryFrom<&'a Token> for &'a $name {
        type Error = &'a Token;

        #[inline]
        fn try_from(token: &'a Token) -> Result<&'a $name, &'a Token> {
          match token {
            Token::Keyword(Keyword::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }
    )*
  }
}

macro_rules! define_operators {
  ($($token:tt pub struct $name:ident #[$doc:meta])*) => {
    #[derive(Copy, Clone, From, PartialEq, Eq, Hash)]
    pub enum Operator {
      $(
        $name($name),
      )*
    }

    impl private::Sealed for Operator {}

    impl Spanned for Operator {
      fn span(&self) -> Span {
        match self {
          $(
            Self::$name(t) => t.span(),
          )*
        }
      }
    }

    impl Tok for Operator {
      const EOF: Option<bool> = Some(false);
      const NAME: &'static str = "operator";

      fn name(&self) -> &'static str {
        match self {
          $(
            Self::$name(t) => t.name(),
          )*
        }
      }

      fn peek(cursor: Cursor) -> bool {
        match cursor.token() {
          Token::Operator(_) => true,
          _ => false,
        }
      }
    }

    impl IntoToken for Operator {
      #[inline]
      fn into_token(self) -> Result<Token, super::error::ErrorToken> {
        Ok(self.into())
      }
    }

    impl Peek for Operator {
      type Token = Self;
    }

    impl Parse for Operator {
      fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
        input.step(|cursor| {
          let cursor = *cursor;
          cursor
            .of_type::<Self>()
            .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
        })
      }
    }

    impl Debug for Operator {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    impl Operator {
      pub fn get(op: &str, span: Span) -> Option<Self> {
        match op {
          $($token => Some(Self::$name($name::new(span))),)*
          _ => None,
        }
      }
    }

    $(
      #[derive(Copy, Clone, From)]
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

      impl Tok for $name {
        const EOF: Option<bool> = Some(false);
        const NAME: &'static str = $token;

        fn peek(cursor: Cursor) -> bool {
          match cursor.token() {
            Token::Operator(Operator::$name(_)) => true,
            _ => false,
          }
        }
      }

      impl IntoToken for $name {
        #[inline]
        fn into_token(self) -> Result<Token, super::error::ErrorToken> {
          Ok(self.into())
        }
      }

      impl Peek for $name {
        type Token = Self;
      }

      impl Parse for $name {
        fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
          input.step(|cursor| {
            let cursor = *cursor;
            cursor
              .of_type::<Self>()
              .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
          })
        }
      }

      impl From<$name> for Token {
        #[inline]
        fn from(t: $name) -> Token {
          Token::Operator(Operator::$name(t))
        }
      }

      impl TryFrom<Operator> for $name {
        type Error = Operator;

        #[inline]
        fn try_from(operator: Operator) -> Result<$name, Operator> {
          match operator {
            Operator::$name(t) => Ok(t),
            op => Err(op),
          }
        }
      }

      impl<'a> TryFrom<&'a Operator> for &'a $name {
        type Error = &'a Operator;

        #[inline]
        fn try_from(operator: &'a Operator) -> Result<&'a $name, &'a Operator> {
          match operator {
            Operator::$name(t) => Ok(t),
            op => Err(op),
          }
        }
      }

      impl TryFrom<Token> for $name {
        type Error = Token;

        #[inline]
        fn try_from(token: Token) -> Result<$name, Token> {
          match token {
            Token::Operator(Operator::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }

      impl<'a> TryFrom<&'a Token> for &'a $name {
        type Error = &'a Token;

        #[inline]
        fn try_from(token: &'a Token) -> Result<&'a $name, &'a Token> {
          match token {
            Token::Operator(Operator::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }
    )*
  };
}

macro_rules! define_symbols {
  ($($token:tt pub struct $name:ident #[$doc:meta])*) => {
    #[derive(Copy, Clone, From, PartialEq, Eq, Hash)]
    pub enum Symbol {
      $(
        $name($name),
      )*
    }

    impl private::Sealed for Symbol {}

    impl Spanned for Symbol {
      fn span(&self) -> Span {
        match self {
          $(
            Self::$name(t) => t.span(),
          )*
        }
      }
    }

    impl Tok for Symbol {
      const EOF: Option<bool> = Some(false);
      const NAME: &'static str = "symbol";

      fn name(&self) -> &'static str {
        match self {
          $(
            Self::$name(t) => t.name(),
          )*
        }
      }

      fn peek(cursor: Cursor) -> bool {
        match cursor.token() {
          Token::Symbol(_) => true,
          _ => false,
        }
      }
    }

    impl IntoToken for Symbol {
      #[inline]
      fn into_token(self) -> Result<Token, super::error::ErrorToken> {
        Ok(self.into())
      }
    }

    impl Peek for Symbol {
      type Token = Self;
    }

    impl Parse for Symbol {
      fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
        input.step(|cursor| {
          let cursor = *cursor;
          cursor
            .of_type::<Self>()
            .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
        })
      }
    }

    impl Debug for Symbol {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    $(
      #[derive(Copy, Clone, From)]
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

      impl Tok for $name {
        const EOF: Option<bool> = Some(false);
        const NAME: &'static str = $token;

        fn peek(cursor: Cursor) -> bool {
          match cursor.token() {
            Token::Symbol(Symbol::$name(_)) => true,
            _ => false,
          }
        }
      }

      impl IntoToken for $name {
        #[inline]
        fn into_token(self) -> Result<Token, super::error::ErrorToken> {
          Ok(self.into())
        }
      }

      impl Peek for $name {
        type Token = Self;
      }

      impl Parse for $name {
        fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
          input.step(|cursor| {
            let cursor = *cursor;
            cursor
              .of_type::<Self>()
              .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
          })
        }
      }

      impl From<$name> for Token {
        #[inline]
        fn from(t: $name) -> Token {
          Token::Symbol(Symbol::$name(t))
        }
      }

      impl TryFrom<Symbol> for $name {
        type Error = Symbol;

        #[inline]
        fn try_from(symbol: Symbol) -> Result<$name, Symbol> {
          match symbol {
            Symbol::$name(t) => Ok(t),
            kw => Err(kw),
          }
        }
      }

      impl<'a> TryFrom<&'a Symbol> for &'a $name {
        type Error = &'a Symbol;

        #[inline]
        fn try_from(symbol: &'a Symbol) -> Result<&'a $name, &'a Symbol> {
          match symbol {
            Symbol::$name(t) => Ok(t),
            kw => Err(kw),
          }
        }
      }

      impl TryFrom<Token> for $name {
        type Error = Token;

        #[inline]
        fn try_from(token: Token) -> Result<$name, Token> {
          match token {
            Token::Symbol(Symbol::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }

      impl<'a> TryFrom<&'a Token> for &'a $name {
        type Error = &'a Token;

        #[inline]
        fn try_from(token: &'a Token) -> Result<&'a $name, &'a Token> {
          match token {
            Token::Symbol(Symbol::$name(t)) => Ok(t),
            token => Err(token),
          }
        }
      }
    )*
  };
}

define_keywords! {
  "assert"          pub struct Assert          /// `assert`
  "else"            pub struct Else            /// `else`
  "error"           pub struct Error           /// `error`
  "false"           pub struct False           /// `false`
  "for"             pub struct For             /// `for`
  "function"        pub struct Function        /// `function`
  "if"              pub struct If              /// `if`
  "import"          pub struct Import          /// `import`
  "importstr"       pub struct ImportStr       /// `importstr`
  "in"              pub struct In              /// `in`
  "local"           pub struct Local           /// `local`
  "null"            pub struct Null            /// `null`
  "tailstrict"      pub struct TailStrict      /// `tailstrict`
  "then"            pub struct Then            /// `then`
  "self"            pub struct SelfValue       /// `self`
  "super"           pub struct Super           /// `super`
  "true"            pub struct True            /// `true`
}

define_operators! {
  "!"               pub struct Not                      /// `!`
  "="               pub struct Assign                   /// `=`
  ":"               pub struct Colon                    /// `:`
  "::"              pub struct DoubleColon              /// `::`
  "*"               pub struct Mul                      /// `*`
  "/"               pub struct Div                      /// `/`
  "%"               pub struct Mod                      /// `%`
  "+"               pub struct Plus                     /// `+`
  "-"               pub struct Minus                    /// `-`
  "<<"              pub struct ShiftLeft                /// `<<`
  ">>"              pub struct ShiftRight               /// `>>`
  "<"               pub struct LessThan                 /// `<`
  ">"               pub struct GreaterThan              /// `>`
  "<="              pub struct LessThanOrEqual          /// `<=`
  ">="              pub struct GreaterThanOrEqual       /// `>=`
  "=="              pub struct Equal                    /// `==`
  "!="              pub struct NotEqual                 /// `!=`
  "&"               pub struct BitAnd                   /// `&`
  "^"               pub struct BitXor                   /// `^`
  "|"               pub struct BitOr                    /// `|`
  "&&"              pub struct And                      /// `&&`
  "||"              pub struct Or                       /// `||`
  "~"               pub struct BitNeg                   /// `~`
}

define_symbols! {
  "{"               pub struct LeftBrace       /// `{`
  "}"               pub struct RightBrace      /// `}`
  "["               pub struct LeftBracket     /// `[`
  "]"               pub struct RightBracket    /// `]`
  "("               pub struct LeftParen       /// `(`
  ")"               pub struct RightParen      /// `)`
  ","               pub struct Comma           /// `,`
  "."               pub struct Dot             /// `.`
  ";"               pub struct SemiColon       /// `;`
  "$"               pub struct Dollar          /// `$`
}
