use crate::{
  lex::{span::Span, IntoToken},
  parse::{buffer::Cursor, error::Error as ParseError, lookahead::Peek, Parse, ParseStream},
};
use alloc::rc::Rc;
use core::{
  convert::TryFrom,
  fmt,
  fmt::{Debug, Display, Write},
  hash::{Hash, Hasher},
};
use derive_more::From;

pub(crate) mod private {
  pub trait Sealed {}
}

pub trait Spanned: private::Sealed {
  fn span(&self) -> Span;
}

pub trait Tok: Debug + Display + IntoToken + Spanned + 'static {
  /// Token display name - used for error messages.
  const NAME: &'static str;

  #[inline]
  fn name(&self) -> &'static str {
    Self::NAME
  }

  fn peek(cursor: Cursor) -> bool;
}

macro_rules! impl_from_strings {
  ($ty:ident) => {
    impl From<Rc<str>> for $ty {
      #[inline]
      fn from(name: Rc<str>) -> Self {
        Self::new(name, Span::default())
      }
    }

    impl From<alloc::string::String> for $ty {
      #[inline]
      fn from(name: alloc::string::String) -> Self {
        Self::new(name.as_ref(), Span::default())
      }
    }

    impl From<&str> for $ty {
      #[inline]
      fn from(name: &str) -> Self {
        Self::new(name, Span::default())
      }
    }
  };
}

/// Identifier token
#[derive(Clone)]
pub struct Ident {
  span: Span,
  name: Rc<str>,
}

impl AsRef<str> for Ident {
  fn as_ref(&self) -> &str {
    &self.name
  }
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

impl Display for Ident {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str(&self.name)
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
  const NAME: &'static str = "ident";

  fn peek(cursor: Cursor) -> bool {
    cursor.peek_token::<Self>().is_some()
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
        .token::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl_from_strings!(Ident);

impl Ident {
  pub fn new(name: impl Into<Rc<str>>, span: Span) -> Self {
    // TODO: Validate name isn't a keyword & is a valid identifier
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

  pub fn ident(&self) -> &Rc<str> {
    &self.name
  }
}

/// Number token
#[derive(Clone)]
pub struct Number {
  span: Span,
  value: f64,
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
    Hash::hash(&self.value.to_string(), state)
  }
}

impl Debug for Number {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_tuple("Number").field(&self.value).finish()
  }
}

impl Display for Number {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    Display::fmt(&self.value, f)
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
  const NAME: &'static str = "number";

  fn peek(cursor: Cursor) -> bool {
    cursor.peek_token::<Self>().is_some()
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
        .token::<Self>()
        .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
    })
  }
}

impl Into<f64> for Number {
  fn into(self) -> f64 {
    self.value
  }
}

impl From<f64> for Number {
  fn from(value: f64) -> Self {
    Self::new(value, Span::default())
  }
}

impl Number {
  pub fn new(value: f64, span: Span) -> Self {
    // TODO: Validate number
    Number { value: value, span }
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(value: f64, range: std::ops::Range<usize>) -> Self {
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

impl AsRef<str> for String {
  fn as_ref(&self) -> &str {
    &self.value
  }
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

impl Display for String {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut buf = alloc::string::String::with_capacity(self.value.len() + 2);
    for c in self.value.chars() {
      match c {
        '\t' => buf.push_str("\\t"),
        '\n' => buf.push_str("\\n"),
        '\\' => buf.push_str("\\\\"),
        '\'' => buf.push('\''),
        '"' => buf.push_str("\\\""),
        _ if !crate::utils::printable::is_printable(c) => {
          write!(buf, "\\u{:x}", c as u32)?;
        }
        c => buf.push(c),
      }
    }

    f.write_str(&buf)
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
  const NAME: &'static str = "string";

  fn peek(cursor: Cursor) -> bool {
    cursor.peek_token::<Self>().is_some()
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
        .token::<Self>()
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
  // EndOfFile(EndOfFile),
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
      // Token::EndOfFile(t) => Debug::fmt(t, f),
    }
  }
}

impl Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Token::Ident(t) => Display::fmt(t, f),
      Token::Number(t) => Display::fmt(t, f),
      Token::String(t) => Display::fmt(t, f),
      Token::Keyword(t) => Display::fmt(t, f),
      Token::Operator(t) => Display::fmt(t, f),
      Token::Symbol(t) => Display::fmt(t, f),
      // Token::EndOfFile(t) => Display::fmt(t, f),
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
      // Token::EndOfFile(t) => t.span(),
    }
  }
}

impl Tok for Token {
  const NAME: &'static str = "token";

  fn name(&self) -> &'static str {
    match self {
      Token::Ident(t) => t.name(),
      Token::Number(t) => t.name(),
      Token::String(t) => t.name(),
      Token::Keyword(t) => t.name(),
      Token::Operator(t) => t.name(),
      Token::Symbol(t) => t.name(),
      // Token::EndOfFile(t) => t.name(),
    }
  }

  #[inline]
  fn peek(cursor: Cursor) -> bool {
    cursor.peek_token::<Token>().is_some()
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
        .token::<Self>()
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
// impl_try_from_token!(EndOfFile);

macro_rules! define_token_kind {
  (@impl $name:ident $value:expr ; Parse) => {
    impl Tok for $name {
      const NAME: &'static str = $value;

      fn peek(cursor: Cursor) -> bool {
        cursor.peek_token::<Self>().is_some()
      }
    }

    impl Parse for $name {
      fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
        input.step(|cursor| {
          let cursor = *cursor;
          cursor
            .token::<Self>()
            .ok_or_else(|| ParseError::expected_token(cursor.span(), Self::NAME))
        })
      }
    }

    impl Peek for $name {
      type Token = Self;
    }
  };

  (@impl $name:ident $value:expr ; Group) => {
    impl Tok for $name {
      const NAME: &'static str = $value;

      #[inline]
      fn peek(_: Cursor) -> bool {
        false
      }
    }
  };

  (@append $ctx:tt [$($processed:tt)*] $rest:tt {
    $(token! {
      $(#[$($m:tt)*])*
      $name:ident($($token_trait:ident,)*)
      => $value:expr
    })*
  }) => {
    define_token_kind! {
      @next
      $ctx
      [$($processed)* $({ $(#[$($m)*])* $name($($token_trait,)*) => $value })*]
      $rest
    }
  };

  (@next ($inner:ident $group:ident $group_name:expr) [$({
    $(#[$($m:tt)*])*
    $name:ident($($token_trait:ident,)*) => $value:expr
  })*] {}) => {
    $(
      $(#[$($m)*])*
      #[derive(Clone, Copy)]
      pub struct $name {
        /// Token span
        span: Span,
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

      impl Display for $name {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
          f.write_str($value)
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
        fn into_token(self) -> Result<Token, super::error::ErrorToken> {
          Ok(self.into())
        }
      }

      impl TryFrom<Token> for $name {
        type Error = Token;

        fn try_from(token: Token) -> Result<Self, Self::Error> {
          match token {
            Token::$group($group::$name(t)) => Ok(t),
            t => Err(t),
          }
        }
      }

      impl<'a> TryFrom<&'a Token> for &'a $name {
        type Error = &'a Token;

        fn try_from(token: &'a Token) -> Result<Self, Self::Error> {
          match token {
            Token::$group($group::$name(t)) => Ok(t),
            t => Err(t),
          }
        }
      }

      impl From<$name> for Token {
        #[inline]
        fn from(t: $name) -> Token {
          Token::$group($group::$name(t))
        }
      }

      $(define_token_kind! {
        @impl
        $name
        $value
        ; $token_trait
      })*
    )*

    #[derive(Clone, Copy, PartialEq, Eq, Hash, From)]
    pub enum $group {
      $(
        $(#[$($m)*])*
        $name($name),
      )*
    }

    impl $group {
      #[allow(dead_code)]
      pub(crate) fn get(token: &str, span: Span) -> Option<Self> {
        match token {
          $($value => Some($name::new(span).into()),)*
          _ => None,
        }
      }
    }

    impl private::Sealed for $group {}
    impl Spanned for $group {
      fn span(&self) -> Span {
        match self {
          $(
            Self::$name(t) => t.span(),
          )*
        }
      }
    }

    impl Debug for $group {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Debug::fmt(t, f),
          )*
        }
      }
    }

    impl Display for $group {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
          $(
            Self::$name(t) => Display::fmt(t, f),
          )*
        }
      }
    }

    impl IntoToken for $group {
      #[inline]
      fn into_token(self) -> Result<Token, super::error::ErrorToken> {
        Ok(self.into())
      }
    }

    impl Tok for $group {
      const NAME: &'static str = $group_name;

      fn peek(cursor: Cursor) -> bool {
        $(
          <$name as Tok>::peek(cursor) ||
        )* false
      }
    }
  };

  (@next ($inner:ident $group:ident $group_value:expr) $processed:tt {
    $(#[$($m:tt)*])* $name:ident($($t:tt)*),$($rest:tt)*
  }) => {
    $inner! {
      define_token_kind
      (
        @append
        ($inner $group $group_value)    // context
        $processed  // processed
        {$($rest)*} // rest
      )
      { $(#[$($m)*])* $name($($t)*) }
    }
  };

  ($item_macro:ident !($group:ident, $group_value:expr) $($t:tt)*) => {
    define_token_kind! {
      @next
      ($item_macro $group $group_value) // context
      []                   // processed
      { $($t)* }           // rest
    }
  };
}

macro_rules! token_item {
  ($cont:ident ($($args:tt)*) {
    $(#[$($m:tt)*])* $name:ident($value:expr)
  }) => {
    $cont! {
      $($args)*
      {
        token! { $(#[$($m)*])* $name(Parse,) => $value }
      }
    }
  };
}

macro_rules! symbol_item {
  ($cont:ident ($($args:tt)*) {
    group(
      $(#[$($open_meta:tt)*])*
      $open:ident($open_value:expr),

      $(#[$($close_meta:tt)*])*
      $close:ident($close_value:expr),
    )
  }) => {
    $cont! {
      $($args)*
      {
        token! { $(#[$($open_meta)*])* $open(Parse,) => $open_value }
        token! { $(#[$($close_meta)*])* $close(Group,) => $close_value }
      }
    }
  };

  ($($t:tt)*) => {
    token_item! { $($t)* }
  }
}

macro_rules! define_token_kind_simple {
  (
    $item_macro:ident !($group:ident, $group_value:expr)
    $(
      $value:tt pub struct $name:ident #[$($m:tt)*]
    )*
  ) => {
    define_token_kind! {
      $item_macro!($group, $group_value)
      $(
        #[$($m)*]
        $name($value),
      )*
    }
  };
}

define_token_kind_simple! {
  token_item!(Keyword, "keyword")
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

define_token_kind_simple! {
  token_item!(Operator, "operator")
  "!"               pub struct Not                      /// `!`
  "="               pub struct Assign                   /// `=`
  ":"               pub struct Colon                    /// `:`
  "::"              pub struct DoubleColon              /// `::`
  ":::"             pub struct TripleColon              /// `:::`
  "+:"              pub struct PlusColon                /// `+:`
  "+::"             pub struct PlusDoubleColon          /// `+::`
  "+:::"            pub struct PlusTripleColon          /// `+:::`
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

//trace_macros!(true);
define_token_kind! {
  symbol_item!(Symbol, "symbol")

  group(
    /// `{`
    BraceL("{"),

    /// `}`
    BraceR("}"),
  ),
  group(
    /// `[`
    BracketL("["),

    /// `]`
    BracketR("]"),
  ),
  group(
    /// `(`
    ParenL("\u{0028}"),

    /// `)`
    ParenR("\u{0029}"),
  ),

  /// `,`
  Comma(","),

  ///`.`
  Dot("."),

  /// `;`
  SemiColon(";"),

  /// `$`
  Dollar("$"),
}
trace_macros!(false);

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    lex::span::FileId,
    parse::buffer::{Braces, Brackets, Delimiter, Parentheses},
  };
  use test_case::test_case;

  #[test_case("assert", Assert::new)]
  #[test_case("else", Else::new)]
  #[test_case("error", Error::new)]
  #[test_case("false", False::new)]
  #[test_case("for", For::new)]
  #[test_case("function", Function::new)]
  #[test_case("if", If::new)]
  #[test_case("import", Import::new)]
  #[test_case("importstr", ImportStr::new)]
  #[test_case("in", In::new)]
  #[test_case("local", Local::new)]
  #[test_case("null", Null::new)]
  #[test_case("tailstrict", TailStrict::new)]
  #[test_case("then", Then::new)]
  #[test_case("self", SelfValue::new)]
  #[test_case("super", Super::new)]
  #[test_case("true", True::new)]
  #[test_case("!", Not::new)]
  #[test_case("=", Assign::new)]
  #[test_case(":", Colon::new)]
  #[test_case("::", DoubleColon::new)]
  #[test_case("*", Mul::new)]
  #[test_case("/", Div::new)]
  #[test_case("%", Mod::new)]
  #[test_case("+", Plus::new)]
  #[test_case("-", Minus::new)]
  #[test_case("<<", ShiftLeft::new)]
  #[test_case(">>", ShiftRight::new)]
  #[test_case("<", LessThan::new)]
  #[test_case(">", GreaterThan::new)]
  #[test_case("<=", LessThanOrEqual::new)]
  #[test_case(">=", GreaterThanOrEqual::new)]
  #[test_case("==", Equal::new)]
  #[test_case("!=", NotEqual::new)]
  #[test_case("&", BitAnd::new)]
  #[test_case("^", BitXor::new)]
  #[test_case("|", BitOr::new)]
  #[test_case("&&", And::new)]
  #[test_case("||", Or::new)]
  #[test_case("~", BitNeg::new)]
  #[test_case(",", Comma::new)]
  #[test_case(".", Dot::new)]
  #[test_case(";", SemiColon::new)]
  #[test_case("$", Dollar::new)]
  fn parse_token<T>(content: &str, ctor: impl Fn(Span) -> T)
  where
    T: Parse + Into<Token>,
  {
    let file = FileId::UNKNOWN;
    let expected: Token = ctor(file.span(0..content.len())).into();
    let parsed: T = crate::parse::parse(content, file).expect("parse");
    let parsed: Token = parsed.into();
    assert_eq!(parsed, expected);
  }

  // macro_rules! crate_parse_group_test {
  //   ($name:ident, $content:expr, $kind:ident, $open:expr) => {
  //     #[test]
  //     fn $name() {
  //       #[derive(Debug, PartialEq)]
  //       struct Group {
  //         open: <$kind as Delimiter>::Open,
  //       }

  //       impl Parse for Group {
  //         fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
  //           //assert!(input.peek::<$kind>());

  //           input.step(|cursor| {
  //             let cursor = *cursor;
  //             cursor
  //               .group($kind)
  //               .map(|(cursor, open, _)| (Group { open }, cursor))
  //               .ok_or_else(|| ParseError::expected_token(cursor.span(), stringify!($kind)))
  //           })
  //         }
  //       }

  //       let file = FileId::UNKNOWN;
  //       let expected = Group { open: $open };
  //       let parsed: Group = crate::parse::parse($content, file).expect("parse");
  //       assert_eq!(parsed, expected);
  //     }
  //   };
  // }

  // // NOTE: range is ignored here
  // crate_parse_group_test!(brace_group, "{}", Braces, BraceL::from_range(0..1));

  // // NOTE: range is ignored here
  // crate_parse_group_test!(bracket_group, "[]", Brackets, BracketL::from_range(0..1));

  // // NOTE: range is ignored here
  // crate_parse_group_test!(paren_group, "()", Parentheses, ParenL::from_range(0..1));

  #[derive(Debug, PartialEq)]
  struct Group<D: Delimiter> {
    open: <D as Delimiter>::OpenToken,
    close: <D as Delimiter>::CloseToken,
  }

  impl<D: Delimiter> Parse for Group<D> {
    fn parse(input: ParseStream) -> crate::parse::error::Result<Self> {
      assert!(input.peek::<D>());

      input.step(|cursor| {
        let cursor = *cursor;
        cursor
          .group(D::default())
          .map(|(cursor, open, close, _)| (Group { open, close }, cursor))
          .ok_or_else(|| ParseError::expected_token(cursor.span(), D::NAME))
      })
    }
  }

  #[test_case("{ }", Braces, BraceL::from_range(0..1), BraceR::from_range(2..3))]
  #[test_case("[ ]", Brackets, BracketL::from_range(0..1), BracketR::from_range(2..3))]
  #[test_case("( )", Parentheses, ParenL::from_range(0..1), ParenR::from_range(2..3))]
  fn parse_group_test<D: Delimiter>(content: &str, _: D, open: D::OpenToken, close: D::CloseToken) {
    let file = FileId::UNKNOWN;
    let expected = Group::<D> { open, close };
    let parsed: Group<D> = crate::parse::parse(content, file).expect("parse");
    assert_eq!(parsed, expected);
    assert_eq!(
      (parsed.open.span(), parsed.close.span()),
      (expected.open.span(), expected.close.span())
    );
  }
}
