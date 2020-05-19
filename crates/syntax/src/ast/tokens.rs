use crate::{
  ast::AstToken,
  SyntaxKind::{self, *},
  SyntaxToken, TextRange, TextSize,
};
use beef::lean::Cow;
use core::convert::TryFrom;

macro_rules! define_token {
  ($name:ident, $kind:ident) => {
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct $name {
      pub(crate) syntax: SyntaxToken,
    }

    impl core::fmt::Display for $name {
      fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        core::fmt::Display::fmt(&self.syntax, f)
      }
    }

    impl AstToken for $name {
      fn can_cast(kind: SyntaxKind) -> bool {
        kind == $kind
      }

      fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
          Some(Self { syntax })
        } else {
          None
        }
      }

      fn syntax(&self) -> &SyntaxToken {
        &self.syntax
      }
    }
  };
}

define_token!(Whitespace, WHITESPACE);
define_token!(Comment, COMMENT);
define_token!(String, STRING);
define_token!(VerbatimString, VERBATIM_STRING);
define_token!(BlockString, BLOCK_STRING);
//define_token!(Number, NUMBER);

impl Comment {
  pub fn kind(&self) -> CommentKind {
    kind_by_prefix(self.text())
  }

  pub fn prefix(&self) -> &'static str {
    for (prefix, k) in COMMENT_PREFIX_TO_KIND.iter() {
      if *k == self.kind() && self.text().starts_with(prefix) {
        return prefix;
      }
    }

    unreachable!()
  }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CommentKind {
  Line,
  Block,
}

impl CommentKind {
  pub fn is_line(self) -> bool {
    self == Self::Line
  }

  pub fn is_block(self) -> bool {
    self == Self::Block
  }
}

#[rustfmt::skip]
const COMMENT_PREFIX_TO_KIND: &[(&str, CommentKind)] = {
  use CommentKind::*;
  &[
    ("#", Line),
    ("//", Line),
    ("/*", Block),
  ]
};

fn kind_by_prefix(text: &str) -> CommentKind {
  for (prefix, kind) in COMMENT_PREFIX_TO_KIND.iter() {
    if text.starts_with(prefix) {
      return *kind;
    }
  }

  panic!("bad comment text: {:?}", text)
}

impl Whitespace {
  pub fn spans_multiple_lines(&self) -> bool {
    let text = self.text();
    text
      .find('\n')
      .map_or(false, |idx| text[idx + 1..].contains('\n'))
  }
}

pub struct QuoteOffsets {
  pub quotes: [TextRange; 2],
  pub contents: TextRange,
}

impl QuoteOffsets {
  fn from_single_char_quote<'a>(literal: &'a str) -> Option<QuoteOffsets> {
    let quote = {
      let mut chars = literal.chars();
      match chars.next() {
        Some('"') => '"',
        Some('\'') => '\'',
        Some('@') => match chars.next() {
          Some('"') => '"',
          Some('\'') => '\'',
          _ => return None,
        },
        _ => return None,
      }
    };

    let left_quote = literal.find(quote)?;
    let right_quote = literal.rfind(quote)?;
    if left_quote == right_quote {
      // `literal` only contains one quote
      return None;
    }

    let start = TextSize::from(0);
    let left_quote = TextSize::try_from(left_quote).unwrap() + TextSize::of(quote);
    let right_quote = TextSize::try_from(right_quote).unwrap();
    let end = TextSize::of(literal);

    let res = QuoteOffsets {
      quotes: [
        TextRange::new(start, left_quote),
        TextRange::new(right_quote, end),
      ],
      contents: TextRange::new(left_quote, right_quote),
    };

    Some(res)
  }

  fn from_multi_char_quote<'a>(literal: &'a str) -> Option<QuoteOffsets> {
    let quote = "|||";
    let left_quote = literal.find(quote)?;
    let right_quote = literal.rfind(quote)?;
    if left_quote == right_quote {
      // `literal` only contains one quote
      return None;
    }

    let start = TextSize::from(0);
    let left_quote = TextSize::try_from(left_quote).unwrap() + TextSize::of(quote);
    let right_quote = TextSize::try_from(right_quote).unwrap();
    let end = TextSize::of(literal);

    let res = QuoteOffsets {
      quotes: [
        TextRange::new(start, left_quote),
        TextRange::new(right_quote, end),
      ],
      contents: TextRange::new(left_quote, right_quote),
    };

    Some(res)
  }
}

pub trait HasQuotes: AstToken {
  fn quote_offsets(&self) -> Option<QuoteOffsets>;

  fn open_quote_text_range(&self) -> Option<TextRange> {
    self.quote_offsets().map(|it| it.quotes[0])
  }

  fn close_quote_text_range(&self) -> Option<TextRange> {
    self.quote_offsets().map(|it| it.quotes[1])
  }

  fn text_range_between_quotes(&self) -> Option<TextRange> {
    self.quote_offsets().map(|it| it.contents)
  }
}

macro_rules! impl_has_quotes {
  (@impl $name:ident $f:ident) => {
    impl HasQuotes for $name {
      fn quote_offsets(&self) -> Option<QuoteOffsets> {
        let text = self.text().as_str();
        let offsets = QuoteOffsets::$f(text)?;
        let o = self.syntax().text_range().start();
        let offsets = QuoteOffsets {
          quotes: [offsets.quotes[0] + o, offsets.quotes[1] + o],
          contents: offsets.contents + o,
        };
        Some(offsets)
      }
    }
  };

  ($name:ident single) => {
    impl_has_quotes! {
      @impl $name from_single_char_quote
    }
  };

  ($name:ident multi) => {
    impl_has_quotes! {
      @impl $name from_multi_char_quote
    }
  };
}

impl_has_quotes!(String single);
impl_has_quotes!(VerbatimString single);
impl_has_quotes!(BlockString multi);

pub trait HasStringValue: HasQuotes {
  fn value(&self) -> Option<Cow<str>>;
}

impl HasStringValue for String {
  fn value(&self) -> Option<Cow<str>> {
    use jsonnet_lex::unescape::*;

    let text = self.text().as_str();
    let text = &text[self.text_range_between_quotes()? - self.syntax().text_range().start()];

    let mut has_error = false;
    let parts = match unescape_str(text) {
      Unescaped::Original(s) => return Some(Cow::borrowed(s)),
      Unescaped::Parts(p) => p,
    };

    let mut buf = alloc::string::String::with_capacity(text.len() + 2);
    for part in parts {
      match part {
        Part::Str(s) => buf.push_str(s),
        Part::Chr(c) => buf.push(c),
        Part::Err(_) => has_error = true,
      }
    }

    if has_error {
      None
    } else {
      Some(Cow::owned(buf))
    }
  }
}

impl HasStringValue for VerbatimString {
  fn value(&self) -> Option<Cow<str>> {
    use jsonnet_lex::unescape::*;

    let text = self.text().as_str();

    let quote = &text[self.open_quote_text_range()? - self.syntax().text_range().start()];
    let quote = QuoteKind::from_str(quote)?;

    let text = &text[self.text_range_between_quotes()? - self.syntax().text_range().start()];

    let mut has_error = false;
    let parts = match unescape_verbatim_str(text, quote) {
      Unescaped::Original(s) => return Some(Cow::borrowed(s)),
      Unescaped::Parts(p) => p,
    };

    let mut buf = alloc::string::String::with_capacity(text.len() + 2);
    for part in parts {
      match part {
        Part::Str(s) => buf.push_str(s),
        Part::Chr(c) => buf.push(c),
        Part::Err(_) => has_error = true,
      }
    }

    if has_error {
      None
    } else {
      Some(Cow::owned(buf))
    }
  }
}

impl HasStringValue for BlockString {
  fn value(&self) -> Option<Cow<str>> {
    use jsonnet_lex::unescape::*;

    let text = self.text().as_str();
    let text = &text[self.text_range_between_quotes()? - self.syntax().text_range().start()];

    let mut has_error = false;
    let parts = match unescape_block_str(text) {
      Unescaped::Original(s) => return Some(Cow::borrowed(s)),
      Unescaped::Parts(p) => p,
    };

    let mut buf = alloc::string::String::with_capacity(text.len() + 2);
    for part in parts {
      match part {
        Part::Str(s) => buf.push_str(s),
        Part::Chr(c) => buf.push(c),
        Part::Err(_) => has_error = true,
      }
    }

    if has_error {
      None
    } else {
      Some(Cow::owned(buf))
    }
  }
}
