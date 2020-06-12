//! Utilities for validating string and turning them into
//! values they represent.

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum EscapeError {
  EscapeSequenceUnterminated,
  InvalidHexEscapeSequence,
  InvalidUnicodeCodePoint,
  InvalidEscapeSequence,
  UnexpectedEndOfString,
  InvalidVerbatimQuotes,

  BlockMissingNewline,
  BlockMissingIndent,
}

mod private {
  pub trait Sealed {}
}

pub trait Unescape<'a>: private::Sealed {
  fn next_part(&mut self) -> Option<(u32, Part<'a>)>;
}

pub enum Unescaped<'a, T: Unescape<'a>> {
  Original(&'a str),
  Unescaped(T),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Part<'a> {
  Str(&'a str),
  Chr(char),
  Err(EscapeError),
}

macro_rules! impl_itor_for_unescape {
  ($ty:ident) => {
    impl<'a> Iterator for $ty<'a> {
      type Item = Part<'a>;

      fn next(&mut self) -> Option<Self::Item> {
        if let Some((_len, part)) = self.next_part() {
          Some(part)
        } else {
          None
        }
      }
    }
  };
}

/// Takes a contents of a string literal (without quotes) and produces a
/// sequence of escaped characters or errors.
pub fn unescape_str(literal_text: &str) -> Unescaped<Normal> {
  match State::from_normal_str(literal_text) {
    State::End => Unescaped::Original(literal_text),
    state => Unescaped::Unescaped(Normal {
      rest: literal_text,
      state,
    }),
  }
}

pub struct Normal<'a> {
  rest: &'a str,
  state: State,
}

enum State {
  Text(usize),
  Escaped,
  End,
}

impl State {
  fn from_normal_str(s: &str) -> Self {
    match s.find('\\') {
      None => State::End,
      Some(0) => State::Escaped,
      Some(i) => State::Text(i),
    }
  }
}

fn escaped_unicode_seq(s: &str) -> Part {
  // hex chars are always ASCII, and jsonnet requires exactly
  // 4 of them. This *should* be enforced in the caller, but
  // we do a debug_assert here for, well, debugging.
  debug_assert_eq!(s.len(), 4);

  let hex_num = match u32::from_str_radix(s, 16) {
    Ok(n) => n,
    Err(_) => {
      return Part::Err(EscapeError::InvalidHexEscapeSequence);
    }
  };

  let chr = match std::char::from_u32(hex_num) {
    Some(c) => c,
    None => {
      return Part::Err(EscapeError::InvalidUnicodeCodePoint);
    }
  };

  Part::Chr(chr)
}

impl_itor_for_unescape!(Normal);
impl<'a> private::Sealed for Normal<'a> {}
impl<'a> Unescape<'a> for Normal<'a> {
  fn next_part(&mut self) -> Option<(u32, Part<'a>)> {
    let s = self.rest;

    if s.is_empty() {
      return None;
    }

    match self.state {
      State::End => Some((s.len() as u32, Part::Str(s))),

      State::Text(i) => {
        debug_assert_ne!(s.as_bytes()[0], b'\\');

        let (text, rest) = s.split_at(i);
        self.state = State::Escaped;
        self.rest = rest;
        Some((i as u32, Part::Str(text)))
      }

      State::Escaped => {
        debug_assert_eq!(s.as_bytes()[0], b'\\');

        if s.len() == 1 {
          self.state = State::End;
          self.rest = "";
          return Some((1, Part::Err(EscapeError::EscapeSequenceUnterminated)));
        }

        let escaped = s.as_bytes()[1];
        let mut escaped_len = 1;
        let part = match escaped {
          b'"' => Part::Chr('"'),
          b'\'' => Part::Chr('\''),
          b'\\' => Part::Chr('\\'),
          b'/' => Part::Chr('/'),
          b'b' => Part::Chr('\x08'),
          b'f' => Part::Chr('\x0c'),
          b'n' => Part::Chr('\n'),
          b'r' => Part::Chr('\r'),
          b't' => Part::Chr('\t'),
          b'u' => {
            escaped_len = 5;
            if s.len() < 6 {
              escaped_len = s.len() - 1;
              Part::Err(EscapeError::EscapeSequenceUnterminated)
            } else {
              escaped_unicode_seq(&s[2..6])
            }
          }

          _ => Part::Err(EscapeError::InvalidEscapeSequence),
        };

        let len = escaped_len + 1;
        self.rest = &s[len..];
        self.state = State::from_normal_str(self.rest);
        Some((len as u32, part))
      }
    }
  }
}

#[inline]
pub fn unescape_verbatim_single_quoted_str(literal_text: &str) -> Unescaped<Verbatim> {
  unescape_verbatim_str(literal_text, QuoteKind::Single)
}

#[inline]
pub fn unescape_verbatim_double_quoted_str(literal_text: &str) -> Unescaped<Verbatim> {
  unescape_verbatim_str(literal_text, QuoteKind::Double)
}

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub enum QuoteKind {
  Single,
  Double,
}

impl QuoteKind {
  #[inline]
  fn char(self) -> char {
    match self {
      QuoteKind::Double => '"',
      QuoteKind::Single => '\'',
    }
  }

  #[inline]
  fn byte(self) -> u8 {
    match self {
      QuoteKind::Double => b'"',
      QuoteKind::Single => b'\'',
    }
  }

  #[inline]
  #[allow(clippy::should_implement_trait)]
  pub fn from_str(s: &str) -> Option<Self> {
    match s {
      "'" => Some(QuoteKind::Single),
      "\"" => Some(QuoteKind::Double),
      _ => None,
    }
  }
}

pub fn unescape_verbatim_str(literal_text: &str, quote_kind: QuoteKind) -> Unescaped<Verbatim> {
  match State::from_verbatim_str(literal_text, quote_kind) {
    State::End => Unescaped::Original(literal_text),
    state => Unescaped::Unescaped(Verbatim {
      rest: literal_text,
      state,
      quote: quote_kind,
    }),
  }
}

pub struct Verbatim<'a> {
  rest: &'a str,
  quote: QuoteKind,
  state: State,
}

impl State {
  fn from_verbatim_str(s: &str, kind: QuoteKind) -> Self {
    match s.find(kind.char()) {
      None => State::End,
      Some(0) => State::Escaped,
      Some(i) => State::Text(i),
    }
  }
}

impl_itor_for_unescape!(Verbatim);
impl<'a> private::Sealed for Verbatim<'a> {}
impl<'a> Unescape<'a> for Verbatim<'a> {
  fn next_part(&mut self) -> Option<(u32, Part<'a>)> {
    let s = self.rest;

    if s.is_empty() {
      return None;
    }

    match self.state {
      State::End => Some((s.len() as u32, Part::Str(s))),

      State::Text(i) => {
        debug_assert_ne!(s.as_bytes()[0], self.quote.byte());

        let (text, rest) = s.split_at(i);
        self.state = State::Escaped;
        self.rest = rest;
        Some((i as u32, Part::Str(text)))
      }

      State::Escaped => {
        debug_assert_eq!(s.as_bytes()[0], self.quote.byte());

        let (rest, part) = if s.len() < 2 {
          ("", Part::Err(EscapeError::UnexpectedEndOfString))
        } else if s.as_bytes()[1] != self.quote.byte() {
          (&s[1..], Part::Err(EscapeError::InvalidVerbatimQuotes))
        } else {
          (&s[2..], Part::Chr(self.quote.char()))
        };

        self.state = State::from_verbatim_str(rest, self.quote);
        self.rest = rest;
        Some((rest.len() as u32, part))
      }
    }
  }
}

enum BlockState<'a> {
  Start,
  ComputeIdent,
  Line(&'a str),
}

pub struct Block<'a> {
  rest: &'a str,
  state: BlockState<'a>,
}

pub fn unescape_block_str(literal_text: &str) -> Unescaped<Block> {
  Unescaped::Unescaped(Block {
    rest: literal_text,
    state: BlockState::Start,
  })
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

struct Ctx<'a>(&'a str);

impl<'a> Ctx<'a> {
  fn eat_while(&mut self, f: impl Fn(char) -> bool) -> Option<&'a str> {
    match self.0.find(|c| !f(c)) {
      None => {
        let old = self.0;
        self.0 = "";
        Some(old)
      }

      Some(0) => None,
      Some(i) => {
        let (eaten, rest) = self.0.split_at(i);
        self.0 = rest;
        Some(eaten)
      }
    }
  }

  fn eat_lines(&mut self) -> Option<&'a str> {
    self.0.find('\n').map(|i| {
      let (eaten, rest) = self.0.split_at(i + 1);
      match rest.find(|c| c != '\n') {
        None => {
          self.0 = rest;
          eaten
        }
        Some(l) => {
          let (eaten, rest) = self.0.split_at(i + l + 1);
          self.0 = rest;
          eaten
        }
      }
    })
  }

  fn skip(&mut self, n: usize) {
    self.0 = &self.0[n..];
  }

  fn next(&mut self) -> Option<char> {
    match self.0.chars().next() {
      None => None,
      Some(c) => {
        self.0 = &self.0[c.len_utf8()..];
        Some(c)
      }
    }
  }
}

impl_itor_for_unescape!(Block);
impl<'a> private::Sealed for Block<'a> {}
impl<'a> Unescape<'a> for Block<'a> {
  fn next_part(&mut self) -> Option<(u32, Part<'a>)> {
    let s = self.rest;

    if s.is_empty() {
      return None;
    }

    let mut ctx = Ctx(s);

    loop {
      match self.state {
        BlockState::Start => {
          // First, we need to figure out how much indentation we're using as our baseline

          // Skip whitespaces
          ctx.eat_while(|r| r == ' ' || r == '\t' || r == '\r');

          // Skip \n
          match ctx.next() {
            Some('\n') => (),
            None => {
              self.rest = "";
              return Some((
                s.len() as u32,
                Part::Err(EscapeError::UnexpectedEndOfString),
              ));
            }
            Some(_) => {
              self.rest = "";
              return Some((s.len() as u32, Part::Err(EscapeError::BlockMissingNewline)));
            }
          }

          // Process leading blank lines before calculating string block indent.
          // If we found any newlines here, we need to immediately return a part
          // to avoid having to create a buffer, because these newlines should be
          // included in the string output.
          if let Some(lines) = ctx.eat_while(|c| c == '\n') {
            self.state = BlockState::ComputeIdent;
            self.rest = ctx.0;
            return Some(((s.len() - ctx.0.len()) as u32, Part::Str(lines)));
          }

          // If not; we want to immediately continue to compute the ident.
          self.state = BlockState::ComputeIdent;
          continue;
        }

        BlockState::ComputeIdent => {
          let num_whitespace = check_whitespace(ctx.0, ctx.0);
          let str_block_indent = &ctx.0[..num_whitespace];

          if num_whitespace == 0 {
            // Text block's first line must start with whitespace
            self.rest = "";
            return Some((s.len() as u32, Part::Err(EscapeError::BlockMissingIndent)));
          }

          self.state = BlockState::Line(str_block_indent);
          continue;
        }

        BlockState::Line(str_block_indent) => {
          debug_assert!(!str_block_indent.is_empty());
          ctx.skip(str_block_indent.len());

          let lines = match ctx.eat_lines() {
            None => {
              self.rest = "";
              return Some((
                s.len() as u32,
                Part::Err(EscapeError::UnexpectedEndOfString),
              ));
            }
            Some(l) => l,
          };

          // Look at the next line
          let num_whitespace = check_whitespace(str_block_indent, ctx.0);
          if num_whitespace == 0 {
            // End of the text block
            self.rest = "";
            return Some((s.len() as u32, Part::Str(lines)));
          }

          // keep the current state, but advance the string
          self.rest = ctx.0;
          return Some(((s.len() - ctx.0.len()) as u32, Part::Str(lines)));
        }
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  pub trait IntoString {
    fn into_string(self) -> Result<String, EscapeError>;
  }

  impl<'a, T: Unescape<'a> + Iterator<Item = Part<'a>>> IntoString for T {
    fn into_string(self) -> Result<String, EscapeError> {
      let mut buf = String::new();
      for part in self {
        match part {
          Part::Str(s) => buf.push_str(s),
          Part::Chr(c) => buf.push(c),
          Part::Err(e) => return Err(e),
        }
      }

      Ok(buf)
    }
  }

  impl<'a, T: Unescape<'a> + IntoString> Unescaped<'a, T> {
    fn into_string(self) -> Result<String, EscapeError> {
      match self {
        Unescaped::Original(s) => Ok(s.to_owned()),
        Unescaped::Unescaped(p) => p.into_string(),
      }
    }
  }

  mod strings {
    use super::*;
    use test_case::test_case;

    #[test_case("" ; "empty")]
    #[test_case("test")]
    #[test_case("even with quotes\"")]
    fn original(s: &str) {
      match unescape_str(s) {
        Unescaped::Original(_) => (),
        Unescaped::Unescaped(_) => panic!("expected original for string '{}'", s),
      }
    }

    #[test_case("hi" => "hi" ; "simple")]
    #[test_case("hi\n" => "hi\n" ; "with newline")]
    #[test_case("hi\\\"" => "hi\"" ; "with escaped double quote")]
    #[test_case("hi\\'" => "hi'" ; "with escaped single quote")]
    #[test_case("hi\\u0020" => "hi " ; "with escaped unicode sequence")]
    fn validate(s: &str) -> String {
      unescape_str(s).into_string().unwrap()
    }
  }

  mod verbatim {
    use super::*;
    use test_case::test_case;

    #[test_case("" ; "empty")]
    #[test_case("test")]
    #[test_case("even with escape sequences \\n")]
    fn original(s: &str) {
      match unescape_verbatim_double_quoted_str(s) {
        Unescaped::Original(_) => (),
        Unescaped::Unescaped(_) => panic!("expected original for string '{}'", s),
      }

      match unescape_verbatim_single_quoted_str(s) {
        Unescaped::Original(_) => (),
        Unescaped::Unescaped(_) => panic!("expected original for string '{}'", s),
      }
    }

    #[test_case("hi" => "hi" ; "simple")]
    #[test_case("hi\n" => "hi\n" ; "with newline")]
    #[test_case("hi\"\"" => "hi\"" ; "with escaped double quote")]
    #[test_case("hi''" => "hi''" ; "with escaped single quote")]
    #[test_case("hi\\u0020" => "hi\\u0020" ; "with escaped unicode sequence")]
    fn validate_double_quoted(s: &str) -> String {
      unescape_verbatim_double_quoted_str(s)
        .into_string()
        .unwrap()
    }

    #[test_case("hi" => "hi" ; "simple")]
    #[test_case("hi\n" => "hi\n" ; "with newline")]
    #[test_case("hi\"\"" => "hi\"\"" ; "with escaped double quote")]
    #[test_case("hi''" => "hi'" ; "with escaped single quote")]
    #[test_case("hi\\u0020" => "hi\\u0020" ; "with escaped unicode sequence")]
    fn validate_single_quoted(s: &str) -> String {
      unescape_verbatim_single_quoted_str(s)
        .into_string()
        .unwrap()
    }
  }

  mod block {
    use super::*;
    use test_case::test_case;

    #[test_case("\n  test\n    more\n  |||\n    foo\n" => "test\n  more\n|||\n  foo\n" ; "only spaces")]
    #[test_case("\n\ttest\n\t  more\n\t|||\n\t  foo\n" => "test\n  more\n|||\n  foo\n" ; "tabs and spaces")]
    #[test_case("\n\t  \ttest\n\t  \t  more\n\t  \t|||\n\t  \t  foo\n" => "test\n  more\n|||\n  foo\n" ; "with internal delimeter")]
    #[test_case("\n\n  test\n\n\n    more\n  |||\n    foo\n" => "\ntest\n\n\n  more\n|||\n  foo\n" ; "multiple newlines after one another")]
    fn validate_block(s: &str) -> String {
      unescape_block_str(s).into_string().unwrap()
    }
  }
}
