use core::fmt::{Formatter, Result, Write};

const SPACES: &'static str = "                                                                                                                                                                                                                                                                                                                                    ";

#[inline]
fn spaces(len: usize) -> &'static str {
  &SPACES[0..len]
}

pub(crate) struct IndentFormatter<'a, 'b> {
  /// Currently at the start of a newline
  newline: bool,
  output: &'a mut Formatter<'b>,
  indent: usize,
}

impl<'a, 'b> Write for IndentFormatter<'a, 'b> {
  fn write_str(&mut self, s: &str) -> Result {
    for c in s.chars() {
      if c == '\n' {
        self.output.write_char(c)?;
        self.newline = true;
        continue;
      }

      if self.newline {
        self.output.write_str(spaces(self.indent))?;
      }

      self.output.write_char(c)?;
      self.newline = false;
    }
    Ok(())
  }
}

pub(crate) trait FormatterExt {
  fn indented_with(
    &mut self,
    indent: usize,
    f: impl FnOnce(&mut IndentFormatter) -> Result,
  ) -> Result;

  #[inline]
  fn indented(&mut self, f: impl FnOnce(&mut IndentFormatter) -> Result) -> Result {
    self.indented_with(2, f)
  }
}

impl<'a> FormatterExt for Formatter<'a> {
  #[inline]
  fn indented_with(
    &mut self,
    indent: usize,
    f: impl FnOnce(&mut IndentFormatter) -> Result,
  ) -> Result {
    let mut wrapper = IndentFormatter {
      newline: false,
      output: self,
      indent,
    };

    f(&mut wrapper)
  }
}

impl<'a, 'b> FormatterExt for IndentFormatter<'a, 'b> {
  #[inline]
  fn indented_with(
    &mut self,
    indent: usize,
    f: impl FnOnce(&mut IndentFormatter) -> Result,
  ) -> Result {
    self.indent += indent;
    let ret = f(self);
    self.indent -= indent;
    ret
  }
}
