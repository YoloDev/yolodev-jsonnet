use core::{cmp, fmt, fmt::Debug, ops};

/// An interned file.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct FileId(usize);

impl FileId {
  pub(crate) const UNKNOWN: FileId = FileId(0);

  pub(crate) fn span(&self, span: std::ops::Range<usize>) -> Span {
    Span::new(*self, Pos(span.start), Pos(span.end))
  }
}

impl Default for FileId {
  #[inline]
  fn default() -> Self {
    FileId::UNKNOWN
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pos(usize);

impl Pos {
  pub const ZERO: Pos = Pos(0);

  #[inline]
  pub(crate) const fn to_usize(&self) -> usize {
    self.0
  }
}

impl Default for Pos {
  #[inline]
  fn default() -> Self {
    Pos::ZERO
  }
}

impl Debug for Pos {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    Debug::fmt(&self.0, f)
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Default, Debug)]
pub struct Span {
  file: FileId,
  start: Pos,
  end: Pos,
}

impl Span {
  pub(crate) const EMPTY: Span = Span {
    file: FileId::UNKNOWN,
    start: Pos::ZERO,
    end: Pos::ZERO,
  };

  pub(crate) fn new(file: FileId, start: Pos, end: Pos) -> Self {
    debug_assert!(start <= end);

    Self { file, start, end }
  }

  #[inline]
  pub(crate) const fn file(&self) -> FileId {
    self.file
  }

  #[inline]
  pub const fn start(&self) -> Pos {
    self.start
  }

  #[inline]
  pub const fn end(&self) -> Pos {
    self.end
  }

  pub const fn len(&self) -> usize {
    self.end.0 - self.start.0
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub const fn from_range(range: std::ops::Range<usize>) -> Self {
    Self {
      file: FileId::UNKNOWN,
      start: Pos(range.start),
      end: Pos(range.end),
    }
  }
}

impl ops::Add for Span {
  type Output = Span;

  fn add(self, rhs: Span) -> Self::Output {
    assert_eq!(self.file, rhs.file);

    Span::new(
      self.file,
      cmp::min(self.start, rhs.start),
      cmp::max(self.end, rhs.end),
    )
  }
}
