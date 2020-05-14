use core::{
  cmp, fmt,
  fmt::Debug,
  ops,
  sync::atomic::{AtomicU16, Ordering},
};

static NEXT_FILE_ID: AtomicU16 = AtomicU16::new(1);

/// An interned file.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct FileId(u16);

impl FileId {
  pub(crate) const UNKNOWN: FileId = FileId(0);

  pub(crate) fn span(&self, span: std::ops::Range<usize>) -> Span {
    Span::new(*self, Pos(span.start as u32), Pos(span.end as u32))
  }

  pub(crate) fn next() -> Self {
    FileId(NEXT_FILE_ID.fetch_add(1, Ordering::SeqCst))
  }
}

impl Default for FileId {
  #[inline]
  fn default() -> Self {
    FileId::UNKNOWN
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pos(u32);

impl Pos {
  pub const ZERO: Pos = Pos(0);

  #[inline]
  pub(crate) const fn to_usize(&self) -> usize {
    self.0 as usize
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
struct SpanRaw(u64);

impl SpanRaw {
  const F_MASK: u64 =
    0b1111_1111_1111_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
  const S_MASK: u64 =
    0b0000_0000_0000_1111_1111_1111_1111_1111_1111_1100_0000_0000_0000_0000_0000_0000;
  const E_MASK: u64 =
    0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0011_1111_1111_1111_1111_1111_1111;

  const F_SHIFT: u64 = 64 - 12;
  const S_SHIFT: u64 = 26;
  const E_SHIFT: u64 = 0;

  const F_MAX: u16 = (SpanRaw::F_MASK >> SpanRaw::F_SHIFT) as u16;
  const S_MAX: u32 = (SpanRaw::S_MASK >> SpanRaw::S_SHIFT) as u32;
  const E_MAX: u32 = (SpanRaw::E_MASK >> SpanRaw::E_SHIFT) as u32;

  const fn new_unchecked(file: FileId, start: Pos, end: Pos) -> Self {
    let file = ((file.0 as u64) << SpanRaw::F_SHIFT) & SpanRaw::F_MASK;
    let start = ((start.0 as u64) << SpanRaw::S_SHIFT) & SpanRaw::S_MASK;
    let end = ((end.0 as u64) << SpanRaw::E_SHIFT) & SpanRaw::E_MASK;

    let raw = file | start | end;
    SpanRaw(raw)
  }

  fn new(file: FileId, start: Pos, end: Pos) -> Self {
    assert!(file.0 < SpanRaw::F_MAX);
    assert!(start.0 < SpanRaw::S_MAX);
    assert!(end.0 < SpanRaw::E_MAX);

    Self::new_unchecked(file, start, end)
  }

  #[inline]
  const fn file(&self) -> FileId {
    FileId(((self.0 & SpanRaw::F_MASK) >> SpanRaw::F_SHIFT) as u16)
  }

  #[inline]
  const fn start(&self) -> Pos {
    Pos(((self.0 & SpanRaw::S_MASK) >> SpanRaw::S_SHIFT) as u32)
  }

  #[inline]
  const fn end(&self) -> Pos {
    Pos(((self.0 & SpanRaw::E_MASK) >> SpanRaw::E_SHIFT) as u32)
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Default, Debug)]
pub struct Span(SpanRaw);

impl Span {
  pub(crate) const EMPTY: Span = Span(SpanRaw(0));

  pub(crate) fn new(file: FileId, start: Pos, end: Pos) -> Self {
    debug_assert!(start <= end);

    Self(SpanRaw::new(file, start, end))
  }

  #[inline]
  pub(crate) const fn file(&self) -> FileId {
    self.0.file()
  }

  #[inline]
  pub const fn start(&self) -> Pos {
    self.0.start()
  }

  #[inline]
  pub const fn end(&self) -> Pos {
    self.0.end()
  }

  pub const fn len(&self) -> u32 {
    self.end().0 - self.start().0
  }

  #[cfg(test)]
  #[inline]
  #[allow(dead_code)]
  pub fn from_range(range: std::ops::Range<usize>) -> Self {
    Self::new(
      FileId::UNKNOWN,
      Pos(range.start as u32),
      Pos(range.end as u32),
    )
  }
}

impl ops::Add for Span {
  type Output = Span;

  fn add(self, rhs: Span) -> Self::Output {
    assert_eq!(self.file(), rhs.file());

    Span::new(
      self.file(),
      cmp::min(self.start(), rhs.start()),
      cmp::max(self.end(), rhs.end()),
    )
  }
}
