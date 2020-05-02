use logos::Span;
use std::{
  fmt::Display,
  path::{Path, PathBuf},
  sync::Arc,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Source {
  path: Arc<Path>,
}

impl Default for Source {
  fn default() -> Source {
    let path = PathBuf::from("<unknown>");
    Source {
      path: Arc::from(path),
    }
  }
}

impl Display for Source {
  #[inline]
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Display::fmt(&self.path.display(), f)
  }
}

impl Source {
  #[inline]
  pub fn path(&self) -> &Path {
    &self.path
  }
}

/// A reference to a line and column in an input source file
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct Loc {
  index: usize,
  line: usize,
  col: usize,
}

impl Display for Loc {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}:{}", self.line + 1, self.col + 1)
  }
}

impl Loc {
  const ORIGIN: Self = Self {
    index: 0,
    line: 0,
    col: 0,
  };

  fn new(index: usize, line: usize, col: usize) -> Self {
    debug_assert!(index >= line + col);

    Self { index, line, col }
  }

  /// The index of the character in the input source
  ///
  /// Zero-based index. Take a substring of the original source starting at
  /// this index to access the item pointed to by this `Loc`.
  #[inline]
  pub const fn index(&self) -> usize {
    self.index
  }

  /// The line of the character in the input source
  ///
  /// Zero-based index: the first line is line zero.
  #[inline]
  pub const fn line(&self) -> usize {
    self.line
  }

  /// The column of the character in the input source
  ///
  /// Zero-based index: the first column is column zero.
  #[inline]
  pub const fn column(&self) -> usize {
    self.col
  }
}

impl Default for Loc {
  #[inline]
  fn default() -> Self {
    Loc::ORIGIN
  }
}

/// A reference to a line and column and path
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceLoc {
  source: Source,
  loc: Loc,
}

impl<'a> Display for SourceLoc {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}:{}", self.source, self.loc)
  }
}

impl<'a> SourceLoc {
  fn new(source: Source, loc: Loc) -> Self {
    Self { source, loc }
  }

  /// The index of the character in the input source
  ///
  /// Zero-based index. Take a substring of the original source starting at
  /// this index to access the item pointed to by this `Loc`.
  #[inline]
  pub fn index(&self) -> usize {
    self.loc.index
  }

  /// The line of the character in the input source
  ///
  /// Zero-based index: the first line is line zero.
  #[inline]
  pub fn line(&self) -> usize {
    self.loc.line
  }

  /// The column of the character in the input source
  ///
  /// Zero-based index: the first column is column zero.
  #[inline]
  pub fn column(&self) -> usize {
    self.loc.col
  }

  /// The path to the source file of the given source loc
  #[inline]
  pub fn path(&self) -> &Path {
    self.source.path()
  }
}

/// A reference to a line and column and path
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceSpan<'a> {
  source: &'a Source,
  span: Span,
}

impl<'a> SourceSpan<'a> {
  pub(crate) fn new(source: &'a Source, span: Span) -> Self {
    Self { source, span }
  }

  /// The path to the source file of the given source loc
  #[inline]
  pub fn path(&self) -> &Path {
    self.source.path()
  }

  // #[inline]
  // pub fn start(&self) -> Loc {
  //   self.start
  // }

  // #[inline]
  // pub fn end(&self) -> Loc {
  //   self.end
  // }

  #[inline]
  pub fn source(&self) -> &Source {
    &self.source
  }
}
