//! Syntax Tree library used throughout the jsonnet inerpreter.
//!
//! Properties:
//!   - easy and fast incremental re-parsing
//!   - graceful handling of errors
//!   - full-fidelity representation (*any* text can be precisely represented as
//!     a syntax tree)
//!
//! The most interesting modules here are `syntax_node` (which defines concrete
//! syntax tree) and `ast` (which defines abstract syntax tree on top of the
//! CST). The actual parser live in a separate `jsonnet-parse` crate, and the lexer
//! lives in the `jsonnet-lex` crate (though some mapping of lexing types lives
//! in this crate).

extern crate alloc;

mod parse;
mod syntax_error;
mod syntax_node;

pub mod ast;

pub use crate::{
  ast::{AstNode, AstToken, SourceFile},
  syntax_error::SyntaxError,
  syntax_node::{
    Direction, NodeOrToken, SyntaxElement, SyntaxNode, SyntaxToken, SyntaxTreeBuilder,
  },
};

pub use jsonnet_parse::{SyntaxKind, T};
pub use rowan::{SmolStr, SyntaxText, TextRange, TextSize, TokenAtOffset, WalkEvent};

use crate::syntax_node::GreenNode;
use alloc::sync::Arc;
use core::marker::PhantomData;

/// `Parse` is the result of the parsing: a syntax tree and a collection of
/// errors.
///
/// Note that we always produce a syntax tree, even for completely invalid
/// files.
#[derive(Debug, PartialEq, Eq)]
pub struct Parse<T> {
  green: GreenNode,
  errors: Arc<Vec<SyntaxError>>,
  _ty: PhantomData<fn() -> T>,
}

impl<T> Clone for Parse<T> {
  fn clone(&self) -> Parse<T> {
    Parse {
      green: self.green.clone(),
      errors: self.errors.clone(),
      _ty: PhantomData,
    }
  }
}

impl<T> Parse<T> {
  fn new(green: GreenNode, errors: Vec<SyntaxError>) -> Parse<T> {
    Parse {
      green,
      errors: Arc::new(errors),
      _ty: PhantomData,
    }
  }

  pub fn syntax_node(&self) -> SyntaxNode {
    SyntaxNode::new_root(self.green.clone())
  }
}

impl<T: AstNode> Parse<T> {
  pub fn to_syntax(self) -> Parse<SyntaxNode> {
    Parse {
      green: self.green,
      errors: self.errors,
      _ty: PhantomData,
    }
  }

  pub fn tree(&self) -> T {
    T::cast(self.syntax_node()).unwrap()
  }

  pub fn errors(&self) -> &[SyntaxError] {
    &*self.errors
  }

  pub fn ok(self) -> Result<T, Arc<Vec<SyntaxError>>> {
    if self.errors.is_empty() {
      Ok(self.tree())
    } else {
      Err(self.errors)
    }
  }
}

impl Parse<SyntaxNode> {
  pub fn cast<N: AstNode>(self) -> Option<Parse<N>> {
    if N::cast(self.syntax_node()).is_some() {
      Some(Parse {
        green: self.green,
        errors: self.errors,
        _ty: PhantomData,
      })
    } else {
      None
    }
  }
}

impl Parse<SourceFile> {
  pub fn debug_dump(&self) -> String {
    use core::fmt::Write;

    let mut buf = format!("{:#?}", self.tree().syntax());
    for err in self.errors.iter() {
      write!(buf, "error {:?}: {}\n", err.range(), err).unwrap();
    }

    buf
  }

  // pub fn reparse(&self, indel: &Indel) -> Parse<SourceFile> {
  //     self.incremental_reparse(indel).unwrap_or_else(|| self.full_reparse(indel))
  // }

  // fn incremental_reparse(&self, indel: &Indel) -> Option<Parse<SourceFile>> {
  //     // FIXME: validation errors are not handled here
  //     parsing::incremental_reparse(self.tree().syntax(), indel, self.errors.to_vec()).map(
  //         |(green_node, errors, _reparsed_range)| Parse {
  //             green: green_node,
  //             errors: Arc::new(errors),
  //             _ty: PhantomData,
  //         },
  //     )
  // }

  // fn full_reparse(&self, indel: &Indel) -> Parse<SourceFile> {
  //     let mut text = self.tree().syntax().text().to_string();
  //     indel.apply(&mut text);
  //     SourceFile::parse(&text)
  // }
}

impl SourceFile {
  pub fn parse(text: &str) -> Parse<SourceFile> {
    let (green, errors) = parse::parse_text(text);
    let root = SyntaxNode::new_root(green.clone());

    // if cfg!(debug_assertions) {
    //   validation::validate_block_structure(&root);
    // }

    // errors.extend(validation::validate(&root));

    assert_eq!(root.kind(), SyntaxKind::SOURCE_FILE);
    Parse {
      green,
      errors: Arc::new(errors),
      _ty: PhantomData,
    }
  }
}

/// Matches a `SyntaxNode` against an `ast` type.
///
/// # Example:
///
/// ```ignore
/// match_ast! {
///     match node {
///         ast::CallExpr(it) => { ... },
///         ast::MethodCallExpr(it) => { ... },
///         ast::MacroCall(it) => { ... },
///         _ => None,
///     }
/// }
/// ```
#[macro_export]
macro_rules! match_ast {
  (match $node:ident { $($tt:tt)* }) => { match_ast!(match ($node) { $($tt)* }) };

  (match ($node:expr) {
    $( ast::$ast:ident($it:ident) => $res:expr, )*
    _ => $catch_all:expr $(,)?
  }) => {{
    $( if let Some($it) = ast::$ast::cast($node.clone()) { $res } else )*
    { $catch_all }
  }};
}

#[cfg(test)]
mod tests {
  use super::*;
  use core::fmt;

  #[derive(PartialEq, Eq, Clone, Copy)]
  struct PrettyString<'a>(&'a str);

  impl<'a> PrettyString<'a> {
    #[inline]
    fn new<S: AsRef<str> + ?Sized>(value: &'a S) -> Self {
      PrettyString(value.as_ref())
    }
  }

  impl<'a> fmt::Debug for PrettyString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      f.write_str(self.0)
    }
  }

  macro_rules! assert_eq {
    ($left:expr, $right:expr $(,$($rest:tt)*)?) => {
      pretty_assertions::assert_eq!(
        PrettyString::new($left),
        PrettyString::new($right)
        $(,$($rest)*)?
      );
    }
  }

  #[test_gen::test_golden("test_data/inline/ok/*.jsonnet")]
  fn golden_ok(content: &str, _: &str) -> String {
    let source_file = SourceFile::parse(content);
    std::assert_eq!(
      source_file.errors().len(),
      0,
      "ok files should have no errors"
    );
    source_file.debug_dump()
  }

  #[test_gen::test_golden("test_data/inline/err/*.jsonnet")]
  fn golden_err(content: &str, _: &str) -> String {
    let source_file = SourceFile::parse(content);
    source_file.debug_dump()
  }

  #[test]
  fn tmp() {
    SourceFile::parse("@\"test\"");
  }
}
