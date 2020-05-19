//! Abstract Syntax Tree, layered on top of untyped `SyntaxNode`s

mod nodes;
mod tokens;
mod traits;

use crate::{
  syntax_node::{SyntaxNode, SyntaxNodeChildren, SyntaxToken},
  SmolStr, SyntaxKind,
};
use core::marker::PhantomData;

pub use self::{nodes::*, tokens::*, traits::*};

/// The main trait to go from untyped `SyntaxNode`  to a typed ast. The
/// conversion itself has zero runtime cost: ast and syntax nodes have exactly
/// the same representation: a pointer to the tree root and a pointer to the
/// node itself.
pub trait AstNode {
  fn can_cast(kind: SyntaxKind) -> bool
  where
    Self: Sized;

  fn cast(syntax: SyntaxNode) -> Option<Self>
  where
    Self: Sized;

  fn syntax(&self) -> &SyntaxNode;
}

/// Like `AstNode`, but wraps tokens rather than interior nodes.
pub trait AstToken {
  fn can_cast(token: SyntaxKind) -> bool
  where
    Self: Sized;

  fn cast(syntax: SyntaxToken) -> Option<Self>
  where
    Self: Sized;

  fn syntax(&self) -> &SyntaxToken;

  fn text(&self) -> &SmolStr {
    self.syntax().text()
  }
}

/// An iterator over `SyntaxNode` children of a particular AST type.
#[derive(Debug, Clone)]
pub struct AstChildren<N> {
  inner: SyntaxNodeChildren,
  ph: PhantomData<N>,
}

impl<N> AstChildren<N> {
  fn new(parent: &SyntaxNode) -> Self {
    AstChildren {
      inner: parent.children(),
      ph: PhantomData,
    }
  }
}

impl<N: AstNode> Iterator for AstChildren<N> {
  type Item = N;
  fn next(&mut self) -> Option<N> {
    self.inner.by_ref().find_map(N::cast)
  }
}

mod support {
  use super::{AstChildren, AstNode, SyntaxKind, SyntaxNode, SyntaxToken};

  pub(super) fn child<N: AstNode>(parent: &SyntaxNode) -> Option<N> {
    parent.children().find_map(N::cast)
  }

  pub(super) fn children<N: AstNode>(parent: &SyntaxNode) -> AstChildren<N> {
    AstChildren::new(parent)
  }

  pub(super) fn token(parent: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    parent
      .children_with_tokens()
      .filter_map(|it| it.into_token())
      .find(|it| it.kind() == kind)
  }

  pub(super) fn token_any_of(parent: &SyntaxNode, kinds: &[SyntaxKind]) -> Option<SyntaxToken> {
    parent
      .children_with_tokens()
      .filter_map(|it| it.into_token())
      .find(|it| kinds.contains(&it.kind()))
  }
}

#[test]
fn assert_ast_is_object_safe() {
  fn _f(_: &dyn AstNode) {}
}
