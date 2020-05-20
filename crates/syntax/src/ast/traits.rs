//! Various traits that are implemented by ast nodes.

use crate::ast::{AstNode, AstToken};

// use crate::{
//   ast::{self, support, AstChildren, AstNode, AstToken},
//   syntax_node::SyntaxElementChildren,
//   SyntaxToken, T,
// };

// pub trait TypeAscriptionOwner: AstNode {
//   fn ascribed_type(&self) -> Option<ast::TypeRef> {
//     support::child(self.syntax())
//   }
// }

// pub trait NameOwner: AstNode {
//   fn name(&self) -> Option<ast::Name> {
//     support::child(self.syntax())
//   }
// }

#[cfg(feature = "node-description")]
pub enum AstDescription {
  Node(Box<dyn AstDescribe>),
  Token(Box<dyn AstDescribe>),
  List(Box<dyn Iterator<Item = Box<dyn AstDescribe>>>),
}

#[cfg(feature = "node-description")]
pub trait AstDescribe {
  fn describe_span(&self) -> (u32, u32);
  fn describe_kind(&self) -> &str;
  fn describe_children<'a>(
    &'a self,
  ) -> Box<dyn Iterator<Item = (&'static str, Option<AstDescription>)> + 'a>;
}
