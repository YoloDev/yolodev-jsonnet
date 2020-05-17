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

mod parse;
mod syntax_error;

pub use crate::syntax_error::SyntaxError;

pub use jsonnet_parse::{SyntaxKind, T};
pub use rowan::{SmolStr, SyntaxText, TextRange, TextSize, TokenAtOffset, WalkEvent};

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
