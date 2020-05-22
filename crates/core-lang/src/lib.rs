extern crate alloc;

mod ast;
mod lowering;

pub use crate::ast::*;
pub use jsonnet_syntax::TextRange;

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
