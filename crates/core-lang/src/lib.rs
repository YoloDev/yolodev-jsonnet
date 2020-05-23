extern crate alloc;

mod core_ast;
mod desugar;

pub use crate::{core_ast::*, desugar::desugar};
pub use jsonnet_syntax::TextRange;
