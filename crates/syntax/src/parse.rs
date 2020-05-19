mod lex;
mod token_sink;
mod token_source;

use crate::{syntax_node::GreenNode, SyntaxError};
use token_sink::TextTreeSink;
use token_source::TextTokenSource;

pub use lex::*;

pub(crate) fn parse_text(text: &str) -> (GreenNode, Vec<SyntaxError>) {
  let (tokens, lexer_errors) = tokenize(&text);

  let mut token_source = TextTokenSource::new(&tokens);
  let mut tree_sink = TextTreeSink::new(text, &tokens);

  jsonnet_parse::parse(&mut token_source, &mut tree_sink);

  let (tree, mut parser_errors) = tree_sink.finish();
  parser_errors.extend(lexer_errors);

  (tree, parser_errors)
}
