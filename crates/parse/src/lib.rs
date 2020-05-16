#[macro_use]
mod syntax_kind;
#[macro_use]
mod token_set;
mod event;
mod grammar;
mod parser;

pub(crate) use token_set::TokenSet;

pub use syntax_kind::SyntaxKind;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseError(pub String);

/// `TokenSource` abstracts the source of the tokens parser operates on.
///
/// Hopefully this will allow us to treat text and token trees in the same way!
pub trait TokenSource {
  fn current(&self) -> Token;

  /// Lookahead n token
  fn lookahead_nth(&self, n: usize) -> Token;

  /// bump cursor to next token
  fn bump(&mut self);
}

/// `Token` abstracts the cursor of `TokenSource` operates on.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Token {
  /// What is the current token?
  pub kind: SyntaxKind,
}

/// `TreeSink` abstracts details of a particular syntax tree implementation.
pub trait TreeSink {
  /// Adds new token to the current branch.
  fn token(&mut self, kind: SyntaxKind);

  /// Start new branch and make it current.
  fn start_node(&mut self, kind: SyntaxKind);

  /// Finish current branch and restore previous
  /// branch as current.
  fn finish_node(&mut self);

  fn error(&mut self, error: ParseError);
}

fn parse_from_tokens<S, O, F>(token_source: &mut S, tree_sink: &mut O, f: F)
where
  S: TokenSource,
  O: TreeSink,
  F: FnOnce(&mut parser::Parser<S>),
{
  let mut p = parser::Parser::new(token_source);
  f(&mut p);
  let events = p.finish();
  event::process(tree_sink, events)
}

/// Parse given tokens into the given sink as a jsonnet file.
pub fn parse(token_source: &mut impl TokenSource, tree_sink: &mut impl TreeSink) {
  parse_from_tokens(token_source, tree_sink, grammar::root);
}
