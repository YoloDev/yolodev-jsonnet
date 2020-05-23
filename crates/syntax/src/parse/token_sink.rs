use core::mem;
use jsonnet_parse::{ParseError, TreeSink};

use crate::{
  parse::Token, syntax_node::GreenNode, SmolStr, SyntaxError, SyntaxKind, SyntaxTreeBuilder,
  TextRange, TextSize,
};

/// Bridges the parser with our specific syntax tree representation.
///
/// `TextTreeSink` also handles attachment of trivia (whitespace & comments)
/// to nodes.
pub(crate) struct TextTreeSink<'a> {
  text: &'a str,
  tokens: &'a [Token],
  text_pos: TextSize,
  token_pos: usize,
  state: State,
  inner: SyntaxTreeBuilder,
}

enum State {
  PendingStart,
  Normal,
  PendingFinish,
}

impl<'a> TreeSink for TextTreeSink<'a> {
  fn token(&mut self, kind: SyntaxKind) {
    match mem::replace(&mut self.state, State::Normal) {
      State::PendingStart => unreachable!(),
      State::PendingFinish => self.inner.finish_node(),
      State::Normal => (),
    }

    self.eat_trivias();
    let len = self.tokens[self.token_pos..self.token_pos + 1]
      .iter()
      .map(|it| it.len)
      .sum::<TextSize>();

    self.do_token(kind, len);
  }

  fn start_node(&mut self, kind: SyntaxKind) {
    match mem::replace(&mut self.state, State::Normal) {
      State::PendingStart => {
        self.inner.start_node(kind);
        // No need to attach trivias to previous node: there is no
        // previous node.
        return;
      }
      State::PendingFinish => self.inner.finish_node(),
      State::Normal => (),
    }

    let n_trivias = self.tokens[self.token_pos..]
      .iter()
      .take_while(|it| it.kind.is_trivia())
      .count();
    let leading_trivias = &self.tokens[self.token_pos..self.token_pos + n_trivias];
    let mut trivia_end = self.text_pos + leading_trivias.iter().map(|it| it.len).sum::<TextSize>();

    let n_attached_trivias = {
      let leading_trivias = leading_trivias.iter().rev().map(|it| {
        let next_end = trivia_end - it.len;
        let range = TextRange::new(next_end, trivia_end);
        trivia_end = next_end;
        (it.kind, &self.text[range])
      });
      n_attached_trivias(kind, leading_trivias)
    };
    self.eat_n_trivias(n_trivias - n_attached_trivias);
    self.inner.start_node(kind);
    self.eat_n_trivias(n_attached_trivias);
  }

  fn finish_node(&mut self) {
    match mem::replace(&mut self.state, State::PendingFinish) {
      State::PendingStart => unreachable!(),
      State::PendingFinish => self.inner.finish_node(),
      State::Normal => (),
    }
  }

  fn error(&mut self, error: ParseError) {
    self.inner.error(error, self.text_pos)
  }
}

impl<'a> TextTreeSink<'a> {
  pub(super) fn new(text: &'a str, tokens: &'a [Token]) -> Self {
    Self {
      text,
      tokens,
      text_pos: 0.into(),
      token_pos: 0,
      state: State::PendingStart,
      inner: SyntaxTreeBuilder::default(),
    }
  }

  pub(super) fn finish(mut self) -> (GreenNode, Vec<SyntaxError>) {
    match mem::replace(&mut self.state, State::Normal) {
      State::PendingFinish => {
        self.eat_trivias();
        self.inner.finish_node()
      }
      State::PendingStart | State::Normal => unreachable!(),
    }

    self.inner.finish_raw()
  }

  fn eat_trivias(&mut self) {
    while let Some(&token) = self.tokens.get(self.token_pos) {
      if !token.kind.is_trivia() {
        break;
      }
      self.do_token(token.kind, token.len);
    }
  }

  fn eat_n_trivias(&mut self, n: usize) {
    for _ in 0..n {
      let token = self.tokens[self.token_pos];
      assert!(token.kind.is_trivia());
      self.do_token(token.kind, token.len);
    }
  }

  fn do_token(&mut self, kind: SyntaxKind, len: TextSize) {
    let range = TextRange::at(self.text_pos, len);
    let text: SmolStr = self.text[range].into();
    self.text_pos += len;
    self.token_pos += 1;
    self.inner.token(kind, text);
  }
}

fn n_attached_trivias<'a>(
  _kind: SyntaxKind,
  _trivias: impl Iterator<Item = (SyntaxKind, &'a str)>,
) -> usize {
  // TODO: Figure out how this is supposed to work
  0
}
