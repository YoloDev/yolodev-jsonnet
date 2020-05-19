use jsonnet_parse::{Token as PToken, TokenSource};

use crate::{parse::lex::Token, SyntaxKind::EOF, TextRange, TextSize};

pub(crate) struct TextTokenSource {
  /// non-whitespace/comment tokens
  /// ```non-rust
  /// struct Foo {}
  /// ^^^^^^ ^^^ ^^
  /// ```
  /// tokens: `[struct, Foo, {, }]`
  tokens: Vec<Token>,

  /// Current token and position
  curr: (PToken, usize),
}

impl TokenSource for TextTokenSource {
  fn current(&self) -> PToken {
    self.curr.0
  }

  fn lookahead_nth(&self, n: usize) -> PToken {
    mk_token(self.curr.1 + n, &self.tokens)
  }

  fn bump(&mut self) {
    if self.curr.0.kind == EOF {
      return;
    }

    let pos = self.curr.1 + 1;
    self.curr = (mk_token(pos, &self.tokens), pos);
  }
}

fn mk_token(pos: usize, tokens: &[Token]) -> PToken {
  let kind = tokens.get(pos).map(|t| t.kind).unwrap_or(EOF);

  PToken { kind }
}

impl TextTokenSource {
  /// Generate input from tokens(expect comment and whitespace).
  pub fn new(raw_tokens: &[Token]) -> TextTokenSource {
    let mut tokens = Vec::new();
    for &token in raw_tokens.iter() {
      if !token.kind.is_trivia() {
        tokens.push(token);
      }
    }

    let first = mk_token(0, &tokens);
    TextTokenSource {
      tokens,
      curr: (first, 0),
    }
  }
}
