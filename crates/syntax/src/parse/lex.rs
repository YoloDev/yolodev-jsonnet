//! Lexer analyzes raw input string and produces lexemes (tokens).
//! It is just a bridge to `jsonnet-lex`.

use core::convert::TryInto;

use crate::{
  SyntaxError,
  SyntaxKind::{self, *},
  TextRange, TextSize, T,
};

/// A token of jsonnet source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token {
  /// The kind of token.
  pub kind: SyntaxKind,

  /// The length of the token.
  pub len: TextSize,
}

/// Break a string up into its component tokens.
/// Beware that it checks for shebang first and its length contributes to resulting
/// tokens offsets.
pub fn tokenize(text: &str) -> (Vec<Token>, Vec<SyntaxError>) {
  if text.is_empty() {
    return Default::default();
  }

  let mut tokens = Vec::new();
  //let mut errors = Vec::new();

  let mut offset = match strip_shebang(text) {
    Some(shebang_len) => {
      tokens.push(Token {
        kind: SHEBANG,
        len: shebang_len.try_into().unwrap(),
      });
      shebang_len
    }
    None => 0,
  };

  let text_without_shebang = &text[offset..];
  for token in jsonnet_lex::tokenize(text_without_shebang) {
    let token_len: TextSize = token.len.try_into().unwrap();
    let token_range = TextRange::at(offset.try_into().unwrap(), token_len);

    todo!()
    // let (syntax_kind, err_message) =
    //         lexer_token_kind_to_syntax_kind(&rustc_token.kind, &text[token_range]);
  }

  todo!()
}

fn strip_shebang(input: &str) -> Option<usize> {
  if !input.starts_with("#!") || input.starts_with("#![") {
    return None;
  }

  Some(input.find('\n').unwrap_or(input.len()))
}
