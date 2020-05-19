//! Lexer analyzes raw input string and produces lexemes (tokens).
//! It is just a bridge to `jsonnet-lex`.

use core::convert::TryInto;

use crate::{
  SyntaxError,
  SyntaxKind::{self, *},
  TextRange, TextSize, T,
};

use jsonnet_lex::TokenKind;

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
  let mut errors = Vec::new();

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

  let text_without_shebang = &text[offset as usize..];
  for token in jsonnet_lex::tokenize(text_without_shebang) {
    let token_len: TextSize = token.len.try_into().unwrap();
    let token_range = TextRange::at(offset.try_into().unwrap(), token_len);

    let (syntax_kind, err_message) =
      lexer_token_kind_to_syntax_kind(token.kind, &text[token_range]);

    tokens.push(Token {
      kind: syntax_kind,
      len: token_len,
    });

    if let Some(err_message) = err_message {
      errors.push(SyntaxError::new(err_message, token_range));
    }

    offset += token.len;
  }

  (tokens, errors)
}

fn strip_shebang(input: &str) -> Option<u32> {
  if !input.starts_with("#!") || input.starts_with("#![") {
    return None;
  }

  Some(input.find('\n').map_or(input.len() as u32, |l| l as u32))
}

/// Returns `SyntaxKind` and an optional tokenize error message.
fn lexer_token_kind_to_syntax_kind(
  token_kind: TokenKind,
  token_text: &str,
) -> (SyntaxKind, Option<&'static str>) {
  let syntax_kind = match token_kind {
    TokenKind::KeywordAssert => T![assert],
    TokenKind::KeywordElse => T![else],
    TokenKind::KeywordError => T![error],
    TokenKind::KeywordFalse => T![false],
    TokenKind::KeywordFor => T![for],
    TokenKind::KeywordFunction => T![function],
    TokenKind::KeywordIf => T![if],
    TokenKind::KeywordImport => T![import],
    TokenKind::KeywordImportStr => T![importstr],
    TokenKind::KeywordIn => T![in],
    TokenKind::KeywordLocal => T![local],
    TokenKind::KeywordNull => T![null],
    TokenKind::KeywordTailStrict => T![tailstrict],
    TokenKind::KeywordThen => T![then],
    TokenKind::KeywordSelf => T![self],
    TokenKind::KeywordSuper => T![super],
    TokenKind::KeywordTrue => T![true],
    TokenKind::Ident => IDENT,
    TokenKind::Number => NUMBER,
    TokenKind::SymbolLeftBrace => T!['{'],
    TokenKind::SymbolRightBrace => T!['}'],
    TokenKind::SymbolLeftBracket => T!['['],
    TokenKind::SymbolRightBracket => T![']'],
    TokenKind::SymbolComma => T![,],
    TokenKind::SymbolDot => T![.],
    TokenKind::SymbolLeftParen => T!['('],
    TokenKind::SymbolRightParen => T![')'],
    TokenKind::SymbolSemi => T![;],
    TokenKind::SymbolDollar => T![$],
    TokenKind::OpNot => T![!],
    TokenKind::OpAssign => T![=],
    TokenKind::OpColon => T![:],
    TokenKind::OpDoubleColon => T![::],
    TokenKind::OpTripleColon => T![:::],
    TokenKind::OpPlusColon => T![+:],
    TokenKind::OpPlusDoubleColon => T![+::],
    TokenKind::OpPlusTripleColon => T![+:::],
    TokenKind::OpMul => T![*],
    TokenKind::OpDiv => T![/],
    TokenKind::OpMod => T![%],
    TokenKind::OpPlus => T![+],
    TokenKind::OpMinus => T![-],
    TokenKind::OpShiftLeft => T![<<],
    TokenKind::OpShiftRight => T![>>],
    TokenKind::OpLessThan => T![<],
    TokenKind::OpGreaterThan => T![>],
    TokenKind::OpLessThanOrEqual => T![<=],
    TokenKind::OpGreaterThanOrEqual => T![>=],
    TokenKind::OpEqual => T![==],
    TokenKind::OpNotEqual => T![!=],
    TokenKind::OpBitAnd => T![&],
    TokenKind::OpBitXor => T![^],
    TokenKind::OpBitOr => T![|],
    TokenKind::OpBitNeg => T![~],
    TokenKind::OpAnd => T![&&],
    TokenKind::OpOr => T![||],
    TokenKind::StringDoubleQuoted => STRING,
    TokenKind::StringSingleQuoted => STRING,
    TokenKind::StringDoubleVerbatim => VERBATIM_STRING,
    TokenKind::StringSingleVerbatim => VERBATIM_STRING,
    TokenKind::StringBlock => BLOCK_STRING,
    TokenKind::Whitespace => WHITESPACE,
    TokenKind::SingelLineSlashComment => COMMENT,
    TokenKind::SingleLineHashComment => COMMENT,
    TokenKind::BlockComment => COMMENT,
    TokenKind::ErrorStringDoubleQuotedUnterminated => {
      return (
        STRING,
        Some("Missing trailing `\"` symbol to terminate the string literal"),
      );
    }
    TokenKind::ErrorStringSingleQuotedUnterminated => {
      return (
        STRING,
        Some("Missing trailing `'` symbol to terminate the string literal"),
      );
    }
    TokenKind::ErrorStringDoubleVerbatimUnterminated => {
      return (
        VERBATIM_STRING,
        Some("Missing trailing `\"` symbol to terminate the string literal"),
      );
    }
    TokenKind::ErrorStringSingleVerbatimUnterminated => {
      return (
        VERBATIM_STRING,
        Some("Missing trailing `'` symbol to terminate the string literal"),
      );
    }
    TokenKind::ErrorStringBlockUnerminated => {
      return (
        BLOCK_STRING,
        Some("Missing trailing `|||` symbol to terminate the string literal"),
      );
    }
    TokenKind::ErrorStringMissingQuotes => {
      return (
        BLOCK_STRING,
        Some("Missing quotes (`'` or `\"`) after @ symbol string"),
      );
    }
    TokenKind::ErrorStringBlockMissingNewLine => {
      return (
        BLOCK_STRING,
        Some("Missing newline in string block literal"),
      );
    }
    TokenKind::ErrorStringBlockMissingTermination => {
      return (
        BLOCK_STRING,
        Some("Missing block termination in string block literal"),
      );
    }
    TokenKind::ErrorStringBlockMissingIndent => {
      return (
        BLOCK_STRING,
        Some("Missing indentation in string block literal"),
      );
    }
    TokenKind::ErrorNumJunkAfterDecimalPoint => {
      return (
        NUMBER,
        Some("Invalid character after decimal point in number literal"),
      );
    }
    TokenKind::ErrorNumJunkAfterExponent => {
      return (
        NUMBER,
        Some("Invalid character after exponent in number literal"),
      );
    }
    TokenKind::ErrorNumJunkAfterExponentSign => {
      return (
        NUMBER,
        Some("Invalid character after exponent sign in number literal"),
      );
    }
    TokenKind::ErrorCommentTooShort => {
      return (COMMENT, Some("Invalid comment sequence"));
    }
    TokenKind::ErrorCommentUnterminated => {
      return (
        COMMENT,
        Some("Missing trailing `*/` symbols to terminate the block comment"),
      );
    }
    TokenKind::ErrorUnknownOperator => {
      return (T![+], Some("Unknown operator"));
    }
    TokenKind::ErrorInvalidToken => PARSE_ERR,
  };

  return (syntax_kind, None);
}
