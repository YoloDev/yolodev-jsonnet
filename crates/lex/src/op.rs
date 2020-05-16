use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Operator {
  Not,
  Assign,
  Colon,
  DoubleColon,
  TripleColon,
  PlusColon,
  PlusDoubleColon,
  PlusTripleColon,
  Mul,
  Div,
  Mod,
  Plus,
  Minus,
  ShiftLeft,
  ShiftRight,
  LessThan,
  GreaterThan,
  LessThanOrEqual,
  GreaterThanOrEqual,
  Equal,
  NotEqual,
  BitAnd,
  BitXor,
  BitOr,
  BitNeg,
  And,
  Or,
  Unknown,
}

impl Operator {
  fn from_str(s: &str) -> Operator {
    match s {
      "!" => Operator::Not,
      "=" => Operator::Assign,
      ":" => Operator::Colon,
      "::" => Operator::DoubleColon,
      ":::" => Operator::TripleColon,
      "+:" => Operator::PlusColon,
      "+::" => Operator::PlusDoubleColon,
      "+:::" => Operator::PlusTripleColon,
      "*" => Operator::Mul,
      "/" => Operator::Div,
      "%" => Operator::Mod,
      "+" => Operator::Plus,
      "-" => Operator::Minus,
      "<<" => Operator::ShiftLeft,
      ">>" => Operator::ShiftRight,
      "<" => Operator::LessThan,
      ">" => Operator::GreaterThan,
      "<=" => Operator::LessThanOrEqual,
      ">=" => Operator::GreaterThanOrEqual,
      "==" => Operator::Equal,
      "!=" => Operator::NotEqual,
      "&" => Operator::BitAnd,
      "^" => Operator::BitXor,
      "|" => Operator::BitOr,
      "~" => Operator::BitNeg,
      "&&" => Operator::And,
      "||" => Operator::Or,
      _ => Operator::Unknown,
    }
  }
}

pub(super) fn lex_operator<'a>(lex: &mut logos::Lexer<'a, RawToken>) -> Operator {
  Operator::from_str(lex.slice())
}
