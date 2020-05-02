use crate::{
  ast::{full::*, punctuated::Punctuated},
  lex::{
    error::{Diagnostic, ErrorToken},
    span::Span,
    token::*,
    Lexer,
  },
};
use core::{convert::TryInto, fmt, marker::PhantomData, ops};
use smallvec::SmallVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Precedence(u8);

impl ops::Sub<u8> for Precedence {
  type Output = Precedence;

  #[inline]
  fn sub(self, rhs: u8) -> Self::Output {
    debug_assert!(self.0 >= rhs);
    Precedence(self.0 - rhs)
  }
}

impl Precedence {
  // SAFETY: None of these are 0
  const MIN: Self = Precedence(0);
  const APPLY: Self = Precedence(2);
  const UNARY: Self = Precedence(4);
  const MAX: Self = Precedence(16);

  fn for_bin_op(op: BinaryOperatorKind) -> Precedence {
    match op {
      BinaryOperatorKind::Mul => Precedence(5),
      BinaryOperatorKind::Div => Precedence(5),
      BinaryOperatorKind::Mod => Precedence(5),
      BinaryOperatorKind::Plus => Precedence(6),
      BinaryOperatorKind::Minus => Precedence(6),
      BinaryOperatorKind::ShiftLeft => Precedence(7),
      BinaryOperatorKind::ShiftRight => Precedence(7),
      BinaryOperatorKind::GreaterThan => Precedence(8),
      BinaryOperatorKind::GreaterThanOrEqual => Precedence(8),
      BinaryOperatorKind::LessThan => Precedence(8),
      BinaryOperatorKind::LessThanOrEqual => Precedence(8),
      BinaryOperatorKind::In => Precedence(8),
      BinaryOperatorKind::Equal => Precedence(9),
      BinaryOperatorKind::NotEqual => Precedence(9),
      BinaryOperatorKind::BitwiseAnd => Precedence(10),
      BinaryOperatorKind::BitwiseXor => Precedence(11),
      BinaryOperatorKind::BitwiseOr => Precedence(12),
      BinaryOperatorKind::And => Precedence(13),
      BinaryOperatorKind::Or => Precedence(14),
    }
  }
}

struct Parser<'a> {
  lex: Lexer<'a>,
  diag: SmallVec<[Box<dyn Diagnostic>; 4]>,
}

trait DiagnosticExt: Diagnostic + Sized + 'static {
  #[inline]
  fn into_diag(self) -> Box<dyn Diagnostic> {
    Box::new(self)
  }
}

impl<D: Diagnostic + Sized + 'static> DiagnosticExt for D {}

trait ResultDiagExt<T> {
  fn map_diag(self) -> Result<T, Box<dyn Diagnostic>>;
}

impl<T, D: DiagnosticExt> ResultDiagExt<T> for Result<T, D> {
  #[inline]
  fn map_diag(self) -> Result<T, Box<dyn Diagnostic>> {
    self.map_err(DiagnosticExt::into_diag)
  }
}

trait CheckHelper {
  fn is<T: Tok>(&self) -> bool;
}

impl<T: Tok, E> CheckHelper for Result<T, E> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Ok(t) => t.is::<T2>(),
      Err(_) => false,
    }
  }
}

impl<T: Tok, E> CheckHelper for Option<Result<T, E>> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Some(t) => t.is::<T2>(),
      None => false,
    }
  }
}

impl<E> CheckHelper for Result<Token, E> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Ok(t) => t.is::<T2>(),
      Err(_) => false,
    }
  }
}

impl<E> CheckHelper for Option<Result<Token, E>> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Some(t) => t.is::<T2>(),
      None => false,
    }
  }
}

trait CheckHelperRef {
  fn is<T: Tok>(&self) -> bool;
}

impl<T: Tok, E> CheckHelperRef for Result<&T, E> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Ok(t) => t.is::<T2>(),
      Err(_) => false,
    }
  }
}

impl<T: Tok, E> CheckHelperRef for Option<&Result<T, E>> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Some(t) => t.is::<T2>(),
      None => false,
    }
  }
}

impl<E> CheckHelperRef for Result<&Token, E> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Ok(t) => t.is::<T2>(),
      Err(_) => false,
    }
  }
}

impl<E> CheckHelperRef for Option<&Result<Token, E>> {
  #[inline]
  fn is<T2: Tok>(&self) -> bool {
    match self {
      Some(t) => t.is::<T2>(),
      None => false,
    }
  }
}

macro_rules! define_error {
  ($name:ident, $msg:expr) => {
    #[derive(Debug)]
    struct $name(Span);

    impl private::Sealed for $name {}
    impl Spanned for $name {
      #[inline]
      fn span(&self) -> Span {
        self.0
      }
    }

    impl Diagnostic for $name {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, $msg)
      }
    }
  };
}

define_error!(UnexpectedEof, "Unexpected end of file");
define_error!(
  BlockStringImportIllegal,
  "Block string literals not allowed in imports"
);
define_error!(ComputedImportsIllegal, "Computed imports are not allowed");
define_error!(ExpectedSemiOrColon, "Expected , or ;");
define_error!(InvalidUnaryOperator, "Not a unary operator");
define_error!(InvalidBinaryOperator, "Not a binary operator");
define_error!(InvalidSliceTooManyColons, "Invalid slice: too many colons");
define_error!(
  InvalidIndexRequiresExpression,
  "Index lookup requires an expression"
);
define_error!(ExpectedObjectField, "Expected object field");

#[derive(Debug)]
enum ExpectError<T: Tok + 'static> {
  Eof(UnexpectedEof),
  LexError(ErrorToken),
  WrongToken(Token, PhantomData<T>),
}

impl<T: Tok + 'static> private::Sealed for ExpectError<T> {}
impl<T: Tok + 'static> Spanned for ExpectError<T> {
  fn span(&self) -> Span {
    match self {
      ExpectError::Eof(e) => Spanned::span(e),
      ExpectError::LexError(e) => Spanned::span(e),
      ExpectError::WrongToken(e, _) => Spanned::span(e),
    }
  }
}

impl<T: Tok + 'static> Diagnostic for ExpectError<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ExpectError::Eof(e) => Diagnostic::fmt(e, f),
      ExpectError::LexError(e) => Diagnostic::fmt(e, f),
      ExpectError::WrongToken(t, _) => {
        write!(f, "Expected token '{}', got '{}'", T::NAME, t.name())
      }
    }
  }
}

impl<'a> Parser<'a> {
  fn create_error(&mut self, diag: Box<dyn Diagnostic>) -> Expr {
    let msg = diag.message();
    self.diag.push(diag);
    let msg_tok = String::new(msg, StringKind::DoubleQuoted, Span::EMPTY);
    let msg_expr = ExprString { token: msg_tok };
    let err_expr = ExprError {
      error_token: Error::new(Span::EMPTY),
      expr: msg_expr.into(),
    };

    err_expr.into()
  }

  #[inline]
  fn expect<T: Tok>(&mut self) -> Result<T, ExpectError<T>> {
    match self.next() {
      None => Err(ExpectError::Eof(UnexpectedEof(self.lex.span()))),
      Some(Err(e)) => Err(ExpectError::LexError(e)),
      Some(Ok(t)) => match T::try_from(t) {
        Err(t) => Err(ExpectError::WrongToken(t, PhantomData)),
        Ok(t) => Ok(t),
      },
    }
  }

  #[inline]
  fn next(&mut self) -> Option<Result<Token, ErrorToken>> {
    self.lex.next()
  }

  #[inline]
  fn peek(&mut self) -> Option<&Result<Token, ErrorToken>> {
    self.lex.peek()
  }

  fn peek_token(&mut self) -> Result<&Token, Box<dyn Diagnostic>> {
    // This method is weird to work around some limitations of the borrow checker.
    enum Action {
      LexError,
      ReturnToken,
    }

    let action = match self.peek() {
      None => {
        let diag = UnexpectedEof(self.lex.span());
        return Err(Box::new(diag));
      }
      Some(Err(_)) => Action::LexError,
      Some(Ok(_)) => Action::ReturnToken,
    };

    match action {
      Action::LexError => {
        let diag = self.lex.next().unwrap().unwrap_err();
        Err(Box::new(diag))
      }
      Action::ReturnToken => Ok(self.peek().as_ref().unwrap().as_ref().unwrap()),
    }
  }

  #[inline]
  fn double_peek(&mut self) -> Option<&Result<Token, ErrorToken>> {
    self.lex.peek_nth(1)
  }

  fn parse_parameter(&mut self) -> Param {
    let name: Ident = match self.expect() {
      Ok(i) => i,
      Err(e) => {
        let span = Spanned::span(&e);
        self.create_error(Box::new(e));
        Ident::new("_", span)
      }
    };

    let (assign_token, default_arg) = if self.peek().is::<Assign>() {
      let assign_token: Assign = self.expect().unwrap();
      let default_arg = self.parse_expr(Precedence::MAX);
      (Some(assign_token), Some(default_arg))
    } else {
      (None, None)
    };

    Param {
      name,
      assign_token,
      default_arg,
    }
  }

  fn parse_parameters(&mut self) -> Result<Punctuated<Param, Comma>, Box<dyn Diagnostic>> {
    let mut ret = Punctuated::new();

    loop {
      let next = self.peek_token()?;

      if let Token::Symbol(Symbol::RightParen(_)) = next {
        break;
      }

      if !ret.is_empty() {
        let comma: Comma = match self.expect() {
          Ok(c) => c,
          Err(e) => {
            self.create_error(Box::new(e));
            Comma::default()
          }
        };

        ret.push_punct(comma);
      }

      let param = self.parse_parameter();
      ret.push_value(param);
    }

    Ok(ret)
  }

  fn parse_argument(&mut self) -> Argument {
    if self.peek().is::<Ident>() && self.double_peek().is::<Assign>() {
      let name: Ident = self.expect().unwrap();
      let assign_token: Assign = self.expect().unwrap();
      let value = self.parse_expr(Precedence::MAX);
      ArgNamed {
        name,
        assign_token,
        value,
      }
      .into()
    } else {
      let value = self.parse_expr(Precedence::MAX);
      ArgPositional { value }.into()
    }
  }

  fn parse_arguments(&mut self) -> Result<Punctuated<Argument, Comma>, Box<dyn Diagnostic>> {
    let mut ret = Punctuated::new();

    loop {
      let next = self.peek_token()?;

      if let Token::Symbol(Symbol::RightParen(_)) = next {
        break;
      }

      if !ret.is_empty() {
        let comma: Comma = match self.expect() {
          Ok(c) => c,
          Err(e) => {
            self.create_error(Box::new(e));
            Comma::default()
          }
        };

        ret.push_punct(comma);
      }

      let param = self.parse_argument();
      ret.push_value(param);
    }

    Ok(ret)
  }

  fn parse_bind(&mut self) -> Result<Bind, Box<dyn Diagnostic>> {
    let name: Ident = self.expect().map_diag()?;

    let fun = if self.peek().is::<LeftParen>() {
      let left_paren_token: LeftParen = self.expect().unwrap();
      let params = self.parse_parameters()?;
      let right_paren_token: RightParen = self.expect().unwrap();
      Some((left_paren_token, params, right_paren_token))
    } else {
      None
    };

    let assign_token: Assign = self.expect().map_diag()?;
    let body = self.parse_expr(Precedence::MAX);

    if let Some((left_paren_token, params, right_paren_token)) = fun {
      Ok(
        BindFunction {
          name,
          left_paren_token,
          params,
          right_paren_token,
          assign_token,
          body,
        }
        .into(),
      )
    } else {
      Ok(
        BindValue {
          name,
          assign_token,
          body,
        }
        .into(),
      )
    }
  }

  fn parse_object_remainder_assert(&mut self) -> ObjectFieldAssert {
    let assert_token: Assert = self.expect().unwrap();
    let cond = self.parse_expr(Precedence::MAX);
    let (col_token, msg) = if self.peek().is::<Colon>() {
      let col_token: Colon = self.expect().unwrap();
      let msg = self.parse_expr(Precedence::MAX);
      (Some(col_token), Some(msg))
    } else {
      (None, None)
    };

    ObjectFieldAssert {
      assert_token,
      cond,
      col_token,
      msg,
    }
  }

  fn parse_object_remainder_local(&mut self) -> ObjectFieldLocal {
    let local_token: Local = self.expect().unwrap();
    let name = match self.expect::<Ident>() {
      Ok(name) => name,
      Err(e) => {
        self.diag.push(e.into_diag());
        Ident::new("_", Span::EMPTY)
      }
    };

    // TODO: Can we reuse regular local bind parsing here?
  }

  fn parse_object_remainder(&mut self) -> Punctuated<ObjectField, Comma> {
    let fields = Punctuated::new();

    loop {
      match self.peek_token() {
        Ok(Token::Symbol(Symbol::RightBrace(_))) => return fields,
        Ok(Token::Keyword(Keyword::For(_))) => {
          // It's a comprehension
          return self.parse_object_remainder_comprehension(fields);
        }
        _ => (),
      }

      if !fields.is_empty() {
        let comma: Comma = match self.expect() {
          Ok(c) => c,
          Err(e) => {
            self.create_error(Box::new(e));
            Comma::default()
          }
        };
      }

      let field: ObjectField = match self.peek_token() {
        Ok(Token::Symbol(Symbol::LeftBracket(_))) | Ok(Token::Ident(_)) | Ok(Token::String(_)) => {
          self.parse_object_remainder_field().into()
        }

        Ok(Token::Keyword(Keyword::Local(_))) => self.parse_object_remainder_local().into(),
        Ok(Token::Keyword(Keyword::Assert(_))) => self.parse_object_remainder_assert().into(),

        t => {
          // TODO: this is bad, and I should feel bad
          // proper error please...
          let err = match t.map(|t| ExpectedObjectField(t.span()).into_diag()) {
            Ok(e) => e,
            Err(e) => e,
          };
          self.diag.push(err);
          continue;
        }
      };

      fields.push_value(field);
    }
  }

  fn parse_expr_impl(&mut self, precedence: Precedence) -> Result<Expr, Box<dyn Diagnostic>> {
    let next = self.peek_token()?;

    match next {
      Token::Keyword(Keyword::Assert(_)) => {
        let assert_token: Assert = self.expect().unwrap();
        let cond = self.parse_expr(Precedence::MAX);

        let (col_token, msg) = if self.peek().is::<Colon>() {
          let col_token: Colon = self.expect().unwrap();
          let msg = self.parse_expr(Precedence::MAX);
          (Some(col_token), Some(msg))
        } else {
          (None, None)
        };

        let semi_colon_token: SemiColon = match self.expect().map_diag() {
          Ok(t) => t,
          Err(e) => {
            self.create_error(e);
            SemiColon::default()
          }
        };

        let rest = self.parse_expr(Precedence::MAX);
        Ok(
          ExprAssert {
            assert_token,
            cond,
            col_token,
            msg,
            semi_colon_token,
            rest,
          }
          .into(),
        )
      }

      Token::Keyword(Keyword::Error(_)) => {
        let error_token: Error = self.expect().unwrap();
        let expr = self.parse_expr(Precedence::MAX);

        Ok(ExprError { error_token, expr }.into())
      }

      Token::Keyword(Keyword::If(_)) => {
        let if_token: If = self.expect().unwrap();
        let cond = self.parse_expr(Precedence::MAX);
        let then_token: Then = self.expect().map_diag()?;
        let if_true = self.parse_expr(Precedence::MAX);
        let (else_token, if_false) = if self.peek().is::<Else>() {
          let else_token: Else = self.expect().unwrap();
          let if_false = self.parse_expr(Precedence::MAX);
          (Some(else_token), Some(if_false))
        } else {
          (None, None)
        };

        Ok(
          ExprIf {
            if_token,
            cond,
            then_token,
            if_true,
            else_token,
            if_false,
          }
          .into(),
        )
      }

      Token::Keyword(Keyword::Function(_)) => {
        let function_token: Function = self.expect().unwrap();
        let left_paren_token: LeftParen = self.expect().map_diag()?;
        let params = self.parse_parameters()?;
        let right_paren_token: RightParen = self.expect().map_diag()?;
        let body = self.parse_expr(Precedence::MAX);

        Ok(
          ExprFunction {
            function_token,
            left_paren_token,
            params,
            right_paren_token,
            body,
          }
          .into(),
        )
      }

      Token::Keyword(Keyword::Import(_)) => {
        let import_token: Import = self.expect().unwrap();
        let body = self.parse_expr(Precedence::MAX);
        match body {
          Expr::String(s) => {
            if s.kind() == StringKind::Block {
              Err(BlockStringImportIllegal(s.span()).into_diag())
            } else {
              Ok(
                ExprImport {
                  import_token,
                  file: *s,
                }
                .into(),
              )
            }
          }
          e => Err(ComputedImportsIllegal(e.span()).into_diag()),
        }
      }

      Token::Keyword(Keyword::ImportStr(_)) => {
        let import_str_token: ImportStr = self.expect().unwrap();
        let body = self.parse_expr(Precedence::MAX);
        match body {
          Expr::String(s) => {
            if s.kind() == StringKind::Block {
              Err(BlockStringImportIllegal(s.span()).into_diag())
            } else {
              Ok(
                ExprImportStr {
                  import_str_token,
                  file: *s,
                }
                .into(),
              )
            }
          }
          e => Err(ComputedImportsIllegal(e.span()).into_diag()),
        }
      }

      Token::Keyword(Keyword::Local(_)) => {
        let local_token: Local = self.expect().unwrap();
        let mut binds = Punctuated::new();
        loop {
          let bind = self.parse_bind();
          match bind {
            Ok(bind) => {
              if !binds.empty_or_trailing() {
                // This is to deal with error situations
                binds.push_punct(Comma::default());
              }

              binds.push_value(bind)
            }
            Err(e) => self.diag.push(e),
          }

          let next = self.peek();
          if next.is::<Comma>() {
            let comma: Comma = self.expect().unwrap();
            binds.push_punct(comma);
          } else if next.is::<SemiColon>() {
            break;
          } else {
            let span = next.map(SpanHelper::get_span).unwrap_or_default();
            self.diag.push(ExpectedSemiOrColon(span).into_diag());
          }
        }

        let semi_colon_token: SemiColon = self.expect().unwrap();
        let body = self.parse_expr(Precedence::MAX);
        Ok(
          ExprLocal {
            local_token,
            binds,
            semi_colon_token,
            body,
          }
          .into(),
        )
      }

      _ => {
        // Unary operator
        if let Token::Operator(op) = next {
          if let None = UnaryOperatorKind::for_token(op) {
            let span = self.expect::<Operator>().unwrap().span();
            return Err(InvalidUnaryOperator(span).into_diag());
          }

          if precedence == Precedence::UNARY {
            let op: Operator = self.expect().unwrap();
            let operator = UnaryOperator::from_token(op).unwrap();
            let expr = self.parse_expr(precedence);
            return Ok(ExprUnary { operator, expr }.into());
          }
        }

        // Base case
        if precedence == Precedence::MIN {
          return self.parse_terminal();
        }

        let mut lhs = self.parse_expr(precedence - 1);

        loop {
          // Then next token must be a binary operator.
          let next = match self.peek() {
            None => Ok(None),
            Some(Ok(e)) => Ok(Some(e)),
            Some(Err(e)) => Err(e),
          }?;
          match next {
            Some(Token::Keyword(Keyword::In(_))) => {
              if Precedence::for_bin_op(BinaryOperatorKind::In) != precedence {
                return Some(lhs);
              }
            }

            Some(Token::Operator(op)) => {
              if op.is::<Colon>() {
                // Special case for the colons in assert. It should terminate parsing of the
                // expression here, returning control to the parsing of the actual assert AST.
                return Some(lhs);
              }

              if op.is::<DoubleColon>() {
                // Special case for [e::]
                return Some(lhs);
              }

              let op_kind = match BinaryOperatorKind::for_token(op) {
                None => {
                  self.diag.push(InvalidBinaryOperator(op.span()).into_diag());
                  return Some(lhs);
                }
                Some(kind) => kind,
              };

              if Precedence::for_bin_op(op_kind) != precedence {
                return Some(lhs);
              }
            }

            Some(Token::Symbol(Symbol::Dot(_)))
            | Some(Token::Symbol(Symbol::LeftBracket(_)))
            | Some(Token::Symbol(Symbol::LeftParen(_)))
            | Some(Token::Symbol(Symbol::LeftBrace(_))) => {
              if Precedence::APPLY != precedence {
                return Some(lhs);
              }
            }

            _ => return Some(lhs),
          };

          match self.next().unwrap().unwrap() {
            Token::Symbol(Symbol::LeftBracket(left_bracket_token)) => {
              // handle slice
              let mut colons_consumed = 0usize;
              let mut ready_for_next_index = true;
              let mut colons: [Option<IndexOperator>; 2] = [None; 2];
              let mut indexes: [Option<Expr>; 3] = [None; 3];
              while colons_consumed < 3 {
                if self.peek().is::<RightBracket>() {
                  break;
                } else if self.peek().is::<Colon>() {
                  let token: Colon = self.expect().unwrap();
                  colons_consumed += 1;
                  ready_for_next_index = true;
                  colons[colons_consumed] = Some(token.into());
                } else if self.peek().is::<DoubleColon>() {
                  let token: DoubleColon = self.expect().unwrap();
                  colons_consumed += 2;
                  ready_for_next_index = true;
                  colons[colons_consumed] = Some(token.into());
                } else if ready_for_next_index {
                  indexes[colons_consumed] = Some(self.parse_expr(Precedence::MAX));
                  ready_for_next_index = false;
                } else {
                  let error = self.expect::<RightBracket>().unwrap_err();
                  return Err(error.into_diag());
                }
              }

              let right_bracket_token: RightBracket = self.expect().unwrap();
              if colons_consumed > 2 {
                // example: target[42:42:42:42]
                return Err(
                  InvalidSliceTooManyColons(left_bracket_token.span() + right_bracket_token.span())
                    .into_diag(),
                );
              }

              if colons_consumed == 0 && ready_for_next_index {
                // example: target[]
                return Err(
                  InvalidIndexRequiresExpression(
                    left_bracket_token.span() + right_bracket_token.span(),
                  )
                  .into_diag(),
                );
              }

              let is_slice = colons_consumed > 0;
              if is_slice {
                lhs = ExprSlice {
                  target: lhs,
                  left_bracket_token,
                  begin_index: indexes[0],
                  end_colon_token: colons[0],
                  end_index: indexes[1],
                  step_colon_token: colons[1],
                  step: indexes[2],
                  right_bracket_token,
                }
                .into();
              } else {
                lhs = ExprIndex {
                  target: lhs,
                  left_bracket_token,
                  index: indexes[0].unwrap(),
                  right_bracket_token,
                }
                .into();
              }
            }

            Token::Symbol(Symbol::Dot(dot_token)) => {
              let field_name: Ident = self.expect()?;
              lhs = ExprFieldAccess {
                target: lhs,
                field_name,
              }
              .into();
            }

            Token::Symbol(Symbol::LeftParen(left_paren_token)) => {
              let args = self.parse_arguments()?;
              let right_paren_token: RightParen = self.expect()?;
              let tail_strict_token = if self.peek().is::<TailStrict>() {
                let tail_strict_token: TailStrict = self.expect().unwrap();
                Some(tail_strict_token)
              } else {
                None
              };

              lhs = ExprApply {
                target: lhs,
                left_paren_token,
                args,
                right_paren_token,
                tail_strict_token,
              }
              .into();
            }

            Token::Symbol(Symbol::LeftBrace(left_brace_token)) => {
              let fields = self.parse_object_remainder();
              let right_brace_token: RightBrace = self.expect()?;
              lhs = ExprObjectApply {
                target: lhs,
                left_brace_token,
                fields,
                right_brace_token,
              }
              .into();
            }

            op => {
              if op.is::<In>() && self.peek().is::<Super>() {
                let super_token: Super = self.expect().unwrap();
                lhs = ExprInSuper {
                  target: lhs,
                  in_token: op.try_into().unwrap(),
                  super_token,
                }
                .into()
              } else {
                let rhs = self.parse_expr(precedence - 1);
                let bin_op = BinaryOperator::from_raw_token(op).unwrap();
                lhs = ExprBinary {
                  left: lhs,
                  op: bin_op,
                  right: rhs,
                }
                .into();
              }
            }
          }
        }
      }
    }
  }

  fn parse_expr(&mut self, precedence: Precedence) -> Expr {
    match self.parse_expr_impl(precedence) {
      Ok(e) => e,
      Err(diag) => self.create_error(diag),
    }
  }

  //   // parseArgument parses either id = expr or just expr.
  //   // It returns either (id, expr) or (None, expr)
  //   // respectively.
  //   fn parse_argument(&mut self) -> Result<(Option<Identifier<'a>>, Expr<'a>), ErrData> {
  //     let id =
  //       if self.peek().kind() == TokenKind::Id && self.double_peek().kind() == TokenKind::OpAssign {
  //         let ident = self.pop_expect(TokenKind::Id).id().unwrap();
  //         self.pop_expect(TokenKind::OpAssign).unwrap();
  //         Some(Identifier::from(ident))
  //       } else {
  //         None
  //       };

  //     self.parse(Precedence::MAX).map(|v| (id, v))
  //   }
}
