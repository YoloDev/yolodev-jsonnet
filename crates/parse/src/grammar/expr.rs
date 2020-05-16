use super::*;

#[derive(Copy, Clone, PartialEq, PartialOrd)]
enum Precedence {
  Any,
  // Application,
  // Unary,
  Term,
  Arithmetic,
  Shift,
  Compare,
  Equals,
  BitAnd,
  BitXor,
  BitOr,
  And,
  Or,
}

impl Precedence {
  fn of(kind: SyntaxKind) -> Option<Self> {
    match kind {
      T![*] | T![/] | T![%] => Some(Precedence::Term),
      T![+] | T![-] => Some(Precedence::Arithmetic),
      T![<<] | T![>>] => Some(Precedence::Shift),
      T![>] | T![>=] | T![<] | T![<=] | T![in] => Some(Precedence::Compare),
      T![==] | T![!=] => Some(Precedence::Equals),
      T![&] => Some(Precedence::BitAnd),
      T![^] => Some(Precedence::BitXor),
      T![|] => Some(Precedence::BitOr),
      T![&&] => Some(Precedence::And),
      T![||] => Some(Precedence::Or),
      _ => None,
    }
  }
}

pub(super) fn expr<S: TokenSource>(p: &mut Parser<S>) -> bool {
  unary_expr(p)
    .map(|lhs| expr_bp(p, lhs, Precedence::Any))
    .is_some()
}

fn unary_expr<S: TokenSource>(p: &mut Parser<S>) -> Option<CompletedMarker> {
  if p.at(T![assert]) {
    Some(assert_expr(p))
  } else if p.at(T![error]) {
    Some(error_expr(p))
  } else if p.at(T![function]) {
    Some(function_expr(p))
  } else if p.at(T![if]) {
    Some(if_expr(p))
  } else if p.at(T![import]) {
    Some(import_expr(p))
  } else if p.at(T![importstr]) {
    Some(importstr_expr(p))
  } else if p.at(T![local]) {
    Some(local_expr(p))
  } else if p.at_ts(UNARY_OP) {
    Some(unary_op_expr(p))
  } else {
    trailer_expr(p)
  }
}

const UNARY_OP: TokenSet = token_set![T![-], T![+], T![!], T![~]];
const BINARY_OP: TokenSet = token_set![
  T![*],
  T![/],
  T![%],
  T![+],
  T![-],
  T![<<],
  T![>>],
  T![>],
  T![>=],
  T![<],
  T![<=],
  T![in],
  T![==],
  T![!=],
  T![&],
  T![^],
  T![|],
  T![&&],
  T![||],
];

// test unary_expr
// - 10

// test unary_expr_multiple
// ! - 10
fn unary_op_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at_ts(UNARY_OP));
  let m = p.start();
  p.bump_any();
  unary_expr(p);
  m.complete(p, UNARY_EXPR)
}

// test assert_simple
// assert true ; null
fn assert_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![assert]));
  let m = p.start();
  p.bump(T![assert]);
  expr(p);

  // test assert_with_message
  // assert true : "message" ; null
  if p.eat(T![:]) {
    expr(p);
  }

  p.expect(T![;]);
  expr(p);
  m.complete(p, ASSERT_EXPR)
}

// test error_expr
// error "test"
fn error_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![error]));
  let m = p.start();
  p.bump(T![error]);
  expr(p);
  m.complete(p, ERROR_EXPR)
}

// test if_then_expr
// if true then null
fn if_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![if]));
  let m = p.start();
  p.bump(T![if]);
  expr(p);

  p.expect(T![then]);
  expr(p);

  // test if_then_else_expr
  // if true then true else false
  if p.eat(T![else]) {
    expr(p);
  }

  m.complete(p, IF_EXPR)
}

// test import_expr
// import "test"
fn import_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![import]));
  let m = p.start();
  p.bump(T![import]);
  p.expect(STRING);
  m.complete(p, IMPORT_EXPR)
}

// test importstr_expr
// importstr "test"
fn importstr_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![importstr]));
  let m = p.start();
  p.bump(T![importstr]);
  p.expect(STRING);
  m.complete(p, IMPORTSTR_EXPR)
}

// test local_expr_single
// local foo = true ; foo

// test local_expr_fun_single
// local foo(a, b = 2) = a + b ; foo
fn local_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![local]));
  let m = p.start();
  p.bump(T![local]);

  let mut bind_count = 0u32;

  // test local_expr_multiple
  // local foo = true, bar = foo ; bar

  // test local_expr_fun_multiple
  // local foo(a, b = 2) = a + b,
  //       bar(a = 1, b = 2) = foo(a, b) + foo(a, b);
  // bar
  while !p.at(EOF) && !p.at(T![;]) {
    if bind_count > 0 {
      p.expect(T![,]);
    }

    if !p.at(IDENT) {
      break;
    }

    bind_count += 1;
    bind(p);
  }

  p.expect(T![;]);

  m.complete(p, LOCAL_EXPR)
}

// test function_expr
// function(a, b = 0) a + b
fn function_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![function]));
  let m = p.start();
  p.bump(T![function]);

  params(p);
  expr(p);

  m.complete(p, FUNCTION_EXPR)
}

fn trailer_expr<S: TokenSource>(p: &mut Parser<S>) -> Option<CompletedMarker> {
  if p.at(T!['(']) {
    return Some(group_expr(p));
  }

  atom_expr(p).map(|atom| trailer_helper(p, atom))
}

fn trailer_helper<S: TokenSource>(p: &mut Parser<S>, mut e: CompletedMarker) -> CompletedMarker {
  while !p.at(EOF) {
    if p.at(T!['(']) {
      // test apply_expr
      // foo(a, b = 0)
      e = complete_apply_expr(p, e);
    } else if p.at(T![.]) {
      // test ident_member_expr
      // foo.bar
      e = complete_member_dot_expr(p, e);
    } else if p.at(T!['[']) {
      // test computed_member_expr
      // foo['bar']
      e = complete_member_computed_expr(p, e);
    } else if p.at(T![in]) && p.nth_at(1, T![super]) {
      // test in_super_expr
      // 'foo' in super
      e = complete_in_super_expr(p, e);
    } else {
      break;
    }
  }

  e
}

fn complete_in_super_expr<S: TokenSource>(
  p: &mut Parser<S>,
  e: CompletedMarker,
) -> CompletedMarker {
  assert!(p.at(T![in]));
  assert!(p.nth_at(1, T![super]));
  let m = e.precede(p);
  p.bump(T![in]);
  p.bump(T![super]);
  m.complete(p, IN_SUPER_EXPR)
}

fn complete_member_dot_expr<S: TokenSource>(
  p: &mut Parser<S>,
  e: CompletedMarker,
) -> CompletedMarker {
  assert!(p.at(T![.]));
  let m = e.precede(p);
  p.bump(T![.]);
  p.expect(IDENT);
  m.complete(p, IDENT_FIELD_ACCESS_EXPR)
}

fn complete_member_computed_expr<S: TokenSource>(
  p: &mut Parser<S>,
  e: CompletedMarker,
) -> CompletedMarker {
  assert!(p.at(T!['[']));
  let m = e.precede(p);
  p.bump(T!['[']);
  expr(p);
  p.expect(T![']']);
  m.complete(p, COMPUTED_FIELD_ACCESS_EXPR)
}

fn complete_apply_expr<S: TokenSource>(p: &mut Parser<S>, e: CompletedMarker) -> CompletedMarker {
  assert!(p.at(T!['(']));
  let m = e.precede(p);
  args(p);
  m.complete(p, APPLY_EXPR)
}

fn args<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['(']));
  let m = p.start();
  p.bump(T!['(']);

  while !p.at(EOF) && !p.at(T![')']) {
    let m = p.start();

    let kind = if p.at(IDENT) && p.nth_at(1, T![=]) {
      // test function_named_arg
      // foo(bar = 0)
      p.bump(IDENT);
      p.bump(T![=]);
      expr(p);
      NAMED_ARGUMENT
    } else {
      // test function_positional_arg
      // foo(0)
      expr(p);
      POSITIONAL_ARGUMENT
    };

    m.complete(p, kind);
    if !p.at(T![')']) && !p.expect(T![,]) {
      break;
    }
  }

  p.expect(T![')']);

  m.complete(p, ARG_LIST)
}

fn expr_bp<S: TokenSource>(
  p: &mut Parser<S>,
  mut lhs: CompletedMarker,
  base: Precedence,
) -> CompletedMarker {
  while p.at_ts(BINARY_OP) && Precedence::of(p.current()).map_or(false, |op| op >= base) {
    let m = lhs.precede(p);
    let precedence = Precedence::of(p.current()).unwrap();
    p.bump_any();
    let mut rhs = match unary_expr(p) {
      None => {
        lhs = m.complete(p, BINARY_EXPR);
        break;
      }
      Some(e) => e,
    };

    while p.at_ts(BINARY_OP) {
      let next = Precedence::of(p.current()).unwrap_or(Precedence::Any);
      if next > precedence {
        rhs = expr_bp(p, rhs, next);
      } else {
        break;
      }
    }

    lhs = m.complete(p, BINARY_EXPR);
  }

  lhs
}
