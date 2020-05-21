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

pub(super) fn expr<S: TokenSource>(p: &mut Parser<S>) -> Option<CompletedMarker> {
  unary_expr(p).map(|lhs| expr_bp(p, lhs, Precedence::Any))
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

  {
    let m = p.start();
    expr(p);
    m.complete(p, COND);
  }

  // test assert_with_message
  // assert true : "message" ; null
  if p.eat(T![:]) {
    let m = p.start();
    expr(p);
    m.complete(p, ASSERT_MESSAGE);
  }

  p.expect(T![;]);
  {
    let m = p.start();
    expr(p);
    m.complete(p, REST);
  }

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

  {
    let m = p.start();
    expr(p);
    m.complete(p, COND);
  }

  p.expect(T![then]);

  {
    let m = p.start();
    expr(p);
    m.complete(p, TRUE_BRANCH);
  }

  // test if_then_else_expr
  // if true then true else false
  if p.eat(T![else]) {
    let m = p.start();
    expr(p);
    m.complete(p, FALSE_BRANCH);
  }

  m.complete(p, IF_EXPR)
}

// test import_expr
// import "test"
fn import_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![import]));
  let m = p.start();
  p.bump(T![import]);
  if !p.eat(STRING) && !p.eat(VERBATIM_STRING) {
    if p.eat(BLOCK_STRING) {
      p.error("import does not support block strings");
    } else {
      p.err_and_bump("expected string");
    }
  }
  m.complete(p, IMPORT_EXPR)
}

// test importstr_expr
// importstr "test"
fn importstr_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![importstr]));
  let m = p.start();
  p.bump(T![importstr]);
  if !p.eat(STRING) && !p.eat(VERBATIM_STRING) {
    if p.eat(BLOCK_STRING) {
      p.error("import does not support block strings");
    } else {
      p.err_and_bump("expected string");
    }
  }
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
  {
    let m = p.start();
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

    m.complete(p, BIND_LIST);
  }

  p.expect(T![;]);

  {
    let m = p.start();
    expr(p);
    m.complete(p, REST);
  }

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
      e = complete_member_computed_or_slice_expr(p, e);
    } else if p.at(T!['{']) {
      // test object_apply_expr
      // CCompiler { compiler: "gcc" }

      // test object_apply_comp_expr
      // CCompiler { [x]: true for x in ['1'] }
      e = complete_obj_or_comp_apply_expr(p, e);
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

fn complete_member_computed_or_slice_expr<S: TokenSource>(
  p: &mut Parser<S>,
  e: CompletedMarker,
) -> CompletedMarker {
  assert!(p.at(T!['[']));
  let m = e.precede(p);
  p.bump(T!['[']);

  let mut count = 0u8;
  let mut ready_for_expr = true;
  let mut first = None;

  // test index_expr
  // foo[bar]

  // test index_expr_num
  // foo[0]

  // test slice_expr_all
  // foo[::]

  // test slice_expr_from
  // foo[0:]

  // test slice_expr_to
  // foo[:10]

  // test slice_expr_step
  // foo[::2]

  // test slice_expr_from_to
  // foo[0:10]

  // test slice_expr_from_step
  // foo[0::2]

  // test_slice_expr_to_step
  // foo[:10:2]

  // test slice_expr_from_to_step
  // foo[0:10:2]

  // TODO: Produce SLICE_START, SLICE_END and SLICE_STEP nodes
  while !p.at(EOF) && !p.at(T![']']) {
    if p.eat(T![:]) {
      if count > 1 {
        p.error("too many colons in slice");
        continue;
      }

      count += 1;
      ready_for_expr = true;
    } else if p.eat(T![::]) {
      if count > 0 {
        p.error("too many colons in slice");
        count += 1; // treat as single colon
        continue;
      }

      count += 2;
      ready_for_expr = true;
    } else if ready_for_expr {
      match expr(p) {
        None => break,
        Some(e) => {
          let m = e.precede(p);
          let e = m.complete(
            p,
            match count {
              0 => SLICE_FROM,
              1 => SLICE_TO,
              2 => SLICE_STEP,
              _ => unreachable!(),
            },
          );

          if count == 0 {
            if first.is_none() {
              first = Some(e);
            }
          }
        }
      }
    } else {
      p.error(match count {
        1 => "expected ':' or ']'",
        _ => "expected ']'",
      });
      break;
    }
  }

  if count == 0 {
    match first.take() {
      None => (),
      Some(e) => {
        e.undo_completion(p).abandon(p);
      }
    }
  }

  p.expect(T![']']);

  m.complete(
    p,
    if count == 0 {
      COMPUTED_FIELD_ACCESS_EXPR
    } else {
      SLICE_EXPR
    },
  )
}

fn complete_apply_expr<S: TokenSource>(p: &mut Parser<S>, e: CompletedMarker) -> CompletedMarker {
  assert!(p.at(T!['(']));
  let m = e.precede(p);
  args(p);
  p.eat(T![tailstrict]);
  m.complete(p, APPLY_EXPR)
}

fn complete_obj_or_comp_apply_expr<S: TokenSource>(
  p: &mut Parser<S>,
  e: CompletedMarker,
) -> CompletedMarker {
  assert!(p.at(T!['{']));
  let m = e.precede(p);
  obj_or_comp(p);
  m.complete(p, OBJECT_APPLY_EXPR)
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
