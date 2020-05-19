use super::*;

pub(crate) const LITERAL_FIRST: TokenSet = token_set![
  T![true],
  T![false],
  NUMBER,
  STRING,
  VERBATIM_STRING,
  BLOCK_STRING,
  T![null],
];

pub(super) fn opt_literal_expr<S: TokenSource>(p: &mut Parser<S>) -> Option<CompletedMarker> {
  if !p.at_ts(LITERAL_FIRST) {
    return None;
  }

  let kind = p.current();
  let m = p.start();
  p.bump_any();
  Some(m.complete(
    p,
    match kind {
      // test true_expr
      // true
      T![true] => TRUE_EXPR,

      // test false_expr
      // false
      T![false] => FALSE_EXPR,

      // test number_expr
      // 42
      NUMBER => NUMBER_EXPR,

      // test string_expr
      // "test"
      STRING => STRING_EXPR,

      // test verbatim_string_expr
      // @"test"
      VERBATIM_STRING => STRING_EXPR,

      // test block_string_expr
      // |||
      //   test
      // |||
      BLOCK_STRING => STRING_EXPR,

      // test null_expr
      // null
      T![null] => NULL_EXPR,
      _ => unreachable!(),
    },
  ))
}

pub(crate) const EXPR_RECOVERY_SET: TokenSet = token_set![T![;], T![,], T![:]];
// pub(crate) const EXPR_FIRST: TokenSet = LITERAL_FIRST.union(token_set![
//   T!['('],
//   T![self],
//   T![$],
//   IDENT,
//   T!['{'],
//   T!['['],
//   T![super],
//   T![-],
//   T![+],
//   T![!],
//   T![~],
// ]);

pub(super) fn atom_expr<S: TokenSource>(p: &mut Parser<S>) -> Option<CompletedMarker> {
  if let Some(m) = opt_literal_expr(p) {
    return Some(m);
  }

  match p.current() {
    T!['('] => Some(group_expr(p)),
    T![self] => Some(self_expr(p)),
    T![$] => Some(root_expr(p)),
    IDENT => Some(ident_expr(p)),
    T!['{'] => Some(obj_or_comp(p)),
    T!['['] => Some(arr_or_comp(p)),
    T![super] => Some(super_expr(p)),
    _ => {
      p.err_recover("expected expression", EXPR_RECOVERY_SET);
      None
    }
  }
}

// test self_expr
// self
pub(super) fn self_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![self]));
  let m = p.start();
  p.expect(T![self]);
  m.complete(p, SELF_EXPR)
}

// test root_expr
// $
pub(super) fn root_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![$]));
  let m = p.start();
  p.expect(T![$]);
  m.complete(p, ROOT_EXPR)
}

// test ident_expr
// foo
pub(super) fn ident_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(IDENT));
  let m = p.start();
  p.expect(IDENT);
  m.complete(p, IDENT_EXPR)
}

pub(super) fn super_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![super]));
  let m = p.start();
  p.expect(T![super]);

  // test super_ident
  // super.foo
  let kind = if p.at(T![.]) {
    p.expect(T![.]);
    p.expect(IDENT);
    SUPER_FIELD_EXPR
  }
  // test super_computed
  // super['foo']
  else if p.at(T!['[']) {
    comp_field_name(p);
    SUPER_COMPUTED_EXPR
  }
  // test_err super_missing_field
  // super
  else {
    p.error(format!("expected '.' or '['"));
    SUPER_COMPUTED_EXPR // is this correct in an error setting?
  };

  m.complete(p, kind)
}

// test group_expr
// (5)
pub(super) fn group_expr<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['(']));
  let m = p.start();
  p.expect(T!['(']);

  expr(p);
  if !p.at(T![')']) {
    p.err_recover("expected ')'", token_set![T![')']]);
  }
  p.expect(T![')']);
  m.complete(p, GROUP_EXPR)
}
