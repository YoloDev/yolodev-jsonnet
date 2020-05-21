use super::*;

pub(super) fn arr_or_comp<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['[']));
  let m = p.start();

  let mut is_arr_comp = false;

  p.bump(T!['[']);
  while !p.at(EOF) && !p.at(T![']']) {
    if !expr(p).is_some() {
      break;
    }

    // test arr_comp_without_comma
    // [x for x in [1]]
    if p.at(T![for]) {
      comp_specs(p);
      is_arr_comp = true;
      break;
    }

    if !p.at(T![']']) && !p.expect(T![,]) {
      break;
    }

    // test arr_comp_with_comma
    // [x, for x in [1]]
    if p.at(T![for]) {
      comp_specs(p);
      is_arr_comp = true;
      break;
    }
  }

  p.expect(T![']']);

  m.complete(
    p,
    if is_arr_comp {
      ARRAY_COMP_EXPR
    } else {
      ARRAY_EXPR
    },
  )
}

pub(super) fn comp_specs<S: TokenSource>(p: &mut Parser<S>) {
  const COMP_START: TokenSet = token_set![T![for], T![if]];
  for_spec(p);

  while p.at_ts(COMP_START) {
    if p.at(T![for]) {
      for_spec(p);
    } else {
      if_spec(p);
    }
  }
}

fn for_spec<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![for]));
  let m = p.start();
  p.bump(T![for]);
  p.expect(IDENT);
  p.expect(T![in]);
  expr(p);
  m.complete(p, FOR_COMP_SPEC)
}

fn if_spec<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![if]));
  let m = p.start();
  p.bump(T![if]);
  expr(p);
  m.complete(p, IF_COMP_SPEC)
}
