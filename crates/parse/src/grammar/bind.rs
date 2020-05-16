use super::*;

pub(super) fn bind<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  let m = p.start();
  p.expect(IDENT);
  let is_function = if p.at(T!['(']) {
    params(p);
    true
  } else {
    false
  };

  p.expect(T![=]);
  expr(p);
  m.complete(
    p,
    if is_function {
      FUNCTION_BIND
    } else {
      VALUE_BIND
    },
  )
}

pub(super) fn params<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['(']));
  let m = p.start();
  p.bump(T!['(']);

  while !p.at(EOF) && !p.at(T![')']) {
    let m = p.start();
    if !p.expect(IDENT) {
      m.abandon(p);
      break;
    }

    if p.eat(T![=]) {
      expr(p);
    }

    m.complete(p, PARAM);
    if !p.at(T![')']) && !p.expect(T![,]) {
      break;
    }
  }

  p.expect(T![')']);

  m.complete(p, PARAM_LIST)
}
