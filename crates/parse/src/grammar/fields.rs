use super::*;

pub(super) fn comp_field_name<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['[']));
  let m = p.start();
  p.expect(T!['[']);

  expr(p);
  if !p.at(T![']']) {
    p.err_recover("expected ']'", token_set![T![']']]);
  }
  p.expect(T![']']);
  m.complete(p, COMPUTED_FIELD_NAME)
}

pub(super) fn string_field_name<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(STRING));
  let m = p.start();
  p.expect(STRING);
  m.complete(p, STRING_FIELD_NAME)
}

pub(super) fn ident_field_name<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(IDENT));
  let m = p.start();
  p.expect(IDENT);
  m.complete(p, IDENT_FIELD_NAME)
}

pub(super) fn field_name<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  match p.current() {
    IDENT => ident_field_name(p),
    STRING => string_field_name(p),
    T!['['] => comp_field_name(p),
    _ => {
      let m = p.start();
      // TODO: Figure out if this is correct
      p.error("expected field name");
      m.complete(p, PARSE_ERR)
    }
  }
}
