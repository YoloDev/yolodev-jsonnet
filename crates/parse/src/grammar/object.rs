use super::*;

// we parse object and object comprehensions the same way,
// and report errors on stuff like asserts inside object
// comprehentions at a later stage than parsing.
pub(super) fn obj_or_comp<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T!['{']));
  let m = p.start();

  let mut is_obj_comp = false;

  p.bump(T!['{']);
  while !p.at(EOF) && !p.at(T!['}']) {
    if !obj_field(p) {
      break;
    }

    // test obj_comp_without_comma
    // {[x]: true for x in ['x']}
    if p.at(T![for]) {
      comp_specs(p);
      is_obj_comp = true;
      break;
    }

    if !p.at(T!['}']) && !p.expect(T![,]) {
      break;
    }

    // test obj_comp_with_comma
    // {[x]: true, for x in ['x']}
    if p.at(T![for]) {
      comp_specs(p);
      is_obj_comp = true;
      break;
    }
  }

  p.expect(T!['}']);

  m.complete(
    p,
    if is_obj_comp {
      OBJECT_COMP_EXPR
    } else {
      OBJECT_EXPR
    },
  )
}

const FIELD_START: TokenSet = token_set![IDENT, STRING, T!['['], T![local], T![assert],];
fn obj_field<S: TokenSource>(p: &mut Parser<S>) -> bool {
  if !p.at_ts(FIELD_START) {
    p.error("expected object field");
    return false;
  }

  match p.current() {
    T![local] => obj_local(p),
    T![assert] => obj_assert(p),
    IDENT | STRING | T!['['] => obj_value_field(p),
    _ => unreachable!(),
  };

  return true;
}

fn obj_local<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![local]));
  let m = p.start();
  p.bump(T![local]);
  bind(p);
  m.complete(p, LOCAL_OBJ_FIELD)
}

fn obj_assert<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at(T![assert]));
  let m = p.start();
  p.bump(T![assert]);
  expr(p);

  if p.at(T![:]) {
    expr(p);
  }

  m.complete(p, ASSERT_OBJ_FIELD)
}

fn obj_value_field<S: TokenSource>(p: &mut Parser<S>) -> CompletedMarker {
  assert!(p.at_ts(FIELD_START));
  let m = p.start();
  field_name(p);
  p.expect(T![:]);
  expr(p);
  m.complete(p, VALUE_OBJ_FIELD)
}
