mod array;
mod atom;
mod bind;
mod expr;
mod fields;
mod object;

use crate::{
  parser::{CompletedMarker, Parser},
  SyntaxKind::{self, *},
  TokenSet, TokenSource,
};

use array::*;
use atom::*;
use bind::*;
use expr::*;
use fields::*;
use object::*;

pub(crate) fn root<S: TokenSource>(p: &mut Parser<S>) {
  let m = p.start();
  p.eat(SHEBANG);
  expr(p);
  m.complete(p, SOURCE_FILE);
}
