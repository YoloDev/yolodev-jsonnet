mod stdlib;

use jsonnet_core_lang::CoreExpr;

pub fn get_stdlib() -> CoreExpr {
  stdlib::get()
}
