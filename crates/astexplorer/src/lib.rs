mod describe;

use crate::describe::DescribeExt;
use jsonnet_syntax::SourceFile;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn parse(source: &str) -> JsValue {
  let source_file = SourceFile::parse(source);

  // TODO: Deal with errors somehow
  let tree = source_file.tree();
  JsValue::from_serde(&tree.describe()).unwrap()
}

#[wasm_bindgen]
pub fn desugar(source: &str) -> String {
  use core::fmt::Write;

  let source_file = SourceFile::parse(source);

  // TODO: Deal with errors somehow
  let tree = source_file.tree();
  let (core_expr, errors) = jsonnet_core_lang::desugar(tree);

  let mut buf = format!("{}\n", core_expr);
  for error in source_file.errors() {
    writeln!(buf, "error: {} @{:?}", error, error.range()).unwrap();
  }

  for (loc, error) in errors {
    write!(buf, "error: {}", error).unwrap();
    if let Some(loc) = loc {
      write!(buf, " @{:?}", loc).unwrap();
    }
    buf.push('\n');
  }

  buf
}
