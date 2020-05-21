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
