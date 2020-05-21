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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_name() {
    let src = r#"local a = 5, b = a + 2, c = "foo", d = "bar\\tbaz"; a + b"#;
    parse(src);
  }
}
