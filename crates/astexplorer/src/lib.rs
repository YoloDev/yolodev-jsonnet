use jsonnet_syntax::{ast::AstDescribe, ast::AstDescription, SourceFile};
use serde::ser::*;
use wasm_bindgen::prelude::*;

enum DescriptionWrapper<'a> {
  Node(&'a dyn AstDescribe),
  List(Vec<Box<dyn AstDescribe>>),
}

impl<'a> Serialize for DescriptionWrapper<'a> {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    match self {
      DescriptionWrapper::Node(n) => serialize_node(*n, serializer),
      DescriptionWrapper::List(l) => serialize_list(l, serializer),
      //AstDescription::Token(_) => todo!(),
    }
  }
}

fn serialize_node<S>(node: &dyn AstDescribe, serializer: S) -> Result<S::Ok, S::Error>
where
  S: serde::Serializer,
{
  let children = node.describe_children().collect::<Vec<_>>();
  let mut s = serializer.serialize_struct("node", children.len() + 2)?;
  s.serialize_field("type", node.describe_kind())?;
  s.serialize_field("span", &node.describe_span())?;
  for (child_name, child) in children {
    match child {
      None => s.serialize_field(child_name, &()),
      Some(AstDescription::Node(n)) => {
        s.serialize_field(child_name, &DescriptionWrapper::Node(n.as_ref()))
      }
      Some(AstDescription::List(l)) => {
        s.serialize_field(child_name, &DescriptionWrapper::List(l.collect()))
      }
      Some(AstDescription::Token(_)) => todo!(),
    }?;
  }
  s.end()
}

fn serialize_list<S>(list: &Vec<Box<dyn AstDescribe>>, serializer: S) -> Result<S::Ok, S::Error>
where
  S: serde::Serializer,
{
  let mut s = serializer.serialize_seq(Some(list.len()))?;
  for item in list {
    s.serialize_element(&DescriptionWrapper::Node(item.as_ref()))?;
  }

  s.end()
}

#[wasm_bindgen]
pub fn parse(source: &str) -> JsValue {
  let source_file = SourceFile::parse(source);

  // TODO: Deal with errors somehow
  let tree = source_file.tree();
  JsValue::from_serde(&DescriptionWrapper::Node(&tree)).unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn kitchen_sink() {
    use jsonnet_syntax::ast::*;

    let source_file = SourceFile::parse("local a = 5, b = a; a + b");
    let tree = source_file.tree();
    println!("{}", source_file.debug_dump());
    let local = match tree.root().expect("root") {
      Expr::Local(l) => l,
      _ => panic!("expected local expr"),
    };
    let rest = local.rest().expect("rest");
    let binds = local.binds().expect("binds").bindings().collect::<Vec<_>>();
    assert_eq!(binds.len(), 2);
    JsValue::from_serde(&DescriptionWrapper::Node(&tree)).unwrap();
    panic!("err synth");
  }
}
