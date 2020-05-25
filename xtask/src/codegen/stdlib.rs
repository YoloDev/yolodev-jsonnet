use crate::{
  codegen::{self, update, Mode},
  project_root, Result,
};
use anyhow::bail;
use jsonnet_core_lang::desugar;
use jsonnet_syntax::SourceFile;
use quote::quote;
use std::fs;

pub fn generate_stdlib(mode: Mode) -> Result<()> {
  let in_file = project_root().join(codegen::STDLIB_SOURCE);
  let source = fs::read_to_string(&in_file)?;
  let source_file = SourceFile::parse(&source);

  // TODO: Deal with errors somehow
  let tree = source_file.tree();
  let (core_expr, errors) = desugar(tree);
  if !errors.is_empty() {
    for (_, error) in errors {
      println!("std.jsonnet error: {}", error);
    }

    bail!("std.jsonnet produced errors");
  }

  let generated = quote! {
    pub(crate) fn get() -> ::jsonnet_core_lang::CoreExpr {
      #core_expr
    }
  };

  let output = crate::reformat(generated.to_string().replace("fn ", "\nfn "))?;

  let out_file = project_root().join(codegen::STDLIB_OUT);
  update(out_file.as_path(), &output, mode)
}
