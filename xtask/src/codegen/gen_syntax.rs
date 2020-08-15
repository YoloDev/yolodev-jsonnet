//! This module generates AST datatype used by jsonnet.
//!
//! Specifically, it generates the `SyntaxKind` enum and a number of newtype
//! wrappers around `SyntaxNode` which implement `syntax::AstNode`.

use std::{
  collections::{BTreeSet, HashSet},
  fmt::Write,
  str::FromStr,
};

use proc_macro2::{Punct, Spacing};
use quote::{format_ident, quote};
use ungrammar::{Grammar, Rule};

use crate::{
  ast_src::{AstEnumSrc, AstNodeSrc, AstSrc, Cardinality, Field},
  codegen::{self, update, Mode},
  project_root, Result,
};

pub fn generate_syntax(mode: Mode) -> Result<()> {
  let grammar_src = include_str!("../../jsonnet.ungram");
  let grammar = Grammar::from_str(grammar_src)?;
  let ast = lower(&grammar);

  let ast_tokens_file = project_root().join(codegen::AST_TOKENS);
  let contents = generate_tokens(&ast)?;
  update(ast_tokens_file.as_path(), &contents, mode)?;

  Ok(())
}

fn generate_tokens(grammar: &AstSrc) -> Result<String> {
  let tokens = grammar.tokens.iter().map(|token| {
    let name = format_ident!("{}", token);
    let kind = format_ident!("{}", to_upper_snake_case(token));

    quote! {
      #[derive(Debug, Clone, PartialEq, Eq, Hash)]
      pub struct #name {
        pub(crate) syntax: SyntaxToken,
      }

      impl std::fmt::Display for #name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          std::fmt::Display::fmt(&self.syntax, f)
        }
      }

      impl AstToken for #name {
        fn can_cast(kind: SyntaxKind) -> bool { kind == #kind }
        fn cast(syntax: SyntaxToken) -> Option<Self> {
          if Self::can_cast(syntax.kind()) { Some(Self { syntax }) } else { None }
        }
        fn syntax(&self) -> &SyntaxToken { &self.syntax }
      }
    }
  });

  let pretty = crate::reformat(quote! {
    use crate::{SyntaxKind::{self, *}, SyntaxToken, ast::AstToken};
    #(#tokens)*
  })?
  .replace("#[derive", "\n#[derive");
  Ok(pretty)
}

fn lower(grammar: &Grammar) -> AstSrc {
  let mut res = AstSrc::default();

  res.tokens = vec![
    "Whitespace".into(),
    "Comment".into(),
    "Ident".into(),
    "Number".into(),
  ];

  let nodes = grammar.iter().collect::<Vec<_>>();
  for &node in &nodes {
    let name = grammar[node].name.clone();
    let rule = &grammar[node].rule;
    match lower_enum(grammar, rule) {
      Some(variants) => {
        let enum_src = AstEnumSrc {
          doc: Vec::new(),
          name,
          traits: Vec::new(),
          variants,
        };
        res.enums.push(enum_src);
      }
      None => {
        let mut fields = Vec::new();
        lower_rule(&mut fields, grammar, None, rule);
        res.nodes.push(AstNodeSrc {
          doc: Vec::new(),
          name,
          traits: Vec::new(),
          fields,
        });
      }
    }
  }

  deduplicate_fields(&mut res);
  // extract_enums(&mut res);
  // extract_struct_traits(&mut res);
  // extract_enum_traits(&mut res);
  res
}

fn lower_enum(grammar: &Grammar, rule: &Rule) -> Option<Vec<String>> {
  let alternatives = match rule {
    Rule::Alt(it) => it,
    _ => return None,
  };

  let mut variants = Vec::new();
  for alternative in alternatives {
    match alternative {
      Rule::Node(it) => variants.push(grammar[*it].name.clone()),
      Rule::Token(it) if grammar[*it].name == ";" => (),
      _ => return None,
    }
  }

  Some(variants)
}

fn lower_rule(acc: &mut Vec<Field>, grammar: &Grammar, label: Option<&String>, rule: &Rule) {
  if lower_comma_list(acc, grammar, label, rule) {
    return;
  }

  match rule {
    Rule::Node(node) => {
      let ty = grammar[*node].name.clone();
      let name = label.cloned().unwrap_or_else(|| to_lower_snake_case(&ty));
      let field = Field::Node {
        name,
        ty,
        cardinality: Cardinality::Optional,
      };
      acc.push(field);
    }

    Rule::Token(token) => {
      assert!(label.is_none());
      let mut name = grammar[*token].name.clone();
      if name != "int_number" && name != "string" {
        if "[]{}()".contains(&name) {
          name = format!("'{}'", name);
        }
        let field = Field::Token(name);
        acc.push(field);
      }
    }

    Rule::Rep(inner) => {
      if let Rule::Node(node) = &**inner {
        let ty = grammar[*node].name.clone();
        let name = label
          .cloned()
          .unwrap_or_else(|| pluralize(&to_lower_snake_case(&ty)));
        let field = Field::Node {
          name,
          ty,
          cardinality: Cardinality::Many,
        };
        acc.push(field);
        return;
      }
      todo!("{:?}", rule)
    }

    Rule::Labeled { label: l, rule } => {
      assert!(label.is_none());
      // let manually_implemented = matches!(
      //   l.as_str(),
      //   "lhs"
      //     | "rhs"
      //     | "then_branch"
      //     | "else_branch"
      //     | "start"
      //     | "end"
      //     | "op"
      //     | "index"
      //     | "base"
      //     | "value"
      //     | "trait"
      //     | "self_ty"
      // );
      // if manually_implemented {
      //   return;
      // }
      lower_rule(acc, grammar, Some(l), rule);
    }

    Rule::Seq(rules) | Rule::Alt(rules) => {
      for rule in rules {
        lower_rule(acc, grammar, label, rule)
      }
    }

    Rule::Opt(rule) => lower_rule(acc, grammar, label, rule),
  }
}

// (T (',' T)* ','?)
fn lower_comma_list(
  acc: &mut Vec<Field>,
  grammar: &Grammar,
  label: Option<&String>,
  rule: &Rule,
) -> bool {
  let rule = match rule {
    Rule::Seq(it) => it,
    _ => return false,
  };

  let (node, repeat, trailing_comma) = match rule.as_slice() {
    [Rule::Node(node), Rule::Rep(repeat), Rule::Opt(trailing_comma)] => {
      (node, repeat, trailing_comma)
    }
    _ => return false,
  };

  let repeat = match &**repeat {
    Rule::Seq(it) => it,
    _ => return false,
  };

  match repeat.as_slice() {
    [comma, Rule::Node(n)] if comma == &**trailing_comma && n == node => (),
    _ => return false,
  }

  let ty = grammar[*node].name.clone();
  let name = label
    .cloned()
    .unwrap_or_else(|| pluralize(&to_lower_snake_case(&ty)));
  let field = Field::Node {
    name,
    ty,
    cardinality: Cardinality::Many,
  };
  acc.push(field);

  true
}

fn deduplicate_fields(ast: &mut AstSrc) {
  for node in &mut ast.nodes {
    let mut i = 0;
    'outer: while i < node.fields.len() {
      for j in 0..i {
        let f1 = &node.fields[i];
        let f2 = &node.fields[j];
        if f1 == f2 {
          node.fields.remove(i);
          continue 'outer;
        }
      }
      i += 1;
    }
  }
}

fn pluralize(s: &str) -> String {
  format!("{}s", s)
}

fn to_upper_snake_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev = false;
  for c in s.chars() {
    if c.is_ascii_uppercase() && prev {
      buf.push('_')
    }
    prev = true;

    buf.push(c.to_ascii_uppercase());
  }
  buf
}

fn to_lower_snake_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev = false;
  for c in s.chars() {
    if c.is_ascii_uppercase() && prev {
      buf.push('_')
    }
    prev = true;

    buf.push(c.to_ascii_lowercase());
  }
  buf
}

fn to_pascal_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev_is_underscore = true;
  for c in s.chars() {
    if c == '_' {
      prev_is_underscore = true;
    } else if prev_is_underscore {
      buf.push(c.to_ascii_uppercase());
      prev_is_underscore = false;
    } else {
      buf.push(c.to_ascii_lowercase());
    }
  }
  buf
}
