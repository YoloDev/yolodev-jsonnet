//! Module for generating code.

mod gen_parser_tests;
mod gen_syntax;
mod stdlib;

use std::{mem, path::Path};

use crate::{shell::fs2, Result};

pub use self::gen_parser_tests::generate_parser_tests;
pub use self::stdlib::generate_stdlib;

const GRAMMAR_DIR: &str = "crates/parse/src/grammar";
const OK_INLINE_TESTS_DIRS: &[&str] = &[
  "crates/syntax/test_data/inline/ok",
  "crates/lex/test_data/inline/ok",
];
const ERR_INLINE_TESTS_DIRS: &[&str] = &[
  "crates/syntax/test_data/inline/err",
  "crates/lex/test_data/inline/err",
];

const STDLIB_SOURCE: &str = "crates/stdlib/std.jsonnet";
const STDLIB_OUT: &str = "crates/stdlib/src/stdlib.rs";

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mode {
  Overwrite,
  Verify,
}

/// A helper to update file on disk if it has changed.
/// With verify = false,
fn update(path: &Path, contents: &str, mode: Mode) -> Result<()> {
  match fs2::read_to_string(path) {
    Ok(ref old_contents) if normalize(old_contents) == normalize(contents) => {
      return Ok(());
    }
    _ => (),
  }
  if mode == Mode::Verify {
    anyhow::bail!("`{}` is not up-to-date", path.display());
  }

  eprintln!("updating {}", path.display());
  fs2::write(path, contents)?;
  return Ok(());

  fn normalize(s: &str) -> String {
    s.replace("\r\n", "\n")
  }
}

fn extract_comment_blocks(text: &str) -> Vec<Vec<String>> {
  do_extract_comment_blocks(text, false)
}

fn do_extract_comment_blocks(text: &str, allow_blocks_with_empty_lines: bool) -> Vec<Vec<String>> {
  let mut res = Vec::new();

  let prefix = "// ";
  let lines = text.lines().map(str::trim_start);

  let mut block = vec![];
  for line in lines {
    if line == "//" && allow_blocks_with_empty_lines {
      block.push(String::new());
      continue;
    }

    let is_comment = line.starts_with(prefix);
    if is_comment {
      block.push(line[prefix.len()..].to_string());
    } else if !block.is_empty() {
      res.push(mem::replace(&mut block, Vec::new()));
    }
  }
  if !block.is_empty() {
    res.push(mem::replace(&mut block, Vec::new()))
  }
  res
}
