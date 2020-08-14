//! Support library for `cargo xtask` command.
//!
//! See https://github.com/matklad/cargo-xtask/

pub mod ast_src;
pub mod codegen;
pub mod pre_commit;
pub mod shell;

use std::{
  env,
  path::{Path, PathBuf},
};
use walkdir::{DirEntry, WalkDir};

use crate::{
  codegen::Mode,
  shell::{pushd, pushenv, run},
};

pub use anyhow::{bail, Context as _, Result};

pub fn project_root() -> PathBuf {
  Path::new(
    &env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| env!("CARGO_MANIFEST_DIR").to_owned()),
  )
  .ancestors()
  .nth(1)
  .unwrap()
  .to_path_buf()
}

pub fn rust_files(path: &Path) -> impl Iterator<Item = PathBuf> {
  let iter = WalkDir::new(path);

  return iter
    .into_iter()
    .filter_entry(|e| !is_hidden(e))
    .map(|e| e.unwrap())
    .filter(|e| !e.file_type().is_dir())
    .map(|e| e.into_path())
    .filter(|path| path.extension().map(|it| it == "rs").unwrap_or(false));

  fn is_hidden(entry: &DirEntry) -> bool {
    entry
      .file_name()
      .to_str()
      .map(|s| s.starts_with('.'))
      .unwrap_or(false)
  }
}

pub fn run_rustfmt(mode: Mode) -> Result<()> {
  let _dir = pushd(project_root());
  let _e = pushenv("RUSTUP_TOOLCHAIN", "stable");

  ensure_rustfmt()?;
  match mode {
    Mode::Overwrite => run!("cargo fmt"),
    Mode::Verify => run!("cargo fmt -- --check"),
  }?;
  Ok(())
}

fn reformat(text: impl std::fmt::Display) -> Result<String> {
  let _e = pushenv("RUSTUP_TOOLCHAIN", "stable");

  ensure_rustfmt()?;
  let stdout = run!(
      "rustfmt --config-path {} --config fn_single_line=true", project_root().join("rustfmt.toml").display();
      <text.to_string().as_bytes()
  )?;

  let preamble = "Generated file, do not edit by hand, see `xtask/src/codegen`";
  Ok(format!("//! {}\n\n{}\n", preamble, stdout))
}

fn ensure_rustfmt() -> Result<()> {
  let out = run!("rustfmt --version")?;
  if !out.contains("stable") {
    bail!(
      "Failed to run rustfmt from toolchain 'stable'. \
           Please run `rustup component add rustfmt --toolchain stable` to install it.",
    )
  }
  Ok(())
}

pub fn run_clippy() -> Result<()> {
  if run!("cargo clippy --version").is_err() {
    bail!(
      "Failed run cargo clippy. \
          Please run `rustup component add clippy` to install it.",
    )
  }

  let allowed_lints: [&str; 0] = [
    // "clippy::collapsible_if",
    // "clippy::needless_pass_by_value",
    // "clippy::nonminimal_bool",
    // "clippy::redundant_pattern_matching",
  ];

  run!(
    "cargo clippy --all-features --all-targets -- -A {}",
    allowed_lints.join(" -A ")
  )?;
  Ok(())
}
