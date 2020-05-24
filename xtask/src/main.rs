//! See https://github.com/matklad/cargo-xtask/.
//!
//! This binary defines various auxiliary build commands, which are not
//! expressible with just `cargo`. Notably, it provides `cargo xtask codegen`
//! for code generation and `cargo xtask install` for installation of
//! rust-analyzer server and client.
//!
//! This binary is integrated into the `cargo` command line by using an alias in
//! `.cargo/config`.

use std::env;

use pico_args::Arguments;
use xtask::{
  codegen::{self, Mode},
  pre_commit, project_root, run_clippy, run_rustfmt,
  shell::pushd,
  Result,
};

fn main() -> Result<()> {
  if env::args().next().map(|it| it.contains("pre-commit")) == Some(true) {
    return pre_commit::run_hook();
  }

  let _d = pushd(project_root());

  let mut args = Arguments::from_env();
  let subcommand = args.subcommand()?.unwrap_or_default();

  match subcommand.as_str() {
    "codegen" => {
      args.finish()?;
      //codegen::generate_syntax(Mode::Overwrite)?;
      codegen::generate_parser_tests(Mode::Overwrite)?;
      codegen::generate_stdlib(Mode::Overwrite)?;
      //codegen::generate_assists_docs(Mode::Overwrite)?;
      Ok(())
    }
    "format" => {
      args.finish()?;
      run_rustfmt(Mode::Overwrite)
    }
    "install-pre-commit-hook" => {
      args.finish()?;
      pre_commit::install_hook()
    }
    "lint" => {
      args.finish()?;
      run_clippy()
    }
    _ => {
      eprintln!(
        "\
cargo xtask
Run custom build command.

USAGE:
    cargo xtask <SUBCOMMAND>

SUBCOMMANDS:
    format
    install-pre-commit-hook
    codegen
    lint"
      );
      Ok(())
    }
  }
}
