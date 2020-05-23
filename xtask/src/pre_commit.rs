//! pre-commit hook for code formatting.

use std::{fs, path::PathBuf};

use anyhow::Result;

use crate::{project_root, run_rustfmt, shell::run, Mode};

pub fn run_hook() -> Result<()> {
  run_rustfmt(Mode::Overwrite)?;

  let diff = run!("git diff --diff-filter=MAR --name-only --cached")?;

  let root = project_root();
  for line in diff.lines() {
    run!("git update-index --add {}", root.join(line).display())?;
  }

  Ok(())
}

pub fn install_hook() -> Result<()> {
  let hook_path: PathBuf =
    format!("./.git/hooks/pre-commit{}", std::env::consts::EXE_SUFFIX).into();

  if hook_path.exists() {
    fs::remove_file(&hook_path)?;
  }

  let me = std::env::current_exe()?;
  fs::copy(me, hook_path)?;

  Ok(())
}
