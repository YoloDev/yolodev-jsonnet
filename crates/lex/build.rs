use std::path::Path;
use walkdir::{DirEntry, WalkDir};

fn is_hidden(entry: &DirEntry) -> bool {
  entry
    .file_name()
    .to_str()
    .map(|s| s.starts_with("."))
    .unwrap_or(false)
}

fn rerun_if_any_changed(p: impl AsRef<Path>) {
  for entry in WalkDir::new(p.as_ref())
    .into_iter()
    .filter_entry(|e| !is_hidden(e))
  {
    let entry = entry.unwrap();
    println!("cargo:rerun-if-changed={}", entry.path().display());
  }
}

fn main() {
  rerun_if_any_changed("test_data");
  println!("cargo:rerun-if-env-changed=CI");
}
