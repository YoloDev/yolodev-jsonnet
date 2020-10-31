use std::{fmt::Debug, path::Path, path::PathBuf};

use gc::{Gc, Trace};

use crate::{lazy::EvalError, Value};

pub trait Resolver {
  fn resolve(&self, path: &Path, from: &Path) -> Option<PathBuf>;
}

struct DeafultResolver;

impl Resolver for DeafultResolver {
  #[inline]
  fn resolve(&self, path: &Path, from: &Path) -> Option<PathBuf> {
    Some(from.join(path))
  }
}

struct ChainResolver<R1: Resolver, R2: Resolver>(R1, R2);

impl<R1: Resolver, R2: Resolver> Resolver for ChainResolver<R1, R2> {
  fn resolve(&self, path: &Path, from: &Path) -> Option<PathBuf> {
    self
      .0
      .resolve(path, from)
      .or_else(|| self.1.resolve(path, from))
  }
}

pub trait Loader {
  fn load(&self, path: &Path) -> Result<Option<String>, std::io::Error>;
}

struct DefaultLoader;

impl Loader for DefaultLoader {
  #[inline]
  fn load(&self, path: &Path) -> Result<Option<String>, std::io::Error> {
    std::fs::read_to_string(path).map(Some)
  }
}

struct ChainLoader<L1: Loader, L2: Loader>(L1, L2);

impl<L1: Loader, L2: Loader> Loader for ChainLoader<L1, L2> {
  fn load(&self, path: &Path) -> Result<Option<String>, std::io::Error> {
    self.0.load(path).and_then(|r| match r {
      None => self.1.load(path),
      Some(r) => Ok(Some(r)),
    })
  }
}

pub trait Engine {
  fn eval(&self, source: &str) -> Result<Value, EvalError>;

  fn import_str(&self, path: &str) -> Result<String, EvalError>;

  fn import_jsonnet(&self, path: &str) -> Result<Value, EvalError>;
}

struct DefaultEngine<R: Resolver, L: Loader> {
  resolver: R,
  loader: L,
}
