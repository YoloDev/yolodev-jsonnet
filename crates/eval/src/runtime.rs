use gc::{unsafe_empty_trace, Gc, Trace};
use std::{path::Path, path::PathBuf};

use crate::{
  expr::bind_expr,
  lazy::EvalContext,
  lazy::{EvalError, LazyValue},
  Value,
};

pub trait Resolver {
  fn resolve(&self, path: &Path, from: &Path) -> Option<PathBuf>;
}

pub struct DeafultResolver;

impl Resolver for DeafultResolver {
  #[inline]
  fn resolve(&self, path: &Path, from: &Path) -> Option<PathBuf> {
    Some(from.join(path))
  }
}

pub struct ChainResolver<R1: Resolver + 'static, R2: Resolver + 'static>(R1, R2);

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

pub struct DefaultLoader;

impl Loader for DefaultLoader {
  #[inline]
  fn load(&self, path: &Path) -> Result<Option<String>, std::io::Error> {
    std::fs::read_to_string(path).map(Some)
  }
}

pub struct ChainLoader<L1: Loader + 'static, L2: Loader + 'static>(L1, L2);

impl<L1: Loader, L2: Loader> Loader for ChainLoader<L1, L2> {
  fn load(&self, path: &Path) -> Result<Option<String>, std::io::Error> {
    self.0.load(path).and_then(|r| match r {
      None => self.1.load(path),
      Some(r) => Ok(Some(r)),
    })
  }
}

pub(crate) struct Engine {
  resolver: Box<dyn Resolver>,
  loader: Box<dyn Loader>,
}

unsafe impl Trace for Engine {
  unsafe_empty_trace! {}
}

#[derive(Trace)]
pub struct Runtime(Gc<Engine>);

pub(crate) struct SourceFile {
  pub content: String,
  pub path: PathBuf,
}

impl Runtime {
  #[inline]
  pub fn new() -> Self {
    Self::default()
  }

  #[inline]
  pub fn builder() -> RuntimeBuilder<DefaultLoader, DeafultResolver> {
    RuntimeBuilder {
      loader: DefaultLoader,
      resolver: DeafultResolver,
    }
  }

  pub fn run(&self, source: &str, file_name: &Path) -> Result<Value, EvalError> {
    let engine = self.0.clone();
    self.0.run(source, file_name, engine)
  }
}

impl Default for Runtime {
  #[inline]
  fn default() -> Self {
    Self::builder().build()
  }
}

pub struct RuntimeBuilder<L: Loader + 'static, R: Resolver + 'static> {
  loader: L,
  resolver: R,
}

impl<L: Loader + 'static, R: Resolver + 'static> RuntimeBuilder<L, R> {
  pub fn build(self) -> Runtime {
    Runtime(Gc::new(Engine {
      resolver: Box::new(self.resolver),
      loader: Box::new(self.loader),
    }))
  }

  #[inline]
  pub fn with_loader<L2: Loader + 'static>(self, loader: L2) -> RuntimeBuilder<L2, R> {
    RuntimeBuilder {
      loader,
      resolver: self.resolver,
    }
  }

  #[inline]
  pub fn with_resolver<R2: Resolver + 'static>(self, resolver: R2) -> RuntimeBuilder<L, R2> {
    RuntimeBuilder {
      loader: self.loader,
      resolver,
    }
  }

  #[inline]
  pub fn add_loader<L2: Loader + 'static>(
    self,
    loader: L2,
  ) -> RuntimeBuilder<ChainLoader<L2, L>, R> {
    RuntimeBuilder {
      loader: ChainLoader(loader, self.loader),
      resolver: self.resolver,
    }
  }

  #[inline]
  pub fn add_resolver<R2: Resolver + 'static>(
    self,
    resolver: R2,
  ) -> RuntimeBuilder<L, ChainResolver<R2, R>> {
    RuntimeBuilder {
      loader: self.loader,
      resolver: ChainResolver(resolver, self.resolver),
    }
  }
}

impl Engine {
  pub(crate) fn import(&self, target: &Path, source: &Path) -> Result<SourceFile, EvalError> {
    let path = self
      .resolver
      .resolve(target, source)
      .ok_or_else(|| EvalError::new(format!("File {} not found", target.display()), None))?;
    let content = self
      .loader
      .load(&path)
      .map_err(|e| {
        EvalError::new(
          format!("Failed to load file {}: {:?}", path.display(), e),
          None,
        )
      })?
      .ok_or_else(|| EvalError::new(format!("Failed to load file {}", path.display()), None))?;

    Ok(SourceFile { content, path })
  }

  fn eval(&self, content: &str, ctx: EvalContext) -> Result<LazyValue, EvalError> {
    let ast = jsonnet_syntax::SourceFile::parse(content)
      .ok()
      .map_err(|_e| EvalError::new(format!("Failed to parse {}", ctx.source.display()), None))?;

    let (core_expr, errors) = jsonnet_core_lang::desugar(ast);
    if !errors.is_empty() {
      return Err(EvalError::new(
        format!("Failed to desugar {}", ctx.source.display()),
        None,
      ));
    }

    let bound = bind_expr(&core_expr)
      .map_err(|e| EvalError::new(format!("Failed to bind. {}", e.message), e.location))?;

    bound.eval(ctx)
  }

  pub(crate) fn eval_file(
    &self,
    file: SourceFile,
    ctx: EvalContext,
  ) -> Result<LazyValue, EvalError> {
    let ctx = ctx.with_source(Gc::new(file.path));
    self.eval(&file.content, ctx)
  }

  fn run(&self, source: &str, file_name: &Path, engine: Gc<Engine>) -> Result<Value, EvalError> {
    let ctx = EvalContext::new(engine, Gc::new(file_name.into()));
    let lazy = self.eval(source, ctx)?;
    let forced = lazy.force()?;
    Ok(Value::clone(&forced))
  }
}
