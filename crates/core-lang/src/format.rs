use core::fmt;
use pretty::{Arena, BuildDoc, Doc, DocPtr};

pub(crate) use pretty::{DocAllocator, DocBuilder};

trait WithContext<'a> {
  fn with_context(self, context: &'a Context<'a>) -> DocBuilder<'a, Context<'a>, ()>;
}

impl<'a> WithContext<'a> for DocBuilder<'a, Arena<'a, ()>, ()> {
  #[inline]
  fn with_context(self, context: &'a Context<'a>) -> DocBuilder<'a, Context<'a>, ()> {
    DocBuilder(context, self.1)
  }
}

#[derive(Default)]
pub(crate) struct Context<'a> {
  arena: Arena<'a, ()>,
}

impl<'a> DocAllocator<'a, ()> for Context<'a> {
  type Doc = <Arena<'a, ()> as DocAllocator<'a, ()>>::Doc;

  #[inline]
  fn alloc(&'a self, doc: Doc<'a, Self::Doc, ()>) -> Self::Doc {
    self.arena.alloc(doc)
  }

  #[inline]
  fn alloc_column_fn(
    &'a self,
    f: impl Fn(usize) -> Self::Doc + 'a,
  ) -> <Self::Doc as DocPtr<'a, ()>>::ColumnFn {
    self.arena.alloc_column_fn(f)
  }

  #[inline]
  fn alloc_width_fn(
    &'a self,
    f: impl Fn(isize) -> Self::Doc + 'a,
  ) -> <Self::Doc as DocPtr<'a, ()>>::WidthFn {
    self.arena.alloc_width_fn(f)
  }

  #[inline]
  fn alloc_cow(&'a self, doc: BuildDoc<'a, Self::Doc, ()>) -> Self::Doc {
    self.arena.alloc_cow(doc)
  }

  #[inline]
  fn nil(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.nil().with_context(self)
  }

  #[inline]
  fn fail(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.fail().with_context(self)
  }

  #[inline]
  fn hardline(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.hardline().with_context(self)
  }

  #[inline]
  fn space(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.space().with_context(self)
  }

  #[inline]
  fn line(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.line().with_context(self)
  }

  #[inline]
  fn line_(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.line_().with_context(self)
  }

  #[inline]
  fn softline(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.softline().with_context(self)
  }

  #[inline]
  fn softline_(&'a self) -> DocBuilder<'a, Self, ()> {
    self.arena.softline_().with_context(self)
  }

  #[inline]
  fn as_string<U: std::fmt::Display>(&'a self, data: U) -> DocBuilder<'a, Self, ()> {
    self.arena.as_string(data).with_context(self)
  }

  #[inline]
  fn text<U: Into<std::borrow::Cow<'a, str>>>(&'a self, data: U) -> DocBuilder<'a, Self, ()> {
    self.arena.text(data).with_context(self)
  }

  #[inline]
  fn concat<I>(&'a self, docs: I) -> DocBuilder<'a, Self, ()>
  where
    I: IntoIterator,
    I::Item: Into<BuildDoc<'a, Self::Doc, ()>>,
  {
    self.arena.concat(docs).with_context(self)
  }

  #[inline]
  fn intersperse<I, S>(&'a self, docs: I, separator: S) -> DocBuilder<'a, Self, ()>
  where
    I: IntoIterator,
    I::Item: Into<BuildDoc<'a, Self::Doc, ()>>,
    S: Into<BuildDoc<'a, Self::Doc, ()>> + Clone,
  {
    self.arena.intersperse(docs, separator).with_context(self)
  }

  #[inline]
  fn column(&'a self, f: impl Fn(usize) -> Self::Doc + 'a) -> DocBuilder<'a, Self, ()> {
    self.arena.column(f).with_context(self)
  }

  #[inline]
  fn nesting(&'a self, f: impl Fn(usize) -> Self::Doc + 'a) -> DocBuilder<'a, Self, ()> {
    self.arena.nesting(f).with_context(self)
  }

  #[inline]
  fn reflow(&'a self, text: &'a str) -> DocBuilder<'a, Self, ()>
  where
    Self: Sized,
    Self::Doc: Clone,
    (): Clone,
  {
    self.arena.reflow(text).with_context(self)
  }
}

pub(crate) trait CodeFormat {
  fn format<'ctx, 'a: 'ctx>(
    &'a self,
    f: &'ctx Context<'ctx>,
  ) -> DocBuilder<'ctx, Context<'ctx>, ()>;
}

pub(crate) fn format_code(code: &dyn CodeFormat, f: &mut fmt::Formatter) -> fmt::Result {
  let ctx = Context::default();
  let doc: BuildDoc<_, ()> = code.format(&ctx).into();

  write!(f, "{}", doc.pretty(80))
}

macro_rules! impl_display_code {
  ($ty:ty) => {
    impl ::core::fmt::Display for $ty {
      fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        $crate::format::format_code(self, f)
      }
    }
  };
}

macro_rules! impl_format {
  (
    fn $ty:ident ($inst:tt, $ctx:tt) $body:block
  ) => {
    impl $crate::format::CodeFormat for $ty {
      fn format<'ctx, 'a: 'ctx>(
        &'a self,
        f: &'ctx $crate::format::Context<'ctx>,
      ) -> $crate::format::DocBuilder<'ctx, Context<'ctx>, ()> {
        let $inst = self;
        let $ctx = f;

        $body
      }
    }

    impl_display_code!($ty);
  };
}

mod expr;

#[cfg(test)]
mod tests {
  use jsonnet_syntax::{SourceFile, TextRange};

  use core::fmt;

  #[derive(PartialEq, Eq, Clone, Copy)]
  struct PrettyString<'a>(&'a str);

  impl<'a> PrettyString<'a> {
    #[inline]
    fn new<S: AsRef<str> + ?Sized>(value: &'a S) -> Self {
      PrettyString(value.as_ref())
    }
  }

  impl<'a> fmt::Debug for PrettyString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      f.write_str(self.0)
    }
  }

  macro_rules! assert_eq {
    ($left:expr, $right:expr $(,$($rest:tt)*)?) => {
      pretty_assertions::assert_eq!(
        PrettyString::new($left),
        PrettyString::new($right)
        $(,$($rest)*)?
      );
    }
  }

  struct WriteErrors<'a>(&'a Vec<(Option<TextRange>, String)>);

  impl<'a> fmt::Display for WriteErrors<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      for item in self.0 {
        f.write_str("\n  ")?;
        f.write_str(&item.1)?;

        if let Some(range) = item.0 {
          write!(f, " @{:?}", range)?;
        }
      }

      Ok(())
    }
  }

  #[test_gen::test_golden("test_data/ok/*.jsonnet")]
  fn golden_ok(content: &str, _: &str) -> String {
    let syntax = SourceFile::parse(content);
    let (core, errors) = crate::desugar(syntax.tree());
    if errors.len() > 0 {
      panic!(
        "Expected no errors, but found {}: {}",
        errors.len(),
        WriteErrors(&errors)
      );
    }

    format!("{}", core)
  }
}
