use std::mem;

pub(crate) trait ReplaceWithDefault: Sized {
  fn replace_with_default(&mut self) -> Self;
}

impl<T: Default> ReplaceWithDefault for T {
  #[inline]
  fn replace_with_default(&mut self) -> Self {
    mem::take(self)
  }
}
