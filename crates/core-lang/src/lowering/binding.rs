use crate::{Ident, TextRange};
use jsonnet_syntax::SmolStr;

struct Binding(SmolStr, u32);

#[derive(Default)]
pub(super) struct Binder {
  /// Next binding id
  next: u32,

  /// All bindings currently in scope
  locals: Vec<Binding>,

  /// Indices in the locals vec at which a frame started
  frames: Vec<usize>,
}

impl Binder {
  pub(super) fn new() -> Self {
    Binder::default()
  }

  fn push_frame(&mut self) -> BinderFrame {
    let len = self.locals.len();
    self.frames.push(len);

    BinderFrame {
      binder: self,
      #[cfg(debug_assertions)]
      start: len,
    }
  }

  fn pop_frame(&mut self) -> usize {
    match self.frames.pop() {
      None => panic!("stack inbalance, frame pop called multiple times?"),
      Some(len) => {
        self.locals.truncate(len);

        len
      }
    }
  }

  fn define(&mut self, ident: &SmolStr) -> Option<u32> {
    if let Some(existing) = self
      .locals
      .iter()
      .rev()
      .take(self.locals.len() - *self.frames.last().unwrap())
      .find(|Binding(i, ..)| i == ident)
    {
      return None;
    }

    let id = self.next;
    let binding = Binding(ident.clone(), id);
    self.next += 1;

    // TODO: Validate that we don't have duplicates within the same frame.
    self.locals.push(binding);
    Some(id)
  }

  fn lookup(&self, ident: &SmolStr) -> Option<u32> {
    self
      .locals
      .iter()
      .rev()
      .find_map(|Binding(i, id)| if i == ident { Some(*id) } else { None })
  }
}

pub(super) struct BinderFrame<'a> {
  binder: &'a mut Binder,
  #[cfg(debug_assertions)]
  start: usize,
}

impl<'a> Drop for BinderFrame<'a> {
  fn drop(&mut self) {
    if cfg!(debug_assertions) {
      assert_eq!(self.binder.pop_frame(), self.start);
    } else {
      self.binder.pop_frame();
    }
  }
}

impl<'a> BinderFrame<'a> {
  pub(super) fn define(
    &mut self,
    ident: SmolStr,
    text_range: Option<TextRange>,
  ) -> Result<Ident, String> {
    match self.binder.define(&ident) {
      None => Err(format!("Duplicate binding, '{}' already defined", ident)),
      Some(id) => Ok(Ident {
        name: ident,
        id,
        text_range,
      }),
    }
  }

  pub(super) fn bind(
    &self,
    ident: SmolStr,
    text_range: Option<TextRange>,
  ) -> Result<Ident, String> {
    match self.binder.lookup(&ident) {
      None => Err(format!("Variable '{}' is not defined in this scope", ident)),
      Some(id) => Ok(Ident {
        name: ident,
        id,
        text_range,
      }),
    }
  }

  pub(super) fn frame<'b>(&'b mut self) -> BinderFrame<'b>
  where
    'a: 'b,
  {
    self.binder.push_frame()
  }
}

impl Binder {
  pub(super) fn frame<'a>(&'a mut self) -> BinderFrame<'a> {
    debug_assert_eq!(self.locals.len(), 0);
    self.push_frame()
  }
}
