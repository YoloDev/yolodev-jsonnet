use crate::{CoreIdent, TextRange};
use core::num::NonZeroU32;
use jsonnet_syntax::{ast, AstToken, SmolStr};

const STD: SmolStr = SmolStr::new_inline_from_ascii(3, b"std");
const UNDEF: SmolStr = SmolStr::new_inline_from_ascii(6, b"$error");

struct Binding(SmolStr, NonZeroU32);

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
    let mut binder = Self {
      next: 1,
      locals: Vec::new(),
      frames: Vec::new(),
    };

    binder.define(&STD).unwrap();
    binder
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

  fn define(&mut self, ident: &SmolStr) -> Option<NonZeroU32> {
    if let Some(_) = self
      .locals
      .iter()
      .rev()
      .take(self.locals.len() - *self.frames.last().unwrap())
      .find(|Binding(i, ..)| i == ident)
    {
      return None;
    }

    let id = NonZeroU32::new(self.next).unwrap();
    let binding = Binding(ident.clone(), id);
    self.next += 1;

    // TODO: Validate that we don't have duplicates within the same frame.
    self.locals.push(binding);
    Some(id)
  }

  fn lookup(&self, ident: &SmolStr) -> Option<NonZeroU32> {
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
  ) -> Result<CoreIdent, String> {
    match self.binder.define(&ident) {
      None => Err(format!("Duplicate binding, '{}' already defined", ident)),
      Some(id) => Ok(CoreIdent {
        name: ident,
        id: Some(id),
        text_range,
      }),
    }
  }

  pub(super) fn define_from(&mut self, ident: ast::Ident) -> Result<CoreIdent, String> {
    self.define(
      ident.syntax().text().clone(),
      Some(ident.syntax().text_range()),
    )
  }

  pub(super) fn bind(
    &self,
    ident: SmolStr,
    text_range: Option<TextRange>,
  ) -> Result<CoreIdent, String> {
    match self.binder.lookup(&ident) {
      None => Err(format!("Variable '{}' is not defined in this scope", ident)),
      Some(id) => Ok(CoreIdent {
        name: ident,
        id: Some(id),
        text_range,
      }),
    }
  }

  pub(super) fn bind_from(&self, ident: ast::Ident) -> Result<CoreIdent, String> {
    self.bind(
      ident.syntax().text().clone(),
      Some(ident.syntax().text_range()),
    )
  }

  pub(super) fn new_undef(&self) -> CoreIdent {
    CoreIdent {
      name: UNDEF.clone(),
      id: None,
      text_range: None,
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
