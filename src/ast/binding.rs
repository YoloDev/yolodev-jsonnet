use alloc::rc::Rc;
use hashbrown::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Symbol(usize);

impl Symbol {
  pub(crate) const ERROR: Symbol = Symbol(0);
}

// TODO: At this point, we could definitely intern the strings if wanted...
#[derive(Debug)]
struct BinderStore {
  next: usize,
  lookup: HashMap<usize, Rc<str>>,
}

impl BinderStore {
  fn new() -> Self {
    BinderStore {
      next: 1,
      lookup: HashMap::new(),
    }
  }

  pub(crate) fn insert(&mut self, name: Rc<str>) -> Symbol {
    let id = self.next;
    self.next += 1;
    self.lookup.insert(id, name);
    Symbol(id)
  }
}

// TODO: This whole thing could be simplified a lot using a stack...
#[derive(Debug)]
enum Scope<'store, 'parent: 'store> {
  Root {
    store: &'store mut BinderStore,
    names: HashMap<Rc<str>, Symbol>,
  },
  Child {
    parent: &'parent mut Scope<'parent, 'store>,
    names: HashMap<Rc<str>, Symbol>,
  },
}

impl<'store, 'parent: 'store> Scope<'parent, 'store> {
  fn store(&mut self) -> &mut BinderStore {
    match self {
      Scope::Root { store, .. } => *store,
      Scope::Child { parent, .. } => parent.store(),
    }
  }

  fn names(&mut self) -> &mut HashMap<Rc<str>, Symbol> {
    match self {
      Scope::Root { names, .. } => names,
      Scope::Child { names, .. } => names,
    }
  }

  fn get(&self, name: &str) -> Option<Symbol> {
    match self {
      Scope::Root { names, .. } => names.get(name).cloned(),
      Scope::Child { names, parent } => match names.get(name) {
        Some(n) => Some(*n),
        None => parent.get(name),
      },
    }
  }

  fn child<'n>(&'n mut self) -> Scope<'n, 'store> {
    Scope::Child {
      parent: self,
      names: HashMap::new(),
    }
  }
}

#[derive(Debug)]
pub(crate) struct Binder<'store, 'parent: 'store> {
  scope: Scope<'store, 'parent>,
}

impl<'store, 'parent: 'store> Binder<'store, 'parent> {
  fn store(&mut self) -> &mut BinderStore {
    self.scope.store()
  }

  fn names(&mut self) -> &mut HashMap<Rc<str>, Symbol> {
    self.scope.names()
  }

  // Todo: deal with symbol reuse
  pub(crate) fn define(&mut self, name: impl Into<Rc<str>>) -> Symbol {
    let name = name.into();
    let symbol = self.store().insert(name.clone());
    self.names().insert(name, symbol);

    symbol
  }

  pub(crate) fn get(&self, name: &str) -> Option<Symbol> {
    self.scope.get(name.into())
  }

  pub(crate) fn child<'c>(&'c mut self) -> Binder<'c, 'store> {
    Binder {
      scope: self.scope.child(),
    }
  }
}
