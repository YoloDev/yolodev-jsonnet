use gc::{Gc, GcCell, Trace};

#[derive(Trace)]
struct ExpressionCell<T: Trace + 'static>(GcCell<Gc<dyn Expression<T>>>);

impl<T: Trace + 'static> ExpressionCell<T> {
  fn new(expr: impl Expression<T> + 'static) -> ExpressionCell<T> {
    ExpressionCell(GcCell::new(Gc::new(expr)))
  }

  fn eval(&self) -> Gc<T> {
    let expr = self.0.borrow().clone();

    expr.eval(self)
  }

  fn update(&self, value: Gc<T>) -> Gc<T> {
    *self.0.borrow_mut() = Gc::new(ConstExpr(value.clone()));
    value
  }
}

trait Expression<T: Trace + 'static>: Trace {
  fn eval(&self, cell: &ExpressionCell<T>) -> Gc<T>;
}

#[derive(Trace)]
struct ConstExpr<R: Trace + 'static>(Gc<R>);

impl<T: Trace + 'static> Expression<T> for ConstExpr<T> {
  #[inline]
  fn eval(&self, _: &ExpressionCell<T>) -> Gc<T> {
    dbg!("const eval");
    self.0.clone()
  }
}

#[derive(Trace)]
struct AddExpr(usize, usize);

impl Expression<usize> for AddExpr {
  fn eval(&self, cell: &ExpressionCell<usize>) -> Gc<usize> {
    dbg!("eval addexpr");
    let result = self.0 + self.1;
    cell.update(Gc::new(result))
  }
}

#[test]
fn test() {
  dbg!("ehlo");
  let expr = AddExpr(2, 5);
  let cell = ExpressionCell::new(expr);
  let result = cell.eval();
  assert_eq!(*result, 7);
  let result = cell.eval();
  assert_eq!(*result, 7);
}
