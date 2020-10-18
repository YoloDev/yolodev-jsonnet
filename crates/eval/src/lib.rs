// use gc::{Finalize, Gc, GcCell, Trace};
// use jsonnet_core_lang as lang;
// use std::rc::Rc;

mod expr;
mod fun;
mod helpers;
mod lazy;
mod val;

pub use val::{StringValue, Value};

// pub enum ValueKind {
//   Null,
//   Bool,
//   String,
//   Number,
//   Object,
//   Array,
//   Function,
// }

// #[derive(Debug)]
// enum Value {
//   Null,
//   Bool(bool),
//   String(Rc<str>),
//   Double(f64),
//   Object(Object),
//   Array(Array),
//   Function(Function),
// }

// unsafe impl Trace for Value {
//   gc::custom_trace! {this, {
//     match this {
//       Value::Object(o) => mark(o),
//       Value::Array(a) => mark(a),
//       Value::Function(f) => mark(f),
//       _ => (),
//     }
//   }}
// }

// #[derive(Debug, Trace)]
// struct ObjectProperty {
//   name: GcValue,
//   value: GcValue,
// }

// #[derive(Debug, Trace)]
// struct Object {
//   properties: Vec<GcValue>,
// }

// #[derive(Debug, Trace)]
// struct Array {
//   items: Vec<GcValue>,
// }

// #[derive(Debug, Trace)]
// struct Function;

// #[derive(Debug, Trace)]
// enum LazyValue {
//   Lazy(Gc<dyn Expr>),
//   Realized(Gc<Value>),
// }

// impl LazyValue {
//   fn get(&mut self) -> &Value {
//     match self {
//       LazyValue::Realized(ref v) => &*v,
//       LazyValue::Lazy(ref e) => {
//         let value = Gc::new(e.eval());
//         *self = LazyValue::Realized(value);

//         if let LazyValue::Realized(v) = self {
//           &*v
//         } else {
//           unreachable!()
//         }
//       }
//     }
//   }
// }

// trait Expr: core::fmt::Debug + Trace + Finalize {
//   fn eval(&self) -> Value;
// }

// type GcValue = Gc<GcCell<LazyValue>>;

// #[derive(Debug, Trace, Finalize)]
// pub enum Value {}

// #[derive(Debug, Trace, Finalize)]
// pub enum Primitive {
//   Null,
//   Bool(bool),
//   String(String),
//   Double(f64),
// }

// #[derive(Debug, Trace, Finalize)]
// pub enum Value {
//   Primitive(Primitive),
//   Object(GcObject),
//   Function(Function),
//   Array(Vec<GcValue>),
// }

// #[derive(Debug, Trace, Finalize)]
// pub enum ValueRef {
//   Lazy(Expr),
//   Realized(Value),
// }

// #[derive(Debug, Trace, Finalize)]
// pub struct Function {
//   params: Vec<
// }

// #[derive(Debug, Trace, Finalize)]
// pub enum Object {
//   Lazy {
//     asserts: Vec<Expr>,
//     fields: Vec<(GcValue, GcValue)>,
//   },

//   Realized(Vec<(GcValue, GcValue)>),
// }

// #[derive(Debug, Trace, Finalize)]
// pub enum Expr {

// }

// type GcObject = GcCell<Object>;
// type GcValue = GcCell<ValueRef>;
