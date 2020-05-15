pub(crate) mod binder;

pub use crate::ast::core::{BinaryOperatorKind, ObjectFieldOperatorKind, UnaryOperatorKind};
pub use binder::BindingId;

use crate::{
  core::binder::Binding,
  lex::span::Span,
  utils::{
    arena::{Arena, Id, SliceId},
    intern::{StringId, StringInterner},
  },
};
use derive_more::From;

pub struct Context {
  exprs: Arena<Core>,
  fields: Arena<CoreObjectField>,
  named_args: Arena<CoreNamedArgument>,
  bindings: Arena<CoreBinding>,
  strings: StringInterner,
}

macro_rules! impl_as_ref_arena {
  ($ty:ident, $fld:ident, $item:ident) => {
    impl AsRef<Arena<$item>> for $ty {
      #[inline]
      fn as_ref(&self) -> &Arena<$item> {
        &self.$fld
      }
    }
  };
}

impl_as_ref_arena!(Context, exprs, Core);
impl_as_ref_arena!(Context, fields, CoreObjectField);
impl_as_ref_arena!(Context, named_args, CoreNamedArgument);
impl_as_ref_arena!(Context, bindings, CoreBinding);

macro_rules! define_core_ast_struct {
  (@methods $(,)*) => {};

  (@methods $(#[$($m:tt)*])* $name:ident: StringId, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name<'a, 'ctx: 'a>(&'a self, context: &'ctx Context) -> &'ctx str {
      &context.strings.lookup(self.$name)
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: SliceId<$ty:ident>, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name<'a, 'ctx: 'a>(&'a self, context: &'ctx Context) -> &'ctx [$ty] {
      self.$name.get(AsRef::<Arena<$ty>>::as_ref(context))
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: Id<$ty:ident>, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name<'a, 'ctx: 'a>(&'a self, context: &'ctx Context) -> &'ctx $ty {
      self.$name.get(AsRef::<Arena<$ty>>::as_ref(context))
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: Binding, $($rest:tt)*) => {
    paste::item! {
      $(#[$($m)*])*
      pub fn [<$name _id>](&self) -> BindingId {
        self.$name.id()
      }
    }

    paste::item! {
      $(#[$($m)*])*
      pub fn $name<'a, 'ctx: 'a>(&'a self, context: &'ctx Context) -> &'ctx str {
        &context.strings.lookup(self.$name.name())
      }
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: f64, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name(&self) -> f64 {
      self.$name
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: BinaryOperatorKind, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name(&self) -> BinaryOperatorKind {
      self.$name
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: UnaryOperatorKind, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name(&self) -> UnaryOperatorKind {
      self.$name
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (@methods $(#[$($m:tt)*])* $name:ident: ObjectFieldOperatorKind, $($rest:tt)*) => {
    $(#[$($m)*])*
    pub fn $name(&self) -> ObjectFieldOperatorKind {
      self.$name
    }

    define_core_ast_struct! {
      @methods $($rest)*
    }
  };

  (
    $(#[$($m:tt)*])*
    pub struct $name:ident {
      $($body:tt)*
    }
  ) => {
    $(#[$($m)*])*
    #[derive(Clone, Copy)]
    pub struct $name {
      span: Span,
      $($body)*
    }

    impl $name {
      /// Get expression span.
      pub fn span(&self) -> Span {
        self.span
      }

      define_core_ast_struct! {
        @methods $($body)*
      }
    }
  };
}

macro_rules! define_core_ast {
  (@fin ($enum_name:ident) [$([$($m:tt)*] $ty:ident($inner:ident),)*]) => {
    #[derive(Clone, Copy, From)]
    pub enum $enum_name {
      $(
        $($m)*
        $ty($inner),
      )*
    }

    $(
      impl ::core::convert::TryFrom<$enum_name> for $inner {
        type Error = $enum_name;

        #[inline]
        fn try_from(value: $enum_name) -> ::core::result::Result<Self, Self::Error> {
          match value {
            $enum_name::$ty(v) => ::core::result::Result::Ok(v),
            v => ::core::result::Result::Err(v),
          }
        }
      }
    )*
  };

  (
    @item $ctx:tt $acc:tt {
      [$($m:tt)*]
      pub struct $name:ident {
        $($body:tt)*
      }
    } $rest:tt
  ) => {
    define_core_ast_struct! {
      $($m)*
      pub struct $name {
        $($body)*
      }
    }

    define_core_ast! {
      @next $ctx $acc $rest
    }
  };

  (
    @next $ctx:tt $acc:tt {}
  ) => {
    define_core_ast! {
      @fin $ctx $acc
    }
  };

  (
    @next $ctx:tt [$($ty:tt)*] {
      $(#[$($m:tt)*])*
      $name:ident($struct_name:ident) {
        $($body:tt)*
      }

      $($rest:tt)*
    }
  ) => {
    define_core_ast! {
      @item $ctx [$($ty)* [$(#[$($m)*])*] $name($struct_name),] {
        [$(#[$($m)*])*]
        pub struct $struct_name {
          $($body)*
        }
      } {
        $($rest)*
      }
    }
  };

  (
    @next $ctx:tt [$($ty:tt)*] {
      $(#[$($m:tt)*])*
      $name:ident($struct_name:ident),

      $($rest:tt)*
    }
  ) => {
    define_core_ast! {
      @item $ctx [$($ty)* [$(#[$($m)*])*] $name($struct_name),] {
        [$(#[$($m)*])*]
        pub struct $struct_name {}
      } {
        $($rest)*
      }
    }
  };

  (
    $(#[$($m:tt)*])*
    pub enum $enum_name:ident {
      $($case:tt)*
    }
  ) => {
    define_core_ast! {
      @next ($enum_name) [] {
        $($case)*
      }
    }
  };
}

define_core_ast_struct! {
  /// Core object field.
  pub struct CoreObjectField {
    /// Field name.
    field: Id<Core>,

    /// Field value.
    value: Id<Core>,

    /// Field kind.
    kind: ObjectFieldOperatorKind,
  }
}

define_core_ast_struct! {
  /// Core named argument.
  pub struct CoreNamedArgument {
    /// Argument name.
    name: StringId,

    /// Argument value.
    value: Id<Core>,
  }
}

define_core_ast_struct! {
  /// Core binding.
  pub struct CoreBinding {
    /// Get binding.
    binding: Binding,

    /// Get value.
    value: Id<Core>,
  }
}

define_core_ast! {
  pub enum Core {
    /// Constant `null`.
    Null(CoreNull),

    /// Constant `true`.
    True(CoreTrue),

    /// Constant `false`.
    False(CoreFalse),

    // /// Constant `self`.
    // SelfValue(CoreSelf),

    // /// Constant `super`.
    // Super(CoreSuper),

    /// String expression.
    String(CoreString) {
      /// Get string value.
      value: StringId,
    }

    /// Number expression.
    Number(CoreNumber) {
      /// Get number value.
      value: f64,
    }

    /// Object expression.
    Object(CoreObject) {
      /// Get asserts in object.
      asserts: SliceId<Core>,

      /// Get object fields.
      fields: SliceId<CoreObjectField>,
    }

    /// Object comprehension expression.
    ObjectComp(CoreObjectComp) {
      /// Get field name expression.
      field: Id<Core>,

      /// Get value expression.
      value: Id<Core>,

      /// Get binding for identifier used in comprehension.
      binding: Binding,

      /// Get array expression.
      list: Id<Core>,
    }

    /// Array expression.
    Array(CoreArray) {
      /// Get array items.
      items: SliceId<Core>,
    }

    /// Member access expression.
    MemberAccess(CoreMemberAccess) {
      /// Get member target.
      target: Id<Core>,

      /// Get member expression.
      member: Id<Core>,
    }

    /// Apply expression.
    Apply(CoreApply) {
      /// Get apply target.
      target: Id<Core>,

      /// Get positional arguments.
      positional: SliceId<Core>,

      /// Get named arguments.
      named: SliceId<CoreNamedArgument>,
    }

    /// Identifier expression.
    Ident(CoreIdent) {
      /// Get identifier binding.
      binding: Binding,
    }

    /// Local expression (variable bindings).
    Local(CoreLocal) {
      /// Get bindings.
      bindings: SliceId<CoreBinding>,

      /// Get expression.
      expr: Id<Core>,
    }

    /// If expression.
    If(CoreIf) {
      /// Get condition.
      cond: Id<Core>,

      /// Get true branch.
      if_true: Id<Core>,

      /// Get false branch.
      if_false: Id<Core>,
    }

    /// Binary operator expression.
    Binary(CoreBinary) {
      /// Get left side of operator.
      lhs: Id<Core>,

      /// Get right side of operator.
      rhs: Id<Core>,

      /// Get operator.
      op: BinaryOperatorKind,
    }

    /// Unary operator expression.
    Unary(CoreUnary) {
      /// Get expression.
      expr: Id<Core>,

      /// Get operator.
      op: UnaryOperatorKind,
    }

    /// Function expression.
    Function(CoreFunction) {
      /// Get function parameters.
      params: SliceId<CoreBinding>,

      /// Get function body.
      body: Id<Core>,
    }

    /// Error expression.
    Error(CoreError) {
      /// Error expression.
      expr: Id<Core>,
    }

    /// Import expression.
    Import(CoreImport) {
      /// File path.
      path: StringId,
    }

    /// Import string expression.
    ImportStr(CoreImportStr) {
      /// File path.
      path: StringId,
    }
  }
}

/// Bind a parsed ast and produce an expression in the core language.
pub fn bind(ast: crate::ast::full::Expr) -> Result<(Core, Context), crate::parse::error::Error> {
  use crate::ast::core::Allocator;

  let mut allocator = Allocator::new();
  let core_ast = crate::ast::core::from_ast(&mut allocator, ast);

  let mut strings = StringInterner::new();
  core::mem::swap(&mut strings, &mut allocator.strings);
  let mut ctx = Context {
    exprs: Arena::with_capacity(allocator.exprs.len()),
    fields: Arena::with_capacity(allocator.fields.len()),
    named_args: Arena::with_capacity(allocator.named_args.len()),
    bindings: Arena::with_capacity(allocator.binds.len()),
    strings,
  };

  let result = binder::bind(&mut ctx, core_ast, &allocator)?;
  todo!()
  //Ok((result, ctx))
}
