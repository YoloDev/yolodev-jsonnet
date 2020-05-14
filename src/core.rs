use crate::{
  ast::core,
  lex::span::Span,
  utils::{
    arena::{Arena, Id, SliceId},
    intern::{StringId, StringInterner},
  },
};
use alloc::rc::Rc;

struct Context {
  exprs: Arena<core::CoreExpr>,
  strings: StringInterner,
}

macro_rules! define_core_ast {
  (@fin [$($ty:ident,)*]) => {

  };

  (@method [$($m:tt)*] $name:ident StringId) => {
    $($m)*
    pub fn $name(&self) -> &str {
      &self.context.strings.lookup(self.$name)
    }
  };

  (@method [$($m:tt)*] $name:ident f64) => {
    $($m)*
    pub fn $name(&self) -> f64 {
      self.$name
    }
  };

  (
    @item ($enum_name:ident) $acc:tt {
      [$($m:tt)*]
      pub struct $name:ident {
        $(
          [$($fld_m:tt)*]
          $fld_name:ident: $fld_type:ty,
        )*
      }
    } $rest:tt
  ) => {
    paste::item! {
      $($m)*
      #[derive(Clone)]
      pub struct [<$enum_name $name>] {
        context: Rc<Context>,
        span: Span,

        $(
          $fld_name: $fld_type,
        )*
      }

      impl [<$enum_name $name>] {
        /// Get expression span.
        pub fn span(&self) -> Span {
          self.span
        }

        $(
          define_core_ast! {
            @method [$($fld_m)*] $fld_name $fld_type
          }
        )*
      }
    }

    define_core_ast! {
      @next ($enum_name) $acc $rest
    }
  };

  (
    @next $ctx:tt [$($ty:ident,)*] {}
  ) => {
    define_core_ast! {
      @fin [$($ty,)*]
    }
  };

  (
    @next $ctx:tt [$($ty:ident,)*] {
      $(#[$($m:tt)*])*
      $name:ident {
        $(
          $(#[$($fld_m:tt)*])*
          $fld_name:ident: $fld_value:ident,
        )*
      }

      $($rest:tt)*
    }
  ) => {
    define_core_ast! {
      @item $ctx [$($ty,)* $name,] {
        [$(#[$($m)*])*]
        pub struct $name {
          $(
            [$(#[$($fld_m)*])*]
            $fld_name: $fld_value,
          )*
        }
      } {
        $($rest)*
      }
    }
  };

  (
    @next $ctx:tt [$($ty:ident,)*] {
      $(#[$($m:tt)*])*
      $name:ident,

      $($rest:tt)*
    }
  ) => {
    define_core_ast! {
      @item $ctx [$($ty,)* $name,] {
        [$(#[$($m)*])*]
        pub struct $name {}
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

define_core_ast! {
  pub enum Core {
    /// Constant `null`.
    Null,

    /// Constant `true`.
    True,

    /// Constant `false`.
    False,

    /// Constant `self`.
    SelfValue,

    /// Constant `super`.
    Super,

    /// String expression.
    String {
      /// Get string value.
      value: StringId,
    }

    /// Number expression.
    Number {
      /// Get number value.
      value: f64,
    }

    /// Object expression.
    Object {

    }
  }
}
