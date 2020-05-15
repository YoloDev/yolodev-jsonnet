#![feature(never_type)]
#![feature(const_fn)]
#![feature(trace_macros)]
#![feature(ptr_offset_from)]
#![feature(new_uninit)]
#![feature(maybe_uninit_slice)]
#![feature(associated_type_defaults)]
#![feature(type_alias_impl_trait)]
#![cfg_attr(test, feature(option_expect_none, box_patterns))]

extern crate alloc;

macro_rules! define_error {
  (
    @impl
    $(#[$($m:tt)*])+
    $vis:vis struct $name:ident {
      $(
        $(#[$($field_meta:tt)*])*
        $field:ident: $field_ty:ty,
      )*
    }
  ) => {
    $(#[$($m)*])+
    #[derive(Clone, Debug, displaydoc::Display, derive_new::new)]
    $vis struct $name {
      $(
        $(#[$($field_meta)*])*
        $field: $field_ty,
      )*
    }

    impl crate::lex::token::private::Sealed for $name {}
    impl crate::lex::token::Spanned for $name {
      #[inline]
      fn span(&self) -> Span {
        self.span
      }
    }

    impl crate::parse::error::Diagnostic for $name {
      fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Display::fmt(self, f)
      }
    }
  };

  (
    $(#[$($m:tt)*])+
    $vis:vis struct $name:ident {
      $(
        $(#[$($field_meta:tt)*])*
        $field:ident: $field_ty:ty,
      )*
    }
  ) => {
    define_error! {
      @impl
      $(#[$($m)*])+
      $vis struct $name {
        /// Error span
        span: Span,
        $(
          $(#[$($field_meta)*])*
          $field: $field_ty,
        )*
      }
    }
  };

  (
    $(#[$($m:tt)*])+
    $vis:vis struct $name:ident;
  ) => {
    define_error! {
      @impl
      $(#[$($m)*])+
      $vis struct $name {
        /// Error span
        span: Span,
      }
    }
  };
}

pub(crate) mod ast;
pub(crate) mod core;
pub(crate) mod lex;
pub(crate) mod parse;
pub(crate) mod utils;
