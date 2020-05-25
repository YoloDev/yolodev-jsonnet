//! ToTokens implementation for CoreExpr and children.
//!
//! This is primarily intended to compile the representation
//! of stdlib into a rust binary (so it doesn't have to be
//! parsed and processed every time), but the trait is public
//! meaning that it could be done with other libraries as well.
//!
//! However, due to this being intended to save space (and cpu
//! cycles), positional information (line-numbers and simliar)
//! is thrown away.
//!
//! It's recomended to put the output from this ToTokens in it's
//! own module, as it generates a bunch of small functions (to avoid
//! generating one big one).

use crate::*;
use alloc::collections::BTreeMap;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};

impl ToTokens for CoreExpr {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let mut context = Context {
      next_id: 0,
      fns: Vec::new(),
      cached: BTreeMap::new(),
      idents: BTreeMap::new(),
    };

    let end = self.gen_code(&mut context);

    let fns = context.fns;
    tokens.extend(quote! {{
      #[allow(non_snake_case)]
      mod token_fns {
        use ::jsonnet_core_lang::*;

        #(#fns)*
      }

      token_fns::#end
    }})
  }
}

#[derive(PartialEq, Eq, Hash, Ord, PartialOrd)]
enum Symbol {
  LiteralNull,
  LiteralBool(bool),
  LiteralString(String),
  LiteralNumber(String),
  SelfExpr,
  SuperExpr,
  Ident(u32),
  MemberAccess(u32, String),
}

impl Symbol {
  fn get_name(&self, ctx: &Context) -> Option<String> {
    let name = match self {
      Symbol::LiteralNull => "null".into(),
      Symbol::LiteralBool(true) => "true".into(),
      Symbol::LiteralBool(false) => "false".into(),
      Symbol::LiteralString(_) => return None,
      Symbol::LiteralNumber(n) => format!("number_{}", n).replace('.', "_"),
      Symbol::SelfExpr => "self".into(),
      Symbol::SuperExpr => "super".into(),
      Symbol::Ident(n) => {
        return ctx
          .idents
          .get(n)
          .map(|id| format!("ident_{}_{}", id.replace("$", "genid_"), n))
      }
      Symbol::MemberAccess(n, mem) => {
        return ctx
          .idents
          .get(n)
          .map(|id| format!("member_{}_{}_{}", id.replace("$", "genid_"), n, mem))
      }
    };

    Some(name)
  }
}

struct Context {
  next_id: u32,
  fns: Vec<TokenStream>,
  cached: BTreeMap<Symbol, Ident>,
  idents: BTreeMap<u32, String>,
}

impl Context {
  fn next(&mut self) -> u32 {
    let current = self.next_id;
    self.next_id += 1;
    current
  }
}

trait CodeGen {
  fn get_type_name() -> TokenStream;
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream;

  fn gen_code(&self, ctx: &mut Context) -> TokenStream {
    self.get_token_stream(ctx)
  }

  fn symbol(&self, _: &mut Context) -> Option<Symbol> {
    None
  }
}

impl CodeGen for CoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { CoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    match self {
      CoreExpr::Literal(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Literal(#it) }
      }
      CoreExpr::SelfValue(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::SelfValue(#it) }
      }
      CoreExpr::Super(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Super(#it) }
      }
      CoreExpr::Object(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Object(#it) }
      }
      CoreExpr::ObjectComp(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::ObjectComp(#it) }
      }
      CoreExpr::Array(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Array(#it) }
      }
      CoreExpr::MemberAccess(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::MemberAccess(#it) }
      }
      CoreExpr::Ident(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Ident(#it) }
      }
      CoreExpr::Local(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Local(#it) }
      }
      CoreExpr::If(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::If(#it) }
      }
      CoreExpr::Binary(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Binary(#it) }
      }
      CoreExpr::Unary(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Unary(#it) }
      }
      CoreExpr::Function(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Function(#it) }
      }
      CoreExpr::Apply(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Apply(#it) }
      }
      CoreExpr::Error(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Error(#it) }
      }
      CoreExpr::Import(it) => {
        let it = it.gen_code(ctx);
        quote! { CoreExpr::Import(#it) }
      }
    }
  }

  fn symbol(&self, ctx: &mut Context) -> Option<Symbol> {
    match self {
      CoreExpr::Literal(it) => it.symbol(ctx),
      CoreExpr::SelfValue(it) => it.symbol(ctx),
      CoreExpr::Super(it) => it.symbol(ctx),
      CoreExpr::Object(it) => it.symbol(ctx),
      CoreExpr::ObjectComp(it) => it.symbol(ctx),
      CoreExpr::Array(it) => it.symbol(ctx),
      CoreExpr::MemberAccess(it) => it.symbol(ctx),
      CoreExpr::Ident(it) => it.symbol(ctx),
      CoreExpr::Local(it) => it.symbol(ctx),
      CoreExpr::If(it) => it.symbol(ctx),
      CoreExpr::Binary(it) => it.symbol(ctx),
      CoreExpr::Unary(it) => it.symbol(ctx),
      CoreExpr::Function(it) => it.symbol(ctx),
      CoreExpr::Apply(it) => it.symbol(ctx),
      CoreExpr::Error(it) => it.symbol(ctx),
      CoreExpr::Import(it) => it.symbol(ctx),
    }
  }

  fn gen_code(&self, ctx: &mut Context) -> TokenStream {
    if let Some(sym) = self.symbol(ctx) {
      match ctx.cached.get(&sym) {
        Some(id) => quote! { #id() },
        None => {
          let num = ctx.next();
          let fn_name_str = sym
            .get_name(ctx)
            .map(|n| format!("get_{}", n))
            .unwrap_or_else(|| format!("get_{:0width$}", num, width = 6));
          let fn_name = format_ident!("{}", fn_name_str);
          let ret = Self::get_type_name();
          let body = self.get_token_stream(ctx);

          ctx.fns.push(quote! {
            pub(super) fn #fn_name() -> #ret {
              #body
            }
          });

          let ret = quote! { #fn_name() };
          ctx.cached.insert(sym, fn_name);
          ret
        }
      }
    } else {
      let fn_name_str = format!("get_{:0width$}", ctx.next(), width = 6);
      let fn_name = format_ident!("{}", fn_name_str);
      let ret = Self::get_type_name();
      let body = self.get_token_stream(ctx);

      ctx.fns.push(quote! {
        pub(super) fn #fn_name() -> #ret {
          #body
        }
      });

      quote! { #fn_name() }
    }
  }
}

impl CodeGen for LiteralCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { LiteralCoreExpr }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    match self.value() {
      CoreLiteral::Null => quote! { LiteralCoreExpr::new_null() },
      CoreLiteral::Bool(true) => quote! { LiteralCoreExpr::new_true() },
      CoreLiteral::Bool(false) => quote! { LiteralCoreExpr::new_false() },
      CoreLiteral::String(it) => quote! { LiteralCoreExpr::new_str(#it) },
      CoreLiteral::Number(it) => quote! { LiteralCoreExpr::new_number(#it) },
    }
  }

  fn symbol(&self, _: &mut Context) -> Option<Symbol> {
    match self.value() {
      CoreLiteral::Null => Some(Symbol::LiteralNull),
      CoreLiteral::Bool(b) => Some(Symbol::LiteralBool(b)),
      CoreLiteral::String(s) => Some(Symbol::LiteralString(s.into())),
      CoreLiteral::Number(f) => {
        let mut buf = [b'\0'; 20];
        let len = dtoa::write(&mut buf[..], f).unwrap();
        let s = core::str::from_utf8(&buf[..len]).unwrap();
        let s = String::from(s);

        Some(Symbol::LiteralNumber(s))
      }
    }
  }
}

impl CodeGen for SelfCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { SelfCoreExpr }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    quote! { SelfCoreExpr::new() }
  }

  fn symbol(&self, _: &mut Context) -> Option<Symbol> {
    Some(Symbol::SelfExpr)
  }
}

impl CodeGen for SuperCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { SuperCoreExpr }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    quote! { SuperCoreExpr::new() }
  }

  fn symbol(&self, _: &mut Context) -> Option<Symbol> {
    Some(Symbol::SuperExpr)
  }
}

impl CodeGen for CoreIdent {
  fn get_type_name() -> TokenStream {
    quote! { CoreIdent }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    let name = self.name.as_str();
    let id = self.id.unwrap().get();

    quote! { unsafe { CoreIdent::new_unchecked(#name, #id) } }
  }
}

impl CodeGen for IdentCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { IdentCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let ident = self.ident.gen_code(ctx);

    quote! { IdentCoreExpr::new(#ident) }
  }

  fn symbol(&self, ctx: &mut Context) -> Option<Symbol> {
    self.ident.id.map(|id| {
      ctx
        .idents
        .entry(id.get())
        .or_insert_with(|| self.ident.name.to_string());

      Symbol::Ident(id.get())
    })
  }
}

impl CodeGen for CoreLocalBind {
  fn get_type_name() -> TokenStream {
    quote! { CoreLocalBind }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let ident = self.ident.gen_code(ctx);
    let value = self.value.gen_code(ctx);

    quote! { CoreLocalBind::new(#ident, #value) }
  }
}

impl CodeGen for LocalCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { LocalCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let binds = self.binds.gen_code(ctx);
    let rest = self.rest.gen_code(ctx);

    quote! {
      LocalCoreExpr::new(
        #binds,
        #rest
      )
    }
  }
}

impl CodeGen for ErrorCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ErrorCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let expr = self.expr.gen_code(ctx);

    quote! { ErrorCoreExpr::new(#expr) }
  }
}

impl CodeGen for ImportCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ImportCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let file = self.file.as_str();
    let kind = self.kind.gen_code(ctx);

    quote! { ImportCoreExpr::new(#file, #kind) }
  }
}

impl CodeGen for CoreImportKind {
  fn get_type_name() -> TokenStream {
    quote! { CoreImportKind }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    match self {
      CoreImportKind::Jsonnet => quote! { CoreImportKind::Jsonnet },
      CoreImportKind::String => quote! { CoreImportKind::String },
    }
  }
}

impl CodeGen for UnaryCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { UnaryCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let op = self.op.gen_code(ctx);
    let expr = self.expr.gen_code(ctx);

    quote! { UnaryCoreExpr::new(#op, #expr) }
  }
}

impl CodeGen for CoreUnaryOperator {
  fn get_type_name() -> TokenStream {
    quote! { CoreUnaryOperator }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    match self {
      CoreUnaryOperator::Plus(_) => quote! { CoreUnaryOperator::Plus(None) },
      CoreUnaryOperator::Minus(_) => quote! { CoreUnaryOperator::Minus(None) },
      CoreUnaryOperator::Not(_) => quote! { CoreUnaryOperator::Not(None) },
      CoreUnaryOperator::BitNeg(_) => quote! { CoreUnaryOperator::BitNeg(None) },
    }
  }
}

impl CodeGen for BinaryCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { BinaryCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let lhs = self.lhs.gen_code(ctx);
    let op = self.op.gen_code(ctx);
    let rhs = self.rhs.gen_code(ctx);

    quote! { BinaryCoreExpr::new(#lhs, #op, #rhs) }
  }
}

impl CodeGen for CoreBinaryOperator {
  fn get_type_name() -> TokenStream {
    quote! { CoreBinaryOperator }
  }

  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    match self {
      CoreBinaryOperator::Mult(_) => quote! { CoreBinaryOperator::Mult(None) },
      CoreBinaryOperator::Div(_) => quote! { CoreBinaryOperator::Div(None) },
      CoreBinaryOperator::Plus(_) => quote! { CoreBinaryOperator::Plus(None) },
      CoreBinaryOperator::Minus(_) => quote! { CoreBinaryOperator::Minus(None) },
      CoreBinaryOperator::ShiftL(_) => quote! { CoreBinaryOperator::ShiftL(None) },
      CoreBinaryOperator::ShiftR(_) => quote! { CoreBinaryOperator::ShiftR(None) },
      CoreBinaryOperator::GreaterThan(_) => quote! { CoreBinaryOperator::GreaterThan(None) },
      CoreBinaryOperator::GreaterThanOrEquals(_) => {
        quote! { CoreBinaryOperator::GreaterThanOrEquals(None) }
      }
      CoreBinaryOperator::LessThan(_) => quote! { CoreBinaryOperator::LessThan(None) },
      CoreBinaryOperator::LessThanOrEquals(_) => {
        quote! { CoreBinaryOperator::LessThanOrEquals(None) }
      }
      CoreBinaryOperator::BitAnd(_) => quote! { CoreBinaryOperator::BitAnd(None) },
      CoreBinaryOperator::BitXor(_) => quote! { CoreBinaryOperator::BitXor(None) },
      CoreBinaryOperator::BitOr(_) => quote! { CoreBinaryOperator::BitOr(None) },
      CoreBinaryOperator::And(_) => quote! { CoreBinaryOperator::And(None) },
      CoreBinaryOperator::Or(_) => quote! { CoreBinaryOperator::Or(None) },
    }
  }
}

impl CodeGen for IfCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { IfCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let cond = self.cond.gen_code(ctx);
    let if_true = self.if_true.gen_code(ctx);
    let if_false = self.if_false.gen_code(ctx);

    quote! { IfCoreExpr::new(#cond, #if_true, #if_false) }
  }
}

impl CodeGen for ArrayCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ArrayCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let items = self.items.gen_code(ctx);

    quote! { ArrayCoreExpr::new(#items) }
  }
}

impl CodeGen for ObjectCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ObjectCoreExpr }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let asserts = self.asserts.gen_code(ctx);
    let fields = self.fields.gen_code(ctx);

    quote! {
      ObjectCoreExpr::new(
        #asserts,
        #fields,
      )
    }
  }
}

impl CodeGen for CoreObjectField {
  fn get_type_name() -> TokenStream {
    quote! { CoreObjectField }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let name = self.name.gen_code(ctx);
    let op = self.op.gen_code(ctx);
    let value = self.value.gen_code(ctx);

    quote! { CoreObjectField::new(#name, #op, #value) }
  }
}

impl CodeGen for CoreObjectFieldOperator {
  fn get_type_name() -> TokenStream {
    quote! { CoreObjectFieldOperator }
  }
  fn get_token_stream(&self, _: &mut Context) -> TokenStream {
    match self {
      CoreObjectFieldOperator::Default(_) => quote! { CoreObjectFieldOperator::Default(None) },
      CoreObjectFieldOperator::Hidden(_) => quote! { CoreObjectFieldOperator::Hidden(None) },
      CoreObjectFieldOperator::Visible(_) => quote! { CoreObjectFieldOperator::Visible(None) },
      CoreObjectFieldOperator::MergeDefault(_) => {
        quote! { CoreObjectFieldOperator::MergeDefault(None) }
      }
      CoreObjectFieldOperator::MergeHidden(_) => {
        quote! { CoreObjectFieldOperator::MergeHidden(None) }
      }
      CoreObjectFieldOperator::MergeVisible(_) => {
        quote! { CoreObjectFieldOperator::MergeVisible(None) }
      }
    }
  }
}

impl CodeGen for MemberAccessCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { MemberAccessCoreExpr }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let target = self.target.gen_code(ctx);
    let field_name = self.field_name.gen_code(ctx);

    quote! { MemberAccessCoreExpr::new(#target, #field_name) }
  }
  fn symbol(&self, ctx: &mut Context) -> Option<Symbol> {
    let target = self.target.symbol(ctx)?;
    let field_name = self.field_name.symbol(ctx)?;

    match (&target, &field_name) {
      (Symbol::Ident(target), Symbol::LiteralString(field_name)) => {
        Some(Symbol::MemberAccess(*target, field_name.clone()))
      }
      _ => None,
    }
  }
}

impl CodeGen for ObjectCompCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ObjectCompCoreExpr }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let field_name = self.field_name.gen_code(ctx);
    let field_value = self.field_value.gen_code(ctx);
    let loop_var_ident = self.loop_var_ident.gen_code(ctx);
    let list = self.list.gen_code(ctx);

    quote! {
      ObjectCompCoreExpr::new(#field_name, #field_value, #loop_var_ident, #list)
    }
  }
}

impl CodeGen for FunctionCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { FunctionCoreExpr }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let params = self.params.gen_code(ctx);
    let expr = self.expr.gen_code(ctx);

    quote! { FunctionCoreExpr::new(#params, #expr) }
  }
}

impl CodeGen for CoreFunctionParam {
  fn get_type_name() -> TokenStream {
    quote! { CoreFunctionParam }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let name = self.name.gen_code(ctx);
    let default_value = self.default_value.gen_code(ctx);

    quote! { CoreFunctionParam::new(#name, #default_value) }
  }
}

impl CodeGen for ApplyCoreExpr {
  fn get_type_name() -> TokenStream {
    quote! { ApplyCoreExpr }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let target = self.target.gen_code(ctx);
    let positionals = self.positionals.gen_code(ctx);
    let named = self.named.gen_code(ctx);
    let is_tailstrict = self.is_tailstrict;

    quote! {
      ApplyCoreExpr::new(
        #target,
        #positionals,
        #named,
        #is_tailstrict
      )
    }
  }
}

impl CodeGen for CoreNamedArg {
  fn get_type_name() -> TokenStream {
    quote! { CoreNamedArg }
  }
  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let name = self.name.as_str();
    let value = self.value.gen_code(ctx);

    quote! { CoreNamedArg::new(#name, #value) }
  }
}

impl<T: CodeGen> CodeGen for Vec<T> {
  fn get_type_name() -> TokenStream {
    let inner = T::get_type_name();

    quote! { Vec<#inner> }
  }

  fn get_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let items = self.iter().map(|item| item.gen_code(ctx));

    quote! { vec![#(#items,)*] }
  }
}
