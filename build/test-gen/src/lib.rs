use glob::glob;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use std::path::Path;
use syn::{
  parse::{Parse, ParseStream, Result as ParseResult},
  parse_macro_input, Ident, ItemFn, LitStr,
};

// Form canonical name without any punctuation/delimiter or special character
fn canonical_fn_name(s: &str) -> String {
  // remove delimiters and special characters
  s.replace(
    &['"', ' ', '.', ':', '-', '*', '/', '\\', '\n', '\t', '\r'][..],
    "_",
  )
  .replace('\u{FFFD}', "")
}

fn gen_test_name(ident: &Ident, path: &Path) -> Ident {
  let name_part_from_path = canonical_fn_name(&path.to_string_lossy());
  let mut name = ident.to_string();
  name.reserve(name_part_from_path.len() + 1);
  name.push('_');
  name.push_str(&name_part_from_path);

  Ident::new(&name, Span::call_site())
}

/// MacroAttributes elements
struct MacroAttributes {
  glob_pattern: LitStr,
}

// MacroAttributes parser
impl Parse for MacroAttributes {
  fn parse(input: ParseStream) -> ParseResult<Self> {
    let glob_pattern: LitStr = input.parse()?;
    if !input.is_empty() {
      return Err(input.error("found multiple parameters, expected one"));
    }

    Ok(MacroAttributes { glob_pattern })
  }
}

fn generate_test_case(
  input: &Path,
  output: &Path,
  fn_name: &Ident,
  test_name: Ident,
) -> TokenStream2 {
  let input = match input.to_str() {
    None => {
      return syn::Error::new(
        Span::call_site(),
        &format!("failed to process path: {:?}", input.display()),
      )
      .to_compile_error()
    }
    Some(p) => p,
  };

  let output = match output.to_str() {
    None => {
      return syn::Error::new(
        Span::call_site(),
        &format!("failed to process path: {:?}", output.display()),
      )
      .to_compile_error()
    }
    Some(p) => p,
  };

  quote! {
    #[test]
    fn #test_name() {
      let input = ::core::include_str!(#input);
      let expected = ::core::include_str!(#output);

      let mut output: String = #fn_name(input, #input).into();
      output.push('\n');
      let output: &str = output.as_ref();
      assert_eq!(output, expected, "file: {}", #input);
    }
  }
}

fn generate_missing_golden(
  input: &Path,
  output: &Path,
  fn_name: &Ident,
  test_name: Ident,
) -> TokenStream2 {
  let input = match input.to_str() {
    None => {
      return syn::Error::new(
        Span::call_site(),
        &format!("failed to process path: {:?}", input.display()),
      )
      .to_compile_error()
    }
    Some(p) => p,
  };

  let output = match output.to_str() {
    None => {
      return syn::Error::new(
        Span::call_site(),
        &format!("failed to process path: {:?}", output.display()),
      )
      .to_compile_error()
    }
    Some(p) => p,
  };

  quote! {
    #[test]
    fn #test_name() {
      if ::core::option_env!("CI").is_some() {
        panic!("missing golden file for {} on CI. Expected file: {}", #input, #output);
      }

      let input = ::core::include_str!(#input);
      let mut output: String = #fn_name(input, #input).into();
      output.push('\n');
      let output: &str = output.as_ref();
      ::std::fs::write(#output, &output).expect("write golden");
    }
  }
}

fn generate_tests(glob_pattern: LitStr, fun: ItemFn) -> TokenStream2 {
  let ident = fun.sig.ident;

  let paths = match glob(&glob_pattern.value()) {
    Err(e) => {
      return syn::Error::new_spanned(&glob_pattern, format!("failed to fetch files: {}", e))
        .to_compile_error()
    }
    Ok(p) => p,
  };

  let tests = paths.map(|p| {
    let (input, test_name) = match p {
      Err(e) => {
        return syn::Error::new_spanned(&glob_pattern, format!("failed to fetch files: {}", e))
          .to_compile_error()
      }
      Ok(p) => match p.canonicalize() {
        Err(e) => {
          return syn::Error::new_spanned(
            &glob_pattern,
            format!("failed to canonicalize path '{:?}': {}", p.display(), e),
          )
          .to_compile_error()
        }
        Ok(input) => (input, gen_test_name(&ident, &p)),
      },
    };

    let golden = input.with_extension("golden");
    if golden.is_file() {
      generate_test_case(&input, &golden, &ident, test_name)
    } else {
      generate_missing_golden(&input, &golden, &ident, test_name)
    }
  });

  quote! {
    #(#tests)*
  }
}

#[proc_macro_attribute]
pub fn test_golden(attr: TokenStream, item: TokenStream) -> TokenStream {
  let item_clone: TokenStream2 = item.clone().into();

  let MacroAttributes { glob_pattern } = parse_macro_input!(attr as MacroAttributes);

  // TODO: Validate that func output is AsRef<str> somehow.
  let fun = parse_macro_input!(item as ItemFn);

  let tests = generate_tests(glob_pattern, fun);

  let result = quote! {
    #item_clone

    #tests
  };

  result.into()
}
