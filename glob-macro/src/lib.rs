use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use syn::Error;
use syn_mid::ItemFn;

#[proc_macro_attribute]
pub fn glob(args: TokenStream, function: TokenStream) -> TokenStream {
    if args.is_empty() {
        return Error::new(Span::call_site(), "#[glob] attribute requires an argument")
            .to_compile_error()
            .into();
    }

    let glob_path = match syn::parse(args) {
        Ok(p) => p,
        Err(err) => return err.to_compile_error().into(),
    };

    let function: ItemFn = syn::parse_macro_input!(function);

    if !function
        .attrs
        .iter()
        .any(|attr| attr.path().is_ident("test"))
    {
        return Error::new(
            Span::call_site(),
            "#[glob] attribute currently only supports running on #[test] functions",
        )
        .to_compile_error()
        .into();
    }

    glob2(glob_path, function).into()
}

fn glob2(glob_path: syn::LitStr, function: ItemFn) -> TokenStream2 {
    let paths = match glob::glob(&glob_path.value()) {
        Ok(paths) => paths,
        Err(err) => {
            return Error::new(
                glob_path.span(),
                format!("#[glob] called with invalid value: {err:?}"),
            )
            .to_compile_error();
        }
    };

    let paths = match paths.collect::<Result<Vec<_>, _>>() {
        Ok(p) => p,
        Err(err) => {
            return Error::new(glob_path.span(), format!("#[glob] error: {err:?}"))
                .to_compile_error();
        }
    };
    let counter_width = (paths.len() - 1).to_string().len();

    let common_ancestor = paths
        .iter()
        .fold(paths[0].clone(), |ancestor, path| {
            ancestor
                .components()
                .zip(path.components())
                .take_while(|(a, b)| a == b)
                .map(|(a, _)| a)
                .collect()
        })
        .components()
        .count();

    let mut functions = vec![];

    for (i, path) in paths.iter().enumerate() {
        let function_name = syn::Ident::new(
            &format!(
                "{}__{:0width$}__{}",
                function.sig.ident,
                i,
                path.components()
                    .skip(common_ancestor)
                    .map(|p| p.as_os_str().to_string_lossy())
                    .collect::<Vec<_>>()
                    .join("/")
                    .replace("/", "__")
                    .replace(".", "_")
                    .replace("-", "_")
                    .replace(" ", "_"),
                width = counter_width
            ),
            function.sig.ident.span(),
        );

        let path_buf = syn::LitStr::new(&path.to_string_lossy(), Span::call_site());

        let mut inner_function = function.clone();
        inner_function.sig.ident = syn::Ident::new("test", function.sig.ident.span());
        inner_function.attrs = inner_function
            .attrs
            .into_iter()
            .filter(|attr| !attr.path().is_ident("test"))
            .collect();

        let function = quote! {
            #[test]
            #[allow(non_snake_case)]
            fn #function_name() {
                #inner_function
                let path: &str = #path_buf;
                test(std::path::Path::new(&path));
            }
        };

        functions.push(function);
    }

    quote! {
        #(#functions)*
    }
}
