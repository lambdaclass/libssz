extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Meta};

/// Check if a type has `#[ssz(transparent)]` attribute.
fn is_transparent(input: &DeriveInput) -> bool {
    input.attrs.iter().any(|attr| {
        if let Meta::List(meta_list) = &attr.meta {
            if meta_list.path.is_ident("ssz") {
                let tokens = meta_list.tokens.to_string();
                return tokens.contains("transparent");
            }
        }
        false
    })
}

/// Check if an enum has `#[ssz(enum_behaviour = "union")]` attribute.
fn is_union_enum(input: &DeriveInput) -> bool {
    input.attrs.iter().any(|attr| {
        if let Meta::List(meta_list) = &attr.meta {
            if meta_list.path.is_ident("ssz") {
                let tokens = meta_list.tokens.to_string();
                return tokens.contains("enum_behaviour") && tokens.contains("union");
            }
        }
        false
    })
}

/// Get the single inner type from a transparent struct.
fn transparent_field_info(data: &syn::DataStruct) -> (proc_macro2::TokenStream, syn::Type) {
    match &data.fields {
        Fields::Unnamed(f) if f.unnamed.len() == 1 => {
            let ty = f.unnamed.first().unwrap().ty.clone();
            let idx = syn::Index::from(0);
            (quote! { self.#idx }, ty)
        }
        Fields::Named(f) if f.named.len() == 1 => {
            let field = f.named.first().unwrap();
            let field_name = field.ident.as_ref().unwrap();
            let ty = field.ty.clone();
            (quote! { self.#field_name }, ty)
        }
        _ => panic!("#[ssz(transparent)] requires exactly one field"),
    }
}

// ── SszEncode ──

#[proc_macro_derive(SszEncode, attributes(ssz))]
pub fn derive_ssz_encode(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if is_transparent(&input) {
                derive_encode_transparent(name, &impl_generics, &ty_generics, where_clause, data_struct)
            } else {
                derive_encode_struct(name, &impl_generics, &ty_generics, where_clause, data_struct)
            }
        }
        Data::Enum(data_enum) => {
            if is_union_enum(&input) {
                derive_encode_union_enum(name, &impl_generics, &ty_generics, where_clause, data_enum)
            } else {
                panic!("SszEncode for enums requires #[ssz(enum_behaviour = \"union\")]")
            }
        }
        Data::Union(_) => panic!("SszEncode cannot be derived for Rust unions"),
    };

    expanded.into()
}

fn derive_encode_transparent(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let (field_access, inner_ty) = transparent_field_info(data);

    quote! {
        impl #impl_generics ssz::SszEncode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                <#inner_ty as ssz::SszEncode>::is_fixed_size()
            }

            fn fixed_size() -> usize {
                <#inner_ty as ssz::SszEncode>::fixed_size()
            }

            fn encoded_len(&self) -> usize {
                ssz::SszEncode::encoded_len(&#field_access)
            }

            fn ssz_append(&self, buf: &mut Vec<u8>) {
                ssz::SszEncode::ssz_append(&#field_access, buf);
            }
        }
    }
}

fn derive_encode_struct(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let fields = match &data.fields {
        Fields::Named(f) => &f.named,
        _ => panic!("SszEncode can only be derived for structs with named fields"),
    };

    let field_names: Vec<_> = fields.iter().map(|f| f.ident.as_ref().unwrap()).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();

    // is_fixed_size: all fields must be fixed
    let is_fixed_checks = field_types.iter().map(|ty| {
        quote! { <#ty as ssz::SszEncode>::is_fixed_size() }
    });

    // fixed_size: sum of fixed sizes (only valid if is_fixed_size)
    let fixed_size_terms: Vec<_> = field_types.iter().map(|ty| {
        quote! { <#ty as ssz::SszEncode>::fixed_size() }
    }).collect();

    // encoded_len — wrap in braces so `+` separator works between if-exprs
    let encoded_len_terms: Vec<_> = field_names.iter().zip(field_types.iter()).map(|(fname, ty)| {
        quote! {
            {
                if <#ty as ssz::SszEncode>::is_fixed_size() {
                    <#ty as ssz::SszEncode>::fixed_size()
                } else {
                    4 + ssz::SszEncode::encoded_len(&self.#fname)
                }
            }
        }
    }).collect();

    // ssz_append: use ContainerEncoder
    let append_stmts: Vec<_> = field_names.iter().zip(field_types.iter()).map(|(fname, ty)| {
        quote! {
            if <#ty as ssz::SszEncode>::is_fixed_size() {
                encoder.append_fixed(&self.#fname);
            } else {
                encoder.append_variable(&self.#fname);
            };
        }
    }).collect();

    quote! {
        impl #impl_generics ssz::SszEncode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                true #(&& #is_fixed_checks)*
            }

            fn fixed_size() -> usize {
                if <Self as ssz::SszEncode>::is_fixed_size() {
                    0 #(+ #fixed_size_terms)*
                } else {
                    0
                }
            }

            fn encoded_len(&self) -> usize {
                0 #(+ #encoded_len_terms)*
            }

            fn ssz_append(&self, buf: &mut Vec<u8>) {
                let mut encoder = ssz::ContainerEncoder::new();
                #(#append_stmts)*
                encoder.finalize(buf);
            }
        }
    }
}

fn derive_encode_union_enum(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataEnum,
) -> proc_macro2::TokenStream {
    let variant_arms: Vec<_> = data.variants.iter().enumerate().map(|(i, variant)| {
        let variant_name = &variant.ident;
        let selector = i as u8;
        match &variant.fields {
            Fields::Unnamed(f) if f.unnamed.len() == 1 => {
                quote! {
                    #name::#variant_name(inner) => {
                        buf.push(#selector);
                        ssz::SszEncode::ssz_append(inner, buf);
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    #name::#variant_name => {
                        buf.push(#selector);
                    }
                }
            }
            _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
        }
    }).collect();

    let encoded_len_arms: Vec<_> = data.variants.iter().map(|variant| {
        let variant_name = &variant.ident;
        match &variant.fields {
            Fields::Unnamed(_f) => {
                quote! {
                    #name::#variant_name(inner) => 1 + ssz::SszEncode::encoded_len(inner)
                }
            }
            Fields::Unit => {
                quote! {
                    #name::#variant_name => 1
                }
            }
            _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
        }
    }).collect();

    quote! {
        impl #impl_generics ssz::SszEncode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool { false }
            fn fixed_size() -> usize { 0 }

            fn encoded_len(&self) -> usize {
                match self {
                    #(#encoded_len_arms,)*
                }
            }

            fn ssz_append(&self, buf: &mut Vec<u8>) {
                match self {
                    #(#variant_arms)*
                }
            }
        }
    }
}

// ── SszDecode ──

#[proc_macro_derive(SszDecode, attributes(ssz))]
pub fn derive_ssz_decode(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if is_transparent(&input) {
                derive_decode_transparent(name, &impl_generics, &ty_generics, where_clause, data_struct)
            } else {
                derive_decode_struct(name, &impl_generics, &ty_generics, where_clause, data_struct)
            }
        }
        Data::Enum(data_enum) => {
            if is_union_enum(&input) {
                derive_decode_union_enum(name, &impl_generics, &ty_generics, where_clause, data_enum)
            } else {
                panic!("SszDecode for enums requires #[ssz(enum_behaviour = \"union\")]")
            }
        }
        Data::Union(_) => panic!("SszDecode cannot be derived for Rust unions"),
    };

    expanded.into()
}

fn derive_decode_transparent(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let (_, inner_ty) = transparent_field_info(data);

    let constructor = match &data.fields {
        Fields::Unnamed(_) => quote! { #name(inner) },
        Fields::Named(f) => {
            let field_name = f.named.first().unwrap().ident.as_ref().unwrap();
            quote! { #name { #field_name: inner } }
        }
        _ => panic!("#[ssz(transparent)] requires exactly one field"),
    };

    quote! {
        impl #impl_generics ssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                <#inner_ty as ssz::SszDecode>::is_fixed_size()
            }

            fn fixed_size() -> usize {
                <#inner_ty as ssz::SszDecode>::fixed_size()
            }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
                let inner = <#inner_ty as ssz::SszDecode>::from_ssz_bytes(bytes)?;
                Ok(#constructor)
            }
        }
    }
}

fn derive_decode_struct(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let fields = match &data.fields {
        Fields::Named(f) => &f.named,
        _ => panic!("SszDecode can only be derived for structs with named fields"),
    };

    let field_names: Vec<_> = fields.iter().map(|f| f.ident.as_ref().unwrap()).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();

    // is_fixed_size
    let is_fixed_checks = field_types.iter().map(|ty| {
        quote! { <#ty as ssz::SszDecode>::is_fixed_size() }
    });

    // fixed_size
    let fixed_size_terms: Vec<_> = field_types.iter().map(|ty| {
        quote! { <#ty as ssz::SszDecode>::fixed_size() }
    }).collect();

    // Compute fixed_part_len at runtime — wrap in braces for `+` separator
    let fixed_part_len_terms: Vec<_> = field_types.iter().map(|ty| {
        quote! {
            {
                if <#ty as ssz::SszDecode>::is_fixed_size() {
                    <#ty as ssz::SszDecode>::fixed_size()
                } else {
                    4usize
                }
            }
        }
    }).collect();

    // Fixed-part pass: decode_fixed for fixed fields, read_variable_offset for variable
    let fixed_pass_stmts = field_names.iter().zip(field_types.iter()).map(|(fname, ty)| {
        quote! {
            let #fname = if <#ty as ssz::SszDecode>::is_fixed_size() {
                Some(decoder.decode_fixed::<#ty>()?)
            } else {
                decoder.read_variable_offset()?;
                None
            };
        }
    });

    // Variable-part pass: decode_variable for variable fields
    let variable_pass_stmts = field_names.iter().zip(field_types.iter()).map(|(fname, ty)| {
        quote! {
            let #fname = if <#ty as ssz::SszDecode>::is_fixed_size() {
                #fname.unwrap()
            } else {
                decoder.decode_variable::<#ty>()?
            };
        }
    });

    let field_constructs = field_names.iter().map(|fname| {
        quote! { #fname }
    });

    quote! {
        impl #impl_generics ssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                true #(&& #is_fixed_checks)*
            }

            fn fixed_size() -> usize {
                if <Self as ssz::SszDecode>::is_fixed_size() {
                    0 #(+ #fixed_size_terms)*
                } else {
                    0
                }
            }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
                let fixed_part_len: usize = 0 #(+ #fixed_part_len_terms)*;
                let mut decoder = ssz::ContainerDecoder::new(bytes, fixed_part_len)?;

                // Fixed-part pass
                #(#fixed_pass_stmts)*

                // Variable-part pass
                #(#variable_pass_stmts)*

                Ok(#name {
                    #(#field_constructs,)*
                })
            }
        }
    }
}

fn derive_decode_union_enum(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataEnum,
) -> proc_macro2::TokenStream {
    let variant_arms: Vec<_> = data.variants.iter().enumerate().map(|(i, variant)| {
        let variant_name = &variant.ident;
        let selector = i as u8;
        match &variant.fields {
            Fields::Unnamed(f) if f.unnamed.len() == 1 => {
                let ty = &f.unnamed.first().unwrap().ty;
                quote! {
                    #selector => {
                        let inner = <#ty as ssz::SszDecode>::from_ssz_bytes(&bytes[1..])?;
                        Ok(#name::#variant_name(inner))
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    #selector => {
                        if bytes.len() != 1 {
                            return Err(ssz::DecodeError::AdditionalBytes {
                                expected: 1,
                                got: bytes.len(),
                            });
                        }
                        Ok(#name::#variant_name)
                    }
                }
            }
            _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
        }
    }).collect();

    quote! {
        impl #impl_generics ssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool { false }
            fn fixed_size() -> usize { 0 }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
                if bytes.is_empty() {
                    return Err(ssz::DecodeError::EmptyInput);
                }
                let selector = bytes[0];
                match selector {
                    #(#variant_arms)*
                    s => Err(ssz::DecodeError::InvalidUnionSelector(s)),
                }
            }
        }
    }
}

// ── HashTreeRoot ──

#[proc_macro_derive(HashTreeRoot, attributes(ssz))]
pub fn derive_hash_tree_root(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if is_transparent(&input) {
                derive_htr_transparent(name, &impl_generics, &ty_generics, where_clause, data_struct)
            } else {
                derive_htr_struct(name, &impl_generics, &ty_generics, where_clause, data_struct)
            }
        }
        Data::Enum(data_enum) => {
            if is_union_enum(&input) {
                derive_htr_union_enum(name, &impl_generics, &ty_generics, where_clause, data_enum)
            } else {
                panic!("HashTreeRoot for enums requires #[ssz(enum_behaviour = \"union\")]")
            }
        }
        Data::Union(_) => panic!("HashTreeRoot cannot be derived for Rust unions"),
    };

    expanded.into()
}

fn derive_htr_transparent(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let (field_access, _) = transparent_field_info(data);

    quote! {
        impl #impl_generics ssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self) -> ssz_merkle::Node {
                ssz_merkle::HashTreeRoot::hash_tree_root(&#field_access)
            }
        }
    }
}

fn derive_htr_struct(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let fields = match &data.fields {
        Fields::Named(f) => &f.named,
        _ => panic!("HashTreeRoot can only be derived for structs with named fields"),
    };

    let field_roots = fields.iter().map(|f| {
        let field_name = f.ident.as_ref().unwrap();
        quote! {
            ssz_merkle::HashTreeRoot::hash_tree_root(&self.#field_name)
        }
    });

    let num_fields = fields.len();

    quote! {
        impl #impl_generics ssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self) -> ssz_merkle::Node {
                let field_roots: [ssz_merkle::Node; #num_fields] = [
                    #(#field_roots,)*
                ];
                ssz_merkle::merkleize(&field_roots, None)
            }
        }
    }
}

fn derive_htr_union_enum(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataEnum,
) -> proc_macro2::TokenStream {
    let variant_arms: Vec<_> = data.variants.iter().enumerate().map(|(i, variant)| {
        let variant_name = &variant.ident;
        let selector = i as u8;
        match &variant.fields {
            Fields::Unnamed(_f) => {
                quote! {
                    #name::#variant_name(inner) => {
                        let root = ssz_merkle::HashTreeRoot::hash_tree_root(inner);
                        ssz_merkle::mix_in_selector(&root, #selector)
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    #name::#variant_name => {
                        let root = ssz_merkle::ZERO_HASHES[0];
                        ssz_merkle::mix_in_selector(&root, #selector)
                    }
                }
            }
            _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
        }
    }).collect();

    quote! {
        impl #impl_generics ssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self) -> ssz_merkle::Node {
                match self {
                    #(#variant_arms)*
                }
            }
        }
    }
}
