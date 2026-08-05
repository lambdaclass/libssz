extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Meta};

/// The `#[ssz(...)]` configuration on a type.
#[derive(Default)]
struct SszAttrs {
    transparent: bool,
    progressive_container: bool,
    union_enum: bool,
    /// `active_fields` from `#[ssz(progressive_container, active_fields = [1, 0, 1])]`.
    /// `None` means every field is active.
    active_fields: Option<Vec<bool>>,
}

/// Parse every `#[ssz(...)]` attribute on `input`, rejecting unrecognized keys.
///
/// Unknown keys are a hard error rather than being ignored. A typo such as
/// `#[ssz(progresive_container)]` would otherwise silently fall through to plain
/// container merkleization, producing a different root with no diagnostic.
fn ssz_attrs(input: &DeriveInput) -> SszAttrs {
    let mut parsed = SszAttrs::default();

    for attr in &input.attrs {
        if !attr.path().is_ident("ssz") {
            continue;
        }
        if !matches!(&attr.meta, Meta::List(_)) {
            panic!("#[ssz] must be a list, as in #[ssz(transparent)]");
        }
        let result = attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("transparent") {
                parsed.transparent = true;
            } else if meta.path.is_ident("progressive_container") {
                parsed.progressive_container = true;
            } else if meta.path.is_ident("active_fields") {
                let array: syn::ExprArray = meta.value()?.parse()?;
                parsed.active_fields = Some(parse_active_fields(&array));
            } else if meta.path.is_ident("enum_behaviour") {
                let value: syn::LitStr = meta.value()?.parse()?;
                match value.value().as_str() {
                    "union" => parsed.union_enum = true,
                    other => {
                        panic!("unknown #[ssz(enum_behaviour = \"{other}\")]; expected \"union\"")
                    }
                }
            } else {
                let key = meta
                    .path
                    .get_ident()
                    .map(ToString::to_string)
                    .unwrap_or_default();
                panic!(
                    "unknown #[ssz({key})]; expected transparent, progressive_container, \
                     active_fields or enum_behaviour"
                );
            }
            Ok(())
        });
        if let Err(e) = result {
            panic!("invalid #[ssz(...)]: {e}");
        }
    }

    if parsed.transparent && parsed.progressive_container {
        panic!("#[ssz(transparent)] and #[ssz(progressive_container)] are mutually exclusive");
    }
    if parsed.active_fields.is_some() && !parsed.progressive_container {
        panic!("#[ssz(active_fields = [...])] requires #[ssz(progressive_container)]");
    }

    parsed
}

/// Parse an `active_fields` array literal such as `[1, 0, 1]` into booleans.
fn parse_active_fields(array: &syn::ExprArray) -> Vec<bool> {
    array
        .elems
        .iter()
        .map(|elem| match elem {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(int),
                ..
            }) => match int.base10_digits() {
                "0" => false,
                "1" => true,
                other => panic!("active_fields entries must be 0 or 1, found {other}"),
            },
            _ => panic!("active_fields entries must be the integer literals 0 or 1"),
        })
        .collect()
}

/// The named fields of a struct, or a compile error naming `context`.
fn named_fields<'a>(
    data: &'a syn::DataStruct,
    context: &str,
) -> &'a syn::punctuated::Punctuated<syn::Field, syn::token::Comma> {
    match &data.fields {
        Fields::Named(f) => &f.named,
        _ => panic!("{context} can only be derived for structs with named fields"),
    }
}

/// A `hash_tree_root` call per named field, in declaration order.
fn field_root_exprs(
    fields: &syn::punctuated::Punctuated<syn::Field, syn::token::Comma>,
) -> Vec<proc_macro2::TokenStream> {
    fields
        .iter()
        .map(|f| {
            let field_name = f.ident.as_ref().unwrap();
            quote! {
                libssz_merkle::HashTreeRoot::hash_tree_root(&self.#field_name, hasher)
            }
        })
        .collect()
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
    let attrs = ssz_attrs(&input);
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if attrs.transparent {
                derive_encode_transparent(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            } else {
                derive_encode_struct(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            }
        }
        Data::Enum(data_enum) => {
            if attrs.union_enum {
                derive_encode_union_enum(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_enum,
                )
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
        impl #impl_generics libssz::SszEncode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                <#inner_ty as libssz::SszEncode>::is_fixed_size()
            }

            fn fixed_size() -> usize {
                <#inner_ty as libssz::SszEncode>::fixed_size()
            }

            fn encoded_len(&self) -> usize {
                libssz::SszEncode::encoded_len(&#field_access)
            }

            fn ssz_append(&self, buf: &mut Vec<u8>) {
                libssz::SszEncode::ssz_append(&#field_access, buf);
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
        quote! { <#ty as libssz::SszEncode>::is_fixed_size() }
    });

    // fixed_size: sum of fixed sizes (only valid if is_fixed_size)
    let fixed_size_terms: Vec<_> = field_types
        .iter()
        .map(|ty| {
            quote! { <#ty as libssz::SszEncode>::fixed_size() }
        })
        .collect();

    // encoded_len — wrap in braces so `+` separator works between if-exprs
    let encoded_len_terms: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                {
                    if <#ty as libssz::SszEncode>::is_fixed_size() {
                        <#ty as libssz::SszEncode>::fixed_size()
                    } else {
                        4 + libssz::SszEncode::encoded_len(&self.#fname)
                    }
                }
            }
        })
        .collect();

    // ssz_append: use ContainerEncoder
    let append_stmts: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                if <#ty as libssz::SszEncode>::is_fixed_size() {
                    encoder.append_fixed(&self.#fname);
                } else {
                    encoder.append_variable(&self.#fname);
                };
            }
        })
        .collect();

    // Fast path for all-fixed containers: direct appends, no ContainerEncoder
    let direct_append_stmts: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                <#ty as libssz::SszEncode>::ssz_append(&self.#fname, buf);
            }
        })
        .collect();

    // Compute fixed_part_len for ContainerEncoder — same pattern as decode
    let encode_fixed_part_len_terms: Vec<_> = field_types
        .iter()
        .map(|ty| {
            quote! {
                {
                    if <#ty as libssz::SszEncode>::is_fixed_size() {
                        <#ty as libssz::SszEncode>::fixed_size()
                    } else {
                        4usize
                    }
                }
            }
        })
        .collect();

    // Bulk encode for all-fixed structs: inline field appends into the loop body
    let bulk_append_stmts: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                <#ty as libssz::SszEncode>::ssz_append(&item.#fname, buf);
            }
        })
        .collect();

    quote! {
        impl #impl_generics libssz::SszEncode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                true #(&& #is_fixed_checks)*
            }

            fn fixed_size() -> usize {
                if <Self as libssz::SszEncode>::is_fixed_size() {
                    0 #(+ #fixed_size_terms)*
                } else {
                    0
                }
            }

            fn encoded_len(&self) -> usize {
                0 #(+ #encoded_len_terms)*
            }

            fn ssz_append(&self, buf: &mut Vec<u8>) {
                if <Self as libssz::SszEncode>::is_fixed_size() {
                    #(#direct_append_stmts)*
                } else {
                    let fixed_part_len: usize = 0 #(+ #encode_fixed_part_len_terms)*;
                    let total_len = libssz::SszEncode::encoded_len(self);
                    let mut encoder = libssz::ContainerEncoder::with_capacity(buf, fixed_part_len, total_len);
                    #(#append_stmts)*
                    encoder.finalize();
                }
            }

            fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>)
            where
                Self: Sized,
            {
                if <Self as libssz::SszEncode>::is_fixed_size() {
                    buf.reserve(<Self as libssz::SszEncode>::fixed_size() * items.len());
                    for item in items {
                        #(#bulk_append_stmts)*
                    }
                } else {
                    buf.reserve(<Self as libssz::SszEncode>::fixed_size() * items.len());
                    for item in items {
                        item.ssz_append(buf);
                    }
                }
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
    let variant_arms: Vec<_> = data
        .variants
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let variant_name = &variant.ident;
            let selector = i as u8;
            match &variant.fields {
                Fields::Unnamed(f) if f.unnamed.len() == 1 => {
                    quote! {
                        #name::#variant_name(inner) => {
                            buf.push(#selector);
                            libssz::SszEncode::ssz_append(inner, buf);
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
        })
        .collect();

    let encoded_len_arms: Vec<_> = data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            match &variant.fields {
                Fields::Unnamed(_) => {
                    quote! {
                        #name::#variant_name(inner) => 1 + libssz::SszEncode::encoded_len(inner)
                    }
                }
                Fields::Unit => {
                    quote! {
                        #name::#variant_name => 1
                    }
                }
                _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
            }
        })
        .collect();

    quote! {
        impl #impl_generics libssz::SszEncode for #name #ty_generics #where_clause {
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
    let attrs = ssz_attrs(&input);
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if attrs.transparent {
                derive_decode_transparent(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            } else {
                derive_decode_struct(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            }
        }
        Data::Enum(data_enum) => {
            if attrs.union_enum {
                derive_decode_union_enum(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_enum,
                )
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
        impl #impl_generics libssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                <#inner_ty as libssz::SszDecode>::is_fixed_size()
            }

            fn fixed_size() -> usize {
                <#inner_ty as libssz::SszDecode>::fixed_size()
            }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, libssz::DecodeError> {
                let inner = <#inner_ty as libssz::SszDecode>::from_ssz_bytes(bytes)?;
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
        quote! { <#ty as libssz::SszDecode>::is_fixed_size() }
    });

    // fixed_size
    let fixed_size_terms: Vec<_> = field_types
        .iter()
        .map(|ty| {
            quote! { <#ty as libssz::SszDecode>::fixed_size() }
        })
        .collect();

    // Compute fixed_part_len at runtime — wrap in braces for `+` separator
    let fixed_part_len_terms: Vec<_> = field_types
        .iter()
        .map(|ty| {
            quote! {
                {
                    if <#ty as libssz::SszDecode>::is_fixed_size() {
                        <#ty as libssz::SszDecode>::fixed_size()
                    } else {
                        4usize
                    }
                }
            }
        })
        .collect();

    // Fixed-part pass: decode_fixed for fixed fields, read_variable_offset for variable
    let fixed_pass_stmts = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                let #fname = if <#ty as libssz::SszDecode>::is_fixed_size() {
                    Some(decoder.decode_fixed::<#ty>()?)
                } else {
                    decoder.read_variable_offset()?;
                    None
                };
            }
        });

    // Variable-part pass: decode_variable for variable fields
    let variable_pass_stmts = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                let #fname = if <#ty as libssz::SszDecode>::is_fixed_size() {
                    #fname.unwrap()
                } else {
                    decoder.decode_variable::<#ty>()?
                };
            }
        });

    // Inline field-by-field decode for all-fixed containers, used by both
    // from_ssz_bytes and ssz_decode_fixed_vec.
    let fixed_decode_stmts: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(fname, ty)| {
            quote! {
                let (#fname, __remaining) = {
                    let (slice, rest) = __remaining.split_at(<#ty as libssz::SszDecode>::fixed_size());
                    (<#ty as libssz::SszDecode>::from_ssz_bytes(slice)?, rest)
                };
            }
        })
        .collect();

    quote! {
        impl #impl_generics libssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool {
                true #(&& #is_fixed_checks)*
            }

            fn fixed_size() -> usize {
                if <Self as libssz::SszDecode>::is_fixed_size() {
                    0 #(+ #fixed_size_terms)*
                } else {
                    0
                }
            }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, libssz::DecodeError> {
                if <Self as libssz::SszDecode>::is_fixed_size() {
                    let expected = <Self as libssz::SszDecode>::fixed_size();
                    if bytes.len() != expected {
                        return Err(libssz::DecodeError::InvalidFixedLength { expected, got: bytes.len() });
                    }
                    let __remaining = bytes;
                    #(#fixed_decode_stmts)*
                    Ok(#name {
                        #(#field_names,)*
                    })
                } else {
                    let fixed_part_len: usize = 0 #(+ #fixed_part_len_terms)*;
                    let mut decoder = libssz::ContainerDecoder::new(bytes, fixed_part_len)?;

                    // Fixed-part pass
                    #(#fixed_pass_stmts)*

                    // Variable-part pass
                    #(#variable_pass_stmts)*

                    Ok(#name {
                        #(#field_names,)*
                    })
                }
            }

            fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, libssz::DecodeError> {
                if <Self as libssz::SszDecode>::is_fixed_size() {
                    let item_size = <Self as libssz::SszDecode>::fixed_size();
                    if item_size > 0 && bytes.len() % item_size != 0 {
                        return Err(libssz::DecodeError::InvalidByteLength {
                            expected: item_size,
                            got: bytes.len(),
                        });
                    }
                    let count = if item_size > 0 { bytes.len() / item_size } else { 0 };
                    let mut result = Vec::with_capacity(count);
                    // Inline per-item decode: skip struct-level length check
                    // since chunks_exact guarantees correct chunk size.
                    for chunk in bytes.chunks_exact(item_size) {
                        let __remaining = chunk;
                        #(#fixed_decode_stmts)*
                        result.push(#name {
                            #(#field_names,)*
                        });
                    }
                    Ok(result)
                } else {
                    // Variable-size: fall back to default
                    let item_size = <Self as libssz::SszDecode>::fixed_size();
                    bytes
                        .chunks_exact(item_size)
                        .map(Self::from_ssz_bytes)
                        .collect()
                }
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
    let variant_arms: Vec<_> = data
        .variants
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let variant_name = &variant.ident;
            let selector = i as u8;
            match &variant.fields {
                Fields::Unnamed(f) if f.unnamed.len() == 1 => {
                    let ty = &f.unnamed.first().unwrap().ty;
                    quote! {
                        #selector => {
                            let inner = <#ty as libssz::SszDecode>::from_ssz_bytes(&bytes[1..])?;
                            Ok(#name::#variant_name(inner))
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        #selector => {
                            if bytes.len() != 1 {
                                return Err(libssz::DecodeError::AdditionalBytes {
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
        })
        .collect();

    quote! {
        impl #impl_generics libssz::SszDecode for #name #ty_generics #where_clause {
            fn is_fixed_size() -> bool { false }
            fn fixed_size() -> usize { 0 }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, libssz::DecodeError> {
                if bytes.is_empty() {
                    return Err(libssz::DecodeError::EmptyInput);
                }
                let selector = bytes[0];
                match selector {
                    #(#variant_arms)*
                    s => Err(libssz::DecodeError::InvalidUnionSelector(s)),
                }
            }
        }
    }
}

// ── HashTreeRoot ──

/// Derive [`libssz_merkle::HashTreeRoot`](https://docs.rs/libssz-merkle/latest/libssz_merkle/trait.HashTreeRoot.html).
///
/// A plain struct merkleizes as an SSZ container: the field roots become the
/// leaves of a binary tree. The `#[ssz(...)]` attribute selects other shapes:
///
/// - `#[ssz(transparent)]` on a single-field struct roots to the inner value's
///   own root, adding no tree level of its own.
/// - `#[ssz(enum_behaviour = "union")]` is required on enums, and mixes the
///   selector into the root.
/// - `#[ssz(progressive_container)]` merkleizes as an EIP-7495
///   `ProgressiveContainer`.
///
/// An unrecognized key is a compile error, so a misspelled attribute cannot
/// silently select a different merkleization scheme.
///
/// # Progressive containers
///
/// The root is
/// `mix_in_active_fields(merkleize_progressive(chunks), active_fields)`, where
/// each active position contributes the next field root in declaration order
/// and each inactive position contributes a zero chunk.
///
/// `active_fields` defaults to every field active. Pass it explicitly for a
/// container with inactive (deprecated) fields:
///
/// ```
/// use libssz_derive::HashTreeRoot;
///
/// #[derive(HashTreeRoot)]
/// #[ssz(progressive_container, active_fields = [1, 0, 1, 0, 1])]
/// struct Foo {
///     a: u8,        // active_fields[0]
///     b: u64,       // active_fields[2]
///     c: [u8; 32],  // active_fields[4]
/// }
/// ```
///
/// The EIP-7495 legality rules are enforced at compile time: `active_fields`
/// must be non-empty, hold at most 256 entries, not end in `0`, and have
/// exactly as many `1` entries as the struct has fields.
#[proc_macro_derive(HashTreeRoot, attributes(ssz))]
pub fn derive_hash_tree_root(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let attrs = ssz_attrs(&input);
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = match &input.data {
        Data::Struct(data_struct) => {
            if attrs.transparent {
                derive_htr_transparent(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            } else if attrs.progressive_container {
                derive_htr_progressive_container(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                    attrs.active_fields.as_deref(),
                )
            } else {
                derive_htr_struct(
                    name,
                    &impl_generics,
                    &ty_generics,
                    where_clause,
                    data_struct,
                )
            }
        }
        Data::Enum(data_enum) => {
            assert!(
                !attrs.progressive_container,
                "#[ssz(progressive_container)] applies to structs, not enums"
            );
            if attrs.union_enum {
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
        impl #impl_generics libssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self, hasher: &impl libssz_merkle::Sha256Hasher) -> libssz_merkle::Node {
                libssz_merkle::HashTreeRoot::hash_tree_root(&#field_access, hasher)
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
    let fields = named_fields(data, "HashTreeRoot");
    let field_roots = field_root_exprs(fields);
    let num_fields = fields.len();

    quote! {
        impl #impl_generics libssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self, hasher: &impl libssz_merkle::Sha256Hasher) -> libssz_merkle::Node {
                let field_roots: [libssz_merkle::Node; #num_fields] = [
                    #(#field_roots,)*
                ];
                libssz_merkle::merkleize(hasher, &field_roots, None)
            }
        }
    }
}

/// Validate an `active_fields` configuration against the EIP-7495 legality
/// rules in consensus-specs `ssz/simple-serialize.md`.
///
/// The 256-entry cap is the spec's own: `mix_in_active_fields` hashes
/// `pack_bits(active_fields)` as a single chunk, which holds only up to 256 bits.
fn validate_active_fields(active_fields: &[bool], num_fields: usize) {
    assert!(
        !active_fields.is_empty(),
        "#[ssz(progressive_container)] requires at least one field"
    );
    assert!(
        active_fields.len() <= 256,
        "#[ssz(progressive_container)] allows at most 256 active_fields entries, found {}",
        active_fields.len()
    );
    assert!(
        *active_fields.last().unwrap(),
        "#[ssz(progressive_container)] active_fields must not end in 0"
    );
    let active_count = active_fields.iter().filter(|&&active| active).count();
    assert_eq!(
        active_count, num_fields,
        "#[ssz(progressive_container)] active_fields has {active_count} active entries \
         but the struct has {num_fields} fields"
    );
}

/// The single chunk that `pack_bits(active_fields)` produces.
///
/// `active_fields` holds at most 256 bits, so it always packs into exactly one
/// 32-byte chunk. Mirrors `libssz_merkle::mix_in_active_fields`.
fn active_fields_node(active_fields: &[bool]) -> [u8; 32] {
    let mut node = [0u8; 32];
    for (i, &active) in active_fields.iter().enumerate() {
        if active {
            node[i / 8] |= 1 << (i % 8);
        }
    }
    node
}

/// `HashTreeRoot` for an EIP-7495 `ProgressiveContainer`.
///
/// The `active_fields` chunk is folded in here rather than rebuilt on every
/// call: it is fully determined by the configuration, so calling
/// `mix_in_active_fields` would repack it, and allocate twice, per root.
fn derive_htr_progressive_container(
    name: &syn::Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    data: &syn::DataStruct,
    active_fields: Option<&[bool]>,
) -> proc_macro2::TokenStream {
    let fields = named_fields(data, "#[ssz(progressive_container)]");
    let num_fields = fields.len();
    let active_fields = active_fields.map_or_else(|| vec![true; num_fields], <[bool]>::to_vec);
    validate_active_fields(&active_fields, num_fields);

    let mut field_roots = field_root_exprs(fields).into_iter();
    let chunks: Vec<proc_macro2::TokenStream> = active_fields
        .iter()
        .map(|&active| {
            if active {
                field_roots
                    .next()
                    .expect("active count matches field count")
            } else {
                quote! { [0u8; 32] }
            }
        })
        .collect();
    let num_chunks = chunks.len();
    let active_node = active_fields_node(&active_fields);
    let active_node_bytes = active_node.iter();

    quote! {
        impl #impl_generics libssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self, hasher: &impl libssz_merkle::Sha256Hasher) -> libssz_merkle::Node {
                const ACTIVE_FIELDS: libssz_merkle::Node = [#(#active_node_bytes),*];
                let chunks: [libssz_merkle::Node; #num_chunks] = [
                    #(#chunks,)*
                ];
                let root = libssz_merkle::merkleize_progressive(hasher, &chunks);
                libssz_merkle::hash_nodes(hasher, &root, &ACTIVE_FIELDS)
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
    let variant_arms: Vec<_> = data
        .variants
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let variant_name = &variant.ident;
            let selector = i as u8;
            match &variant.fields {
                Fields::Unnamed(_) => {
                    quote! {
                        #name::#variant_name(inner) => {
                            let root = libssz_merkle::HashTreeRoot::hash_tree_root(inner, hasher);
                            libssz_merkle::mix_in_selector(hasher, &root, #selector)
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        #name::#variant_name => {
                            let root = libssz_merkle::ZERO_HASHES[0];
                            libssz_merkle::mix_in_selector(hasher, &root, #selector)
                        }
                    }
                }
                _ => panic!("Union enum variants must have exactly 0 or 1 fields"),
            }
        })
        .collect();

    quote! {
        impl #impl_generics libssz_merkle::HashTreeRoot for #name #ty_generics #where_clause {
            fn hash_tree_root(&self, hasher: &impl libssz_merkle::Sha256Hasher) -> libssz_merkle::Node {
                match self {
                    #(#variant_arms)*
                }
            }
        }
    }
}
