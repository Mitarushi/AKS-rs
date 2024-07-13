use proc_macro::{TokenStream, TokenTree};

fn to_token_stream(input: Vec<TokenTree>) -> TokenStream {
    let mut result = TokenStream::new();
    result.extend(input);
    result
}
fn split_tokens(input: TokenStream) -> Vec<TokenStream> {
    let mut result = Vec::new();
    let mut last_token = Vec::new();
    let mut bracket_count = 0;
    for token in input {
        last_token.push(token.clone());
        if let TokenTree::Punct(punct) = &token {
            let c = punct.as_char();
            if c == '<' || c == '(' || c == '[' {
                bracket_count += 1;
            } else if c == '>' || c == ')' || c == ']' {
                bracket_count -= 1;
            } else if c == ',' && bracket_count == 0 {
                last_token.pop();
                result.push(to_token_stream(last_token.clone()));
                last_token = Vec::new();
                continue;
            }
        }
    }
    result.push(to_token_stream(last_token));

    result
}

fn generate_overload_code(generics: &TokenStream, trait_name: &TokenStream, type1: &TokenStream, type2: &TokenStream, output_type: &TokenStream, method_name: &TokenStream, method: &TokenStream) -> TokenStream {
    let result = format!(
        r#"
        impl {generics} {trait_name}<{type2}> for {type1} {{
            type Output = {output_type};

            fn {method_name}(self, other: {type2}) -> {output_type} {{
                self.{method}(&other)
            }}
        }}

        impl {generics} {trait_name}<&{type2}> for {type1} {{
            type Output = {output_type};

            fn {method_name}(self, other: &{type2}) -> {output_type} {{
                self.{method}(other)
            }}
        }}

        impl {generics} {trait_name}<{type2}> for &{type1} {{
            type Output = {output_type};

            fn {method_name}(self, other: {type2}) -> {output_type} {{
                self.{method}(&other)
            }}
        }}

        impl {generics} {trait_name}<&{type2}> for &{type1} {{
            type Output = {output_type};

            fn {method_name}(self, other: &{type2}) -> {output_type} {{
                self.{method}(other)
            }}
        }}
        "#,
        generics = generics.to_string(),
        trait_name = trait_name.to_string(),
        type1 = type1.to_string(),
        type2 = type2.to_string(),
        output_type = output_type.to_string(),
        method_name = method_name.to_string(),
        method = method.to_string()
    );

    result.parse().unwrap()
}

#[proc_macro]
pub fn overload(input: TokenStream) -> TokenStream {
    let input = split_tokens(input);

    let (generics, trait_name, type1, type2, output_type, method_name, method) = match input.as_slice() {
        [generics, trait_name, type1, type2, output_type, method_name, method] => (
            generics, trait_name, type1, type2, output_type, method_name, method
        ),
        [generics, trait_nane, type1, type2, method_name, method] => (
            generics, trait_nane, type1, type2, type1, method_name, method
        ),
        [generics, trait_nane, type1,method_name, method] => (
            generics, trait_nane, type1, type1, type1, method_name, method
        ),
        _ => panic!("Invalid input")
    };

    generate_overload_code(generics, trait_name, type1, type2, output_type, method_name, method)
}

fn generate_unary_overload_code(generics: &TokenStream, trait_name: &TokenStream, type_: &TokenStream, method_name: &TokenStream, method: &TokenStream) -> TokenStream {
    let result = format!(
        r#"
        impl {generics} {trait_name} for {type_} {{
            type Output = {type_};

            fn {method_name}(self) -> {type_} {{
                self.{method}()
            }}
        }}

        impl {generics} {trait_name} for &{type_} {{
            type Output = {type_};

            fn {method_name}(self) -> {type_} {{
                self.{method}()
            }}
        }}
        "#,
        generics = generics.to_string(),
        trait_name = trait_name.to_string(),
        type_ = type_.to_string(),
        method_name = method_name.to_string(),
        method = method.to_string()
    );

    result.parse().unwrap()
}


#[proc_macro]
pub fn overload_unary(input: TokenStream) -> TokenStream {
    let input = split_tokens(input);

    let (generics, trait_name, type_, method_name, method) = match input.as_slice() {
        [generics, trait_name, type_, method_name, method] => (
            generics, trait_name, type_, method_name, method
        ),
        _ => panic!("Invalid input")
    };

    generate_unary_overload_code(generics, trait_name, type_, method_name, method)
}

fn generate_overload_eq_code(generics: &TokenStream, trait_name: &TokenStream, type_: &TokenStream, method_name: &TokenStream, method: &TokenStream) -> TokenStream {
    let result = format!(
        r#"
        impl {generics} {trait_name} for {type_} {{
            fn {method_name}(&self, other: &{type_}) -> bool {{
                self.{method}(other)
            }}
        }}
        "#,
        generics = generics.to_string(),
        trait_name = trait_name.to_string(),
        type_ = type_.to_string(),
        method_name = method_name.to_string(),
        method = method.to_string()
    );

    result.parse().unwrap()
}

#[proc_macro]
pub fn overload_eq(input: TokenStream) -> TokenStream {
    let input = split_tokens(input);

    let (generics, trait_name, type_, method_name, method) = match input.as_slice() {
        [generics, trait_name, type_, method_name, method] => (
            generics, trait_name, type_, method_name, method
        ),
        _ => panic!("Invalid input")
    };

    generate_overload_eq_code(generics, trait_name, type_, method_name, method)
}