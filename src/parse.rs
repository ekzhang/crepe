//! Parsing logic

use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{
    parenthesized, parse_quote, token, Attribute, Expr, ExprLet, Field, Generics, Ident, Pat,
    Result, Token, Visibility,
};

#[derive(Clone)]
pub struct Program {
    pub relations: Vec<Relation>,
    pub rules: Vec<Rule>,
}

impl Parse for Program {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut relations: Vec<Relation> = Vec::new();
        let mut rules: Vec<Rule> = Vec::new();

        while !input.is_empty() {
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![@]) || lookahead.peek(Token![struct]) {
                relations.push(input.parse()?);
            } else if lookahead.peek(Ident) {
                rules.push(input.parse()?);
            } else {
                return Err(lookahead.error());
            }
        }

        Ok(Self { relations, rules })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationType {
    Input,
    Intermediate,
    Output,
}

#[derive(Clone)]
pub struct Relation {
    pub attribute: Option<Ident>,
    pub attrs: Vec<Attribute>,
    pub visibility: Visibility,
    pub struct_token: Token![struct],
    pub name: Ident,
    pub generics: Generics,
    pub paren_token: token::Paren,
    pub fields: Punctuated<Field, Token![,]>,
    pub semi_token: Token![;],
}

impl Relation {
    pub fn relation_type(&self) -> std::result::Result<RelationType, &Ident> {
        if let Some(attr) = &self.attribute {
            if attr == "input" {
                Ok(RelationType::Input)
            } else if attr == "output" {
                Ok(RelationType::Output)
            } else {
                Err(attr)
            }
        } else {
            Ok(RelationType::Intermediate)
        }
    }
}

impl Parse for Relation {
    fn parse(input: ParseStream) -> Result<Self> {
        let attribute = if input.peek(Token![@]) {
            let _: Token![@] = input.parse()?; // @
            Some(input.parse()?) // Ident
        } else {
            None
        };
        let content;
        #[allow(clippy::mixed_read_write_in_expression)]
        Ok(Self {
            attribute,
            attrs: input.call(Attribute::parse_outer)?,
            visibility: input.parse()?,
            struct_token: input.parse()?,
            name: input.parse()?,
            generics: input.parse()?,
            paren_token: parenthesized!(content in input),
            fields: content.parse_terminated(Field::parse_unnamed)?,
            semi_token: input.parse()?,
        })
    }
}

#[derive(Clone)]
pub struct Rule {
    pub goal: Fact,
    pub arrow_token: Token![<-],
    pub clauses: Punctuated<Clause, Token![,]>,
    pub semi_token: Token![;],
}

impl Parse for Rule {
    fn parse(input: ParseStream) -> Result<Self> {
        let goal = input.parse()?;
        let lookahead = input.lookahead1();

        // A fact followed by a semicolon is the same as a rule with a single
        // clause of `(true)`
        if lookahead.peek(Token![;]) {
            let semi_token = input.parse()?;

            let arrow_token = parse_quote!(<-);
            let clauses = parse_quote!((true));

            Ok(Self {
                goal,
                arrow_token,
                clauses,
                semi_token,
            })
        } else {
            Ok(Self {
                goal,
                arrow_token: input.parse()?,
                clauses: Punctuated::parse_separated_nonempty(input)?,
                semi_token: input.parse()?,
            })
        }
    }
}

#[derive(Clone)]
pub enum Clause {
    Fact(Fact),
    Expr(Expr),
    Let(ExprLet),
    For(For),
}

impl Parse for Clause {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(token::Paren) {
            input.parse().map(Clause::Expr)
        } else if lookahead.peek(Token![let]) {
            input.parse().map(Clause::Let)
        } else if lookahead.peek(Token![for]) {
            input.parse().map(Clause::For)
        } else if lookahead.peek(Ident) || lookahead.peek(Token![!]) {
            input.parse().map(Clause::Fact)
        } else {
            Err(lookahead.error())
        }
    }
}

#[derive(Clone)]
pub struct Fact {
    pub negate: Option<Token![!]>,
    pub relation: Ident,
    pub paren_token: token::Paren,
    pub fields: Punctuated<FactField, Token![,]>,
}

impl Parse for Fact {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        #[allow(clippy::mixed_read_write_in_expression)]
        Ok(Self {
            negate: input.parse()?,
            relation: input.parse()?,
            paren_token: parenthesized!(content in input),
            fields: content.parse_terminated(|input| {
                if input.peek(Token![_]) {
                    Ok(FactField::Ignored(input.parse()?))
                } else if input.peek(Token![ref]) {
                    let ref_tok: Token![ref] = input.parse()?;
                    let ident: Ident = input.parse()?;
                    Ok(FactField::Ref(ref_tok, ident))
                } else {
                    Ok(FactField::Expr(input.parse()?))
                }
            })?,
        })
    }
}

#[derive(Clone)]
pub struct For {
    pub for_token: Token![for],
    pub pat: Pat,
    pub in_token: Token![in],
    pub expr: Expr,
}

impl Parse for For {
    fn parse(input: ParseStream) -> Result<Self> {
        #[allow(clippy::mixed_read_write_in_expression)]
        Ok(Self {
            for_token: input.parse()?,
            pat: input.parse()?,
            in_token: input.parse()?,
            expr: input.parse()?,
        })
    }
}

#[derive(Clone)]
pub enum FactField {
    Ignored(Token![_]),
    Ref(Token![ref], Ident),
    Expr(Box<Expr>),
}

impl ToTokens for FactField {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            FactField::Ignored(t) => tokens.extend(quote! { #t }),
            FactField::Ref(ref_tok, ident) => tokens.extend(quote! { #ref_tok #ident }),
            FactField::Expr(expr) => tokens.extend(quote! { #expr }),
        }
    }
}
