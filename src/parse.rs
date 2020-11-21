//! Parsing logic

use syn::punctuated::Punctuated;
use syn::{parenthesized, token, Attribute, Expr, ExprLet, Ident, Result, Token, Visibility};
use syn::{
    parse::{Parse, ParseStream},
    Field,
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

#[derive(Clone)]
pub struct Relation {
    pub attribute: Option<Ident>,
    pub attrs: Vec<Attribute>,
    pub visibility: Visibility,
    pub struct_token: Token![struct],
    pub name: Ident,
    pub paren_token: token::Paren,
    pub fields: Punctuated<Field, Token![,]>,
    pub semi_token: Token![;],
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
        #[allow(clippy::eval_order_dependence)]
        Ok(Self {
            attribute,
            attrs: input.call(Attribute::parse_outer)?,
            visibility: input.parse()?,
            struct_token: input.parse()?,
            name: input.parse()?,
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

            let arrow_token = syn::parse_quote!(<-);
            let clauses = syn::parse_quote!((true));

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
}

impl Parse for Clause {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(token::Paren) {
            input.parse().map(Clause::Expr)
        } else if lookahead.peek(Token![let]) {
            input.parse().map(Clause::Let)
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
    pub fields: Punctuated<Option<Expr>, Token![,]>,
}

impl Parse for Fact {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        #[allow(clippy::eval_order_dependence)]
        Ok(Self {
            negate: input.parse()?,
            relation: input.parse()?,
            paren_token: parenthesized!(content in input),
            fields: content.parse_terminated(|input| {
                if input.peek(Token![_]) {
                    let _: Token![_] = input.parse()?;
                    Ok(None)
                } else {
                    input.parse().map(Some)
                }
            })?,
        })
    }
}
