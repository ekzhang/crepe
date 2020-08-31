//! Crepe is a library that allows you to write declarative logic programs in
//! Rust, with a [Datalog](https://en.wikipedia.org/wiki/Datalog)-like syntax.
//! It provides a procedural macro that generates efficient, safe code and
//! interoperates seamlessly with Rust programs.
//!
//! # Documentation
//! See the [`crepe!`](macro.Crepe.html) macro for detailed documentation.

extern crate proc_macro;

mod parse;

use proc_macro::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use quote::{format_ident, quote, quote_spanned};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use syn::{parse_macro_input, Expr, Ident};

use parse::{Clause, Fact, Program, Relation, Rule};

/// The main macro, which lets you write a Datalog program declaratively.
///
/// # Example
/// A program to calculate transitive closure might be written as:
/// ```
/// mod datalog {
///     use crepe::crepe;
///
///     crepe! {
///         @input
///         struct Edge(i32, i32);
///
///         @output
///         struct Tc(i32, i32);
///
///         Tc(x, y) <- Edge(x, y);
///         Tc(x, z) <- Edge(x, y), Tc(y, z);
///     }
///
///     pub fn run(edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
///         let output = Crepe::new()
///             .edge(edges.iter().map(|&(a, b)| Edge(a, b)))
///             .run();
///         output.tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
///     }
/// }
/// # fn main() {}
/// ```
/// Each `struct` in the program is turned into a Datalog relation, while each
/// line of the form `goal <- clause1, clause2, ...;` defines a rule that can
/// used in a logic programming setting to define new relations.
///
/// In order for the engine to work, all relations must be tuple structs, and
/// they automatically derive the `Eq`, `PartialEq`, `Hash`, `Copy`, and
/// `Clone` traits. This is necessary in order to create efficient indices that
/// are used in Datalog evaluation.
///
/// # Datalog Syntax Extensions
/// This library supports arbitrary Rust expression syntax within rules for
/// constructing new relations, as well as Boolean expressions that are
/// evaluated directly as clauses in rules. Basically, this gives you seamless
/// Rust interoperability within your Datalog programs.
///
/// For instance, here is a program that calculates the first 25 Fibonacci
/// numbers using arithmetic functors:
/// ```
/// # mod datalog {
/// #     use crepe::crepe;
/// crepe! {
///     @output
///     struct Fib(u32, u32);
///
///     Fib(0, 0) <- (true);
///     Fib(1, 1) <- (true);
///
///     Fib(n + 2, x + y) <- Fib(n, x), Fib(n + 1, y), (n + 2 <= 25);
/// }
/// #     pub fn run() -> Vec<(u32, u32)> {
/// #         let mut output = Crepe::new()
/// #             .run()
/// #             .fib
/// #             .into_iter()
/// #             .map(|Fib(x, y)| (x, y))
/// #             .collect::<Vec<_>>();
/// #         output.sort();
/// #         output
/// #     }
/// # }
/// #
/// # fn main() {
/// #     let results = datalog::run();
/// #     assert_eq!(
/// #         results,
/// #         [
/// #             (0, 0),
/// #             (1, 1),
/// #             (2, 1),
/// #             (3, 2),
/// #             (4, 3),
/// #             (5, 5),
/// #             (6, 8),
/// #             (7, 13),
/// #             (8, 21),
/// #             (9, 34),
/// #             (10, 55),
/// #             (11, 89),
/// #             (12, 144),
/// #             (13, 233),
/// #             (14, 377),
/// #             (15, 610),
/// #             (16, 987),
/// #             (17, 1597),
/// #             (18, 2584),
/// #             (19, 4181),
/// #             (20, 6765),
/// #             (21, 10946),
/// #             (22, 17711),
/// #             (23, 28657),
/// #             (24, 46368),
/// #             (25, 75025)
/// #         ]
/// #     );
/// # }
/// ```
/// Note that all Boolean conditions within the clauses of rules are evaluated
/// in-place, and they must be surrounded by parentheses.
///
/// # Hygiene
/// In addition to the relation structs, this macro generates implementations
/// of private `Crepe` and `CrepeOutput` structs. Therefore, it is
/// recommended to place each Datalog program within its own module, to prevent
/// name collisions.
#[proc_macro]
#[proc_macro_error]
pub fn crepe(input: TokenStream) -> TokenStream {
    let program = parse_macro_input!(input as Program);
    let context = Context::new(program);

    let struct_decls = make_struct_decls(&context);
    let runtime_decl = make_runtime_decl(&context);
    let runtime_impl = make_runtime_impl(&context);
    let output_decl = make_output_decl(&context);

    let expanded = quote! {
        #struct_decls
        #runtime_decl
        #runtime_impl
        #output_decl
    };

    expanded.into()
}

/// Intermediate representation for Datalog compilation
struct Context {
    rels_input: HashMap<String, Relation>,
    rels_output: HashMap<String, Relation>,
    rels_intermediate: HashMap<String, Relation>,
    rules: Vec<Rule>,
}

#[derive(Eq, PartialEq, Hash, Copy, Clone)]
enum IndexMode {
    Bound,
    Free,
}

#[derive(Eq, PartialEq, Hash, Clone)]
struct Index {
    name: String,
    mode: Vec<IndexMode>,
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mode: String = self
            .mode
            .iter()
            .map(|mode| match mode {
                IndexMode::Bound => 'b',
                IndexMode::Free => 'f',
            })
            .collect();
        write!(f, "__{}_index_{}", self.name.to_lowercase(), mode)
    }
}

impl Context {
    fn new(program: Program) -> Self {
        // Read in relations, ensure no duplicates
        let mut rels_input = HashMap::new();
        let mut rels_output = HashMap::new();
        let mut rels_intermediate = HashMap::new();
        let mut rel_names = HashSet::new();

        program.relations.into_iter().for_each(|relation| {
            let name = relation.name.to_string();
            if !rel_names.insert(name.clone()) {
                abort!(relation.name.span(), "Duplicate relation name: {}", name);
            }

            if let Some(ref attr) = relation.attribute {
                match attr.to_string().as_ref() {
                    "input" => {
                        rels_input.insert(name, relation);
                    }
                    "output" => {
                        rels_output.insert(name, relation);
                    }
                    s => abort!(
                        attr.span(),
                        "Invalid attribute @{}, expected '@input' or '@output'",
                        s
                    ),
                }
            } else {
                rels_intermediate.insert(name, relation);
            }
        });

        // Read in rules, ensure that there are no undefined relations, or
        // relations declared with incorrect arity.
        let check = |fact: &Fact| {
            let name = fact.relation.to_string();
            if !rel_names.contains(&name) {
                abort!(
                    fact.relation.span(),
                    "Relation name '{}' was not found. Did you misspell it?",
                    name
                );
            }
            let rel = rels_input
                .get(&name)
                .or(rels_output.get(&name))
                .or(rels_intermediate.get(&name))
                .expect("relation should exist");
            if rel.fields.len() != fact.fields.len() {
                abort!(
                    fact.relation.span(),
                    "Relation '{}' was declared with arity {}, but constructed with arity {} here.",
                    name,
                    rel.fields.len(),
                    fact.fields.len(),
                );
            }
        };
        program.rules.iter().for_each(|rule| {
            check(&rule.goal);
            if rels_input.get(&rule.goal.relation.to_string()).is_some() {
                abort!(
                    rule.goal.relation.span(),
                    "Relations marked as @input cannot be derived from a rule."
                )
            }
            rule.clauses.iter().for_each(|clause| {
                if let Clause::Fact(fact) = clause {
                    check(&fact);
                }
            });
        });

        // If all the relations are OK, we simply update the rules as-is.
        //
        // There's no need to do complex parsing logic yet; we can work that
        // out when we actually generate the runtime code, since that's
        // context-sensitive logic.
        let rules = program.rules;
        Self {
            rels_input,
            rels_output,
            rels_intermediate,
            rules,
        }
    }
}

fn make_struct_decls(context: &Context) -> proc_macro2::TokenStream {
    context
        .rels_input
        .values()
        .chain(context.rels_intermediate.values())
        .chain(context.rels_output.values())
        .map(|relation| {
            let struct_token = &relation.struct_token;
            let name = &relation.name;
            let semi_token = &relation.semi_token;
            let fields = &relation.fields;
            quote! {
                #[derive(Copy, Clone, Eq, PartialEq, Hash)]
                #struct_token #name(#fields)#semi_token
            }
        })
        .collect()
}

// Generated code should roughly look something like:
// ```ignore
// #[derive(::core::default::Default)]
// struct Crepe {
//     edge: ::std::vec::Vec<Edge>,
// }
// impl Crepe {
//     fn new() -> Self {
//         ::core::default::Default::default()
//     }
//     fn edge(&mut self, edge: impl IntoIterator<Item = Edge>) -> &mut Self {
//         self.edge.extend(edge)
//         self
//     }
//     fn run(self) -> Output {
//         // core logic here
//     }
// }
// ```

fn make_runtime_decl(context: &Context) -> proc_macro2::TokenStream {
    let fields: proc_macro2::TokenStream = context
        .rels_input
        .values()
        .map(|relation| {
            let name = &relation.name;
            let lowercase_name = to_lowercase(name);
            quote! {
                #lowercase_name: ::std::vec::Vec<#name>,
            }
        })
        .collect();

    quote! {
        #[derive(::core::default::Default)]
        struct Crepe {
            #fields
        }
    }
}

fn make_runtime_impl(context: &Context) -> proc_macro2::TokenStream {
    let builders = make_builders(&context);
    let run = make_run(&context);
    quote! {
        impl Crepe {
            fn new() -> Self {
                ::core::default::Default::default()
            }

            #builders
            #run
        }
    }
}

fn make_builders(context: &Context) -> proc_macro2::TokenStream {
    context.rels_input.values().map(|relation| {
        let name = &relation.name;
        let lower = to_lowercase(name);
        quote! {
            fn #lower(&mut self, #lower: impl ::core::iter::IntoIterator<Item = #name>) -> &mut Self {
                self.#lower.extend(#lower);
                self
            }
        }
    }).collect()
}

/// This is the primary method, which consumes the builder. It should compile
/// declarative Datalog into imperative logic to generate facts, essentially
/// what we signed up for!
///
/// Here's an example of what might be generated for transitive closure:
/// ```ignore
/// fn run(&self) -> CrepeOutput {
///     // Relations
///     let mut __edge: ::std::collections::HashSet<Edge> = ::std::collections::HashSet::new();
///     let mut __edge_update: ::std::collections::HashSet<Edge> = ::std::collections::HashSet::new();
///     let mut __tc: ::std::collections::HashSet<Tc> = ::std::collections::HashSet::new();
///     let mut __tc_update: ::std::collections::HashSet<Tc> = ::std::collections::HashSet::new();
///
///     // Indices
///     let mut __tc_index_bf: ::std::collections::HashMap<(i32,), ::std::vec::Vec<Tc>> =
///         ::std::collections::HashMap::new();
///
///     // Input relations
///     __edge_update.extend(&self.edge);
///
///     // Main loop, single stratum for simplicity
///     let mut __crepe_first_iteration = true;
///     while __crepe_first_iteration || !(__edge_update.is_empty() && __tc_update.is_empty()) {
///         __tc.extend(&__tc_update);
///         for &__crepe_var in __tc_update.iter() {
///             __tc_index_bf.entry((__crepe_var.0,)).or_default().push(__crepe_var);
///         }
///         __edge.extend(&__edge_update);
///
///         let mut __tc_new: ::std::collections::HashSet<Tc> = ::std::collections::HashSet::new();
///         let mut __edge_new: ::std::collections::HashSet<Tc> = ::std::collections::HashSet::new();
///
///         for &__crepe_var_0 in __edge.iter() {
///             let x = __crepe_var_0.0;
///             let y = __crepe_var_0.1;
///             let __crepe_goal = Tc(x, y);
///             if !__tc.contains(&__crepe_goal) {
///                 __tc_new.insert(__crepe_goal);
///             }
///         }
///
///         for &__crepe_var_0 in __edge.iter() {
///             let x = __crepe_var_0.0;
///             let y = __crepe_var_0.1;
///             if let Some(__iter_1) = __tc_index_bf.get(&(y,)) {
///                 for &__crepe_var_1 in __iter_1.iter() {
///                     let z = __crepe_var_1.1;
///                     let __crepe_goal = Tc(x, z);
///                     if !__tc.contains(&__crepe_goal) {
///                         __tc_new.insert(__crepe_goal);
///                     }
///                 }
///             }
///         }
///
///         __tc_update = __tc_new;
///         __edge_update = __edge_new;
///         __crepe_first_iteration = false;
///     }
///
///     // Return value
///     CrepeOutput {
///         tc: __tc.into_iter().collect(),
///     }
/// }
/// ```
/// Please note that this example uses naive evaluation for simplicity, but we
/// actually generate code for semi-naive evaluation.
fn make_run(context: &Context) -> proc_macro2::TokenStream {
    let all_rels = context
        .rels_input
        .values()
        .chain(context.rels_intermediate.values())
        .chain(context.rels_output.values());

    let mut indices: HashSet<Index> = HashSet::new();

    let main_loop = {
        let empty_cond: proc_macro2::TokenStream = all_rels
            .clone()
            .map(|rel| {
                let lower = to_lowercase(&rel.name);
                let rel_update = format_ident!("__{}_update", lower);
                quote! {
                    #rel_update.is_empty() &&
                }
            })
            .chain(std::iter::once(quote! {true}))
            .collect();

        let new_decls: proc_macro2::TokenStream = all_rels
            .clone()
            .map(|rel| {
                let name = &rel.name;
                let lower = to_lowercase(name);
                let rel_new = format_ident!("__{}_new", lower);
                quote! {
                    let mut #rel_new: ::std::collections::HashSet<#name> =
                        ::std::collections::HashSet::new();
                }
            })
            .collect();

        let rules: proc_macro2::TokenStream = context
            .rules
            .iter()
            .map(|rule| make_rule(rule, &mut indices))
            .collect();

        let updates: proc_macro2::TokenStream = {
            let rel_updates = all_rels.clone().map(|rel| {
                let lower = to_lowercase(&rel.name);
                let rel = format_ident!("__{}", lower);
                let rel_update = format_ident!("__{}_update", lower);
                quote! {
                    #rel.extend(&#rel_update);
                }
            });
            let index_updates = indices.iter().map(|index| {
                let rel = context
                    .rels_input
                    .get(&index.name)
                    .or(context.rels_output.get(&index.name))
                    .or(context.rels_intermediate.get(&index.name))
                    .expect("index relation should be found in context");
                let rel_update = format_ident!("__{}_update", to_lowercase(&rel.name));
                let index_name = Ident::new(&index.to_string(), rel.name.span());
                let index_name_update = format_ident!("{}_update", index_name);
                let bound_pos: Vec<_> = index
                    .mode
                    .iter()
                    .enumerate()
                    .filter_map(|(i, mode)| match mode {
                        IndexMode::Bound => Some(syn::Index::from(i)),
                        IndexMode::Free => None,
                    })
                    .collect();
                quote! {
                    #index_name_update.clear();
                    for &__crepe_var in #rel_update.iter() {
                        #index_name
                            .entry((#(__crepe_var.#bound_pos,)*))
                            .or_default()
                            .push(__crepe_var);
                        #index_name_update
                            .entry((#(__crepe_var.#bound_pos,)*))
                            .or_default()
                            .push(__crepe_var);
                    }
                }
            });
            rel_updates.chain(index_updates).collect()
        };

        let set_update_to_new: proc_macro2::TokenStream = all_rels
            .clone()
            .map(|rel| {
                let lower = to_lowercase(&rel.name);
                let rel_update = format_ident!("__{}_update", lower);
                let rel_new = format_ident!("__{}_new", lower);
                quote! {
                    #rel_update = #rel_new;
                }
            })
            .collect();

        quote! {
            let mut __crepe_first_iteration = true;
            while __crepe_first_iteration || !(#empty_cond) {
                #updates
                #new_decls
                #rules
                #set_update_to_new
                __crepe_first_iteration = false;
            }
        }
    };

    let initialize = {
        let init_rels = all_rels.clone().map(|rel| {
            let name = &rel.name;
            let lower = to_lowercase(name);
            let var = format_ident!("__{}", lower);
            let var_update = format_ident!("__{}_update", lower);
            quote! {
                let mut #var: ::std::collections::HashSet<#name> =
                    ::std::collections::HashSet::new();
                let mut #var_update: ::std::collections::HashSet<#name> =
                    ::std::collections::HashSet::new();
            }
        });
        let init_indices = indices.iter().map(|index| {
            let rel = context
                .rels_input
                .get(&index.name)
                .or(context.rels_output.get(&index.name))
                .or(context.rels_intermediate.get(&index.name))
                .expect("index relation should be found in context");
            let rel_name = &rel.name;
            let index_name = Ident::new(&index.to_string(), rel.name.span());
            let index_name_update = format_ident!("{}_update", index_name);
            let key_type: Vec<_> = index
                .mode
                .iter()
                .zip(rel.fields.iter())
                .filter_map(|(mode, ty)| match mode {
                    IndexMode::Bound => Some(ty),
                    IndexMode::Free => None,
                })
                .collect();
            quote! {
                let mut #index_name:
                    ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_name>> =
                    ::std::collections::HashMap::new();
                let mut #index_name_update:
                    ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_name>> =
                    ::std::collections::HashMap::new();
            }
        });
        let load_inputs = context.rels_input.values().map(|rel| {
            let lower = to_lowercase(&rel.name);
            let var_update = format_ident!("__{}_update", lower);
            quote! {
                #var_update.extend(&self.#lower);
            }
        });
        init_rels
            .chain(init_indices)
            .chain(load_inputs)
            .collect::<proc_macro2::TokenStream>()
    };

    let output = {
        let output_fields: proc_macro2::TokenStream = context
            .rels_output
            .values()
            .map(|rel| {
                let lower = to_lowercase(&rel.name);
                let var_name = format_ident!("__{}", lower);
                quote! {
                    #lower: #var_name.into_iter().collect(),
                }
            })
            .collect();

        quote! {
            CrepeOutput {
                #output_fields
            }
        }
    };

    quote! {
        fn run(&self) -> CrepeOutput {
            #initialize
            #main_loop
            #output
        }
    }
}

fn make_rule(rule: &Rule, indices: &mut HashSet<Index>) -> proc_macro2::TokenStream {
    let goal = {
        let relation = &rule.goal.relation;
        let fields = &rule.goal.fields;
        let name = format_ident!("__{}", to_lowercase(relation));
        let name_new = format_ident!("__{}_new", to_lowercase(relation));
        quote! {
            let __crepe_goal = #relation(#fields);
            if !#name.contains(&__crepe_goal) {
                #name_new.insert(__crepe_goal);
            }
        }
    };
    let fact_positions: Vec<_> = rule
        .clauses
        .iter()
        .enumerate()
        .filter_map(|(i, clause)| match clause {
            Clause::Fact(_) => Some(i),
            Clause::Expr(_) => None,
        })
        .collect();
    if fact_positions.is_empty() {
        // Purely an expression, so we only need to evaluate it once
        let mut datalog_vars: HashSet<String> = HashSet::new();
        let fragments: Vec<_> = rule
            .clauses
            .iter()
            .cloned()
            .map(|clause| make_clause(clause, false, &mut datalog_vars, indices))
            .collect();
        let eval_loop = fragments.into_iter().rev().fold(goal, |x, f| f(x));
        quote! {
            if __crepe_first_iteration {
                #eval_loop
            }
        }
    } else {
        // Rule has one or more facts, so we use semi-naive evaluation
        let mut variants = Vec::new();
        for update_position in fact_positions {
            let mut datalog_vars: HashSet<String> = HashSet::new();
            let fragments: Vec<_> = rule
                .clauses
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, clause)| {
                    make_clause(clause, update_position == i, &mut datalog_vars, indices)
                })
                .collect();
            let eval_loop = fragments.into_iter().rev().fold(goal.clone(), |x, f| f(x));
            variants.push(eval_loop);
        }
        variants.into_iter().collect()
    }
}

type QuoteWrapper = dyn Fn(proc_macro2::TokenStream) -> proc_macro2::TokenStream;

fn make_clause(
    clause: Clause,
    only_update: bool,
    datalog_vars: &mut HashSet<String>,
    indices: &mut HashSet<Index>,
) -> Box<QuoteWrapper> {
    match clause {
        Clause::Fact(fact) => {
            let name = &fact.relation;
            let mut setters = Vec::new();
            let mut index_mode = Vec::new();
            for (i, field) in fact.fields.iter().enumerate() {
                let idx = syn::Index::from(i);
                if let Some(var) = is_datalog_var(field) {
                    let var_name = var.to_string();
                    if datalog_vars.contains(&var_name) {
                        index_mode.push(IndexMode::Bound);
                    } else {
                        index_mode.push(IndexMode::Free);
                        datalog_vars.insert(var_name);
                        setters.push(quote! {
                            let #field = __crepe_var.#idx;
                        });
                    }
                } else {
                    index_mode.push(IndexMode::Bound);
                }
            }
            let setters: proc_macro2::TokenStream = setters.into_iter().collect();

            if !index_mode.contains(&IndexMode::Bound) {
                let mut rel = format_ident!("__{}", &to_lowercase(name));
                if only_update {
                    rel = format_ident!("{}_update", rel);
                }
                // If no fields are bound, we don't need an index
                Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        for __crepe_var in #rel.iter() {
                            #setters
                            #body
                        }
                    }
                })
            } else {
                // Otherwise, we're going to need an index!
                let bound_fields: Vec<_> = index_mode
                    .iter()
                    .zip(fact.fields.iter())
                    .filter_map(|(mode, field)| match mode {
                        IndexMode::Bound => Some(field.clone()),
                        IndexMode::Free => None,
                    })
                    .collect();
                let index = Index {
                    name: name.to_string(),
                    mode: index_mode,
                };
                let mut index_name = Ident::new(&index.to_string(), name.span());
                if only_update {
                    index_name = format_ident!("{}_update", index_name);
                }
                indices.insert(index);
                Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        if let Some(__crepe_iter) = #index_name.get(&(#(#bound_fields,)*)) {
                            for &__crepe_var in __crepe_iter.iter() {
                                #setters
                                #body
                            }
                        }
                    }
                })
            }
        }
        Clause::Expr(expr) => {
            assert!(!only_update);
            Box::new(move |body| {
                quote! {
                    #[allow(unused_parens)]
                    if #expr { #body }
                }
            })
        }
    }
}

fn make_output_decl(context: &Context) -> proc_macro2::TokenStream {
    let fields: proc_macro2::TokenStream = context
        .rels_output
        .values()
        .map(|relation| {
            let name = &relation.name;
            let lower = to_lowercase(name);
            quote! {
                #lower: ::std::vec::Vec<#name>,
            }
        })
        .collect();

    quote! {
        struct CrepeOutput {
            #fields
        }
    }
}

/// Returns whether an expression in a relation is a Datalog variable.
///
/// - `is_datalog_var(x) => Some(Ident("x"))`
/// - `is_datalog_var(_helloWorld) => Some(Ident("_helloWorld"))`
/// - `is_datalog_var(x + y) => None`
/// - `is_datalog_var(StartsWithCapitalLetter) => None`
/// - `is_datalog_var(true) => None`
fn is_datalog_var(expr: &Expr) -> Option<Ident> {
    use syn::{ExprPath, Path, PathArguments};
    match expr {
        Expr::Path(ExprPath {
            attrs,
            qself: None,
            path:
                Path {
                    leading_colon: None,
                    segments,
                },
        }) => {
            if attrs.is_empty() && segments.len() == 1 {
                let segment = segments.iter().next()?;
                if let PathArguments::None = segment.arguments {
                    let ident = segment.ident.clone();
                    match ident.to_string().chars().next() {
                        Some('a'..='z') | Some('_') => return Some(ident),
                        _ => (),
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Converts an `Ident` to lowercase, with the same `Span`
fn to_lowercase(name: &Ident) -> Ident {
    let s = name.to_string().to_lowercase();
    Ident::new(&s, name.span())
}
