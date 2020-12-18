//! Crepe is a library that allows you to write declarative logic programs in
//! Rust, with a [Datalog](https://en.wikipedia.org/wiki/Datalog)-like syntax.
//! It provides a procedural macro that generates efficient, safe code and
//! interoperates seamlessly with Rust programs.
//!
//! # Documentation
//! See the [`crepe!`](macro.crepe.html) macro for detailed documentation.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate proc_macro;

mod parse;
mod strata;

use proc_macro::TokenStream;
use proc_macro_error::{abort, emit_error, proc_macro_error};
use quote::{format_ident, quote, quote_spanned};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use syn::{parse_macro_input, spanned::Spanned, Expr, Ident, Lifetime, Type};

use parse::{Clause, Fact, FactField, Program, Relation, RelationType, Rule};
use strata::Strata;

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
///         let mut runtime = Crepe::new();
///         runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
///         let (tc,) = runtime.run();
///         tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
///     }
/// }
/// # fn main() {}
/// ```
///
/// # Generated Code
/// Each `struct` in the program is turned into a Datalog relation, while each
/// line of the form `goal <- clause1, clause2, ...;` or `fact;` defines a
/// logic programming rule that is used to derive new relations.
///
/// In addition to the relation structs, the macro also defines a `Crepe`
/// struct representing the runtime. This is the primary way that you interact
/// with Crepe. It provides a couple methods and traits (here `Rel` is a
/// placeholder for the name of your relation):
///
/// - `Crepe::new()`: construct a new runtime
/// - Implements `std::iter::Extend<Rel>` for each @input struct.
///   - `Crepe::extend(&mut self, iter: impl IntoIterator<Item = Rel>)`
/// - Implements `std::iter::Extend<&'a Rel>` for each @input struct.
///   - `Crepe::extend(&mut self, iter: impl IntoIterator<Item = &'a Rel>)`
/// - `Crepe::run(self)`: evaluates the Datalog program on the given inputs,
///   consuming the runtime object, and returns a tuple of `HashSet<Rel>`s
///   containing the final derived @output structs.
///
/// In order for the engine to work, all relations must be tuple structs, and
/// they automatically derive the `Eq`, `PartialEq`, `Hash`, `Copy`, and
/// `Clone` traits. This is necessary in order to create efficient indices that
/// are used in Datalog evaluation. If you want to use Crepe with types that
/// do not implement `Copy`, consider passing references instead.
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
///     Fib(1, 1); // shorthand for `Fib(1, 1) <- (true);`
///
///     Fib(n + 2, x + y) <- Fib(n, x), Fib(n + 1, y), (n + 2 <= 25);
/// }
/// #     pub fn run() -> Vec<(u32, u32)> {
/// #         let (fib,) = Crepe::new().run();
/// #         let mut output: Vec<_> = fib.into_iter().map(|Fib(x, y)| (x, y)).collect();
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
/// We also support let-bindings in rules, including bindings that destructure
/// their arguments conditionally. See `tests/test_destructure.rs` for an
/// example of this.
///
/// # Evaluation Mode
/// All generated code uses semi-naive evaluation (see Chapter 3 of _Datalog
/// and Recursive Query Processing_), and it is split into multiple strata to
/// enable stratified negation. For example, we can extend the first example to
/// also compute the complement of transitive closure in a graph:
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
///         struct Node(i32);
///
///         @output
///         struct NotTc(i32, i32);
///
///         Tc(x, y) <- Edge(x, y);
///         Tc(x, z) <- Edge(x, y), Tc(y, z);
///
///         Node(x) <- Edge(x, _);
///         Node(x) <- Edge(_, x);
///         NotTc(x, y) <- Node(x), Node(y), !Tc(x, y);
///     }
///
///     pub fn run(edges: &[(i32, i32)]) -> (Vec<(i32, i32)>, Vec<(i32, i32)>) {
///         let mut runtime = Crepe::new();
///         runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
///         let (tc, not_tc) = runtime.run();
///         (
///             tc.into_iter().map(|Tc(a, b)| (a, b)).collect(),
///             not_tc.into_iter().map(|NotTc(a, b)| (a, b)).collect(),
///         )
///     }
/// }
/// # fn main() {}
/// ```
///
/// # Lifetimes and Attributes
/// This macro allows you to specify attributes, visibility modifiers, and
/// lifetimes on the relation structs. These can include additional `derive`
/// attributes, and lifetimes can be used to construct relations that include
/// non-owning references. The following example computes suffixes of words.
/// ```
/// use crepe::crepe;
///
/// crepe! {
///     @input
///     struct Word<'a>(&'a str);
///
///     @output
///     #[derive(Debug)]
///     struct Suffix<'a>(&'a str);
///
///     Suffix(w) <- Word(w);
///     Suffix(&w[1..]) <- Suffix(w), (!w.is_empty());
/// }
///
/// fn main() {
///     let mut runtime = Crepe::new();
///     runtime.extend(&[Word("banana"), Word("bandana")]);
///     let (suffixes,) = runtime.run();
///     println!("{:?}", suffixes);
/// }
/// ```
///
/// # Hygiene
/// In addition to the relation structs, this macro generates implementations
/// of a private struct named `Crepe` for the runtime. Therefore, it is
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

    let expanded = quote! {
        #struct_decls
        #runtime_decl
        #runtime_impl
    };

    expanded.into()
}

/// Function that takes a `TokenStream` as input, and returns a `TokenStream`
type QuoteWrapper = dyn Fn(proc_macro2::TokenStream) -> proc_macro2::TokenStream;

type NumLifetimes = usize;

/// Intermediate representation for Datalog compilation
struct Context {
    has_input_lifetime: bool,
    rels_input: HashMap<String, Relation>,
    rels_output: HashMap<String, Relation>,
    output_order: Vec<(Ident, NumLifetimes)>,
    rels_intermediate: HashMap<String, Relation>,
    rules: Vec<Rule>,
    strata: Strata,
}

impl Context {
    fn new(program: Program) -> Self {
        // Read in relations, ensure no duplicates
        let mut rels_input = HashMap::new();
        let mut rels_output = HashMap::new();
        let mut rels_intermediate = HashMap::new();
        let mut rel_names = HashSet::new();
        let mut output_order = Vec::new();

        let mut has_input_lifetime = false;
        let mut has_non_input_lifetime = false;

        program.relations.into_iter().for_each(|relation| {
            let name = relation.name.to_string();
            if !rel_names.insert(relation.name.clone()) {
                abort!(relation.name.span(), "Duplicate relation name: {}", name);
            }

            if let Some(t) = relation.generics.type_params().next() {
                abort!(t.span(), "Type parameters are not supported in relations");
            }
            if let Some(c) = relation.generics.const_params().next() {
                abort!(c.span(), "Const parameters are not supported in relations");
            }
            let num_lifetimes = relation.generics.lifetimes().count();

            match relation.relation_type() {
                Ok(RelationType::Input) => {
                    rels_input.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_input_lifetime = true;
                    }
                }
                Ok(RelationType::Output) => {
                    output_order.push((relation.name.clone(), num_lifetimes));
                    rels_output.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_non_input_lifetime = true;
                    }
                }
                Ok(RelationType::Intermediate) => {
                    if num_lifetimes > 0 {
                        has_non_input_lifetime = true;
                    }
                    rels_intermediate.insert(name, relation);
                }
                Err(attr) => {
                    abort!(
                        attr.span(),
                        "Invalid attribute @{}, expected '@input' or '@output'",
                        attr
                    )
                }
            }
        });

        // all lifetimes currently are set to the input lifetime, so one needs to
        // be present somewhere
        if has_non_input_lifetime && !has_input_lifetime {
            // This should be the exception (assuming most crepe programs are
            // well "lifetimed") so for all structs that have lifetimes but
            // should not have one, an error gets emitted

            for r in rels_output.values() {
                if r.generics.lifetimes().next().is_some() {
                    emit_error!(
                        r.generics,
                        "Lifetime on output relation without any input relations having a lifetime"
                    );
                }
            }
        }

        // Read in rules, ensuring that there are no undefined relations, or
        // relations declared with incorrect arity.
        //
        // Also generate dependency edges between relations for stratification.
        let mut dependencies = HashSet::new();
        let check = |fact: &Fact| {
            let name = fact.relation.to_string();
            if !rel_names.contains(&fact.relation) {
                abort!(
                    fact.relation.span(),
                    "Relation name '{}' was not found. Did you misspell it?",
                    name
                );
            }
            let rel = rels_input
                .get(&name)
                .or_else(|| rels_output.get(&name))
                .or_else(|| rels_intermediate.get(&name))
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
            if rule
                .goal
                .fields
                .iter()
                .any(|f| matches!(f, FactField::Ignored(_)))
            {
                abort!(
                    rule.goal.relation.span(),
                    "Cannot have _ in goal atom of rule."
                )
            }
            if rule
                .goal
                .fields
                .iter()
                .any(|f| matches!(f, FactField::Ref(_, _)))
            {
                abort!(
                    rule.goal.relation.span(),
                    "Cannot have `ref` in goal atom of rule."
                )
            }
            rule.clauses.iter().for_each(|clause| {
                if let Clause::Fact(fact) = clause {
                    check(&fact);
                    dependencies.insert((&rule.goal.relation, &fact.relation));
                }
            });
        });

        // Now we can stratify the relations
        let strata = Strata::new(rel_names, dependencies);

        // Check for dependency cycles in datalog negations
        for rule in &program.rules {
            let goal_stratum = strata.find_relation(&rule.goal.relation);
            for clause in &rule.clauses {
                if let Clause::Fact(fact) = clause {
                    if fact.negate.is_some() {
                        let fact_stratum = strata.find_relation(&fact.relation);
                        if goal_stratum == fact_stratum {
                            abort!(
                                fact.relation.span(),
                                "Negation of relation '{}' creates a dependency cycle \
                                and cannot be stratified.",
                                fact.relation
                            );
                        }
                        // This should be guaranteed by reverse topological order
                        assert!(goal_stratum > fact_stratum);
                    }
                }
            }
        }

        // If all the relations are OK, we simply update the rules as-is.
        //
        // There's no need to do complex parsing logic yet; we can work that
        // out when we actually generate the runtime code, since that's
        // context-sensitive logic.
        let rules = program.rules;
        Self {
            has_input_lifetime,
            rels_input,
            rels_output,
            output_order,
            rels_intermediate,
            rules,
            strata,
        }
    }

    fn get_relation(&self, name: &str) -> Option<&Relation> {
        self.rels_input
            .get(name)
            .or_else(|| self.rels_intermediate.get(name))
            .or_else(|| self.rels_output.get(name))
    }

    fn is_input_relation(&self, name: &Ident) -> bool {
        self.rels_input.contains_key(name.to_string().as_str())
    }

    fn input_relations(&self) -> impl Iterator<Item = &Relation> {
        self.rels_input.values()
    }

    fn non_input_relations(&self) -> impl Iterator<Item = &Relation> {
        self.rels_intermediate
            .values()
            .chain(self.rels_output.values())
    }

    fn all_relations(&self) -> impl Iterator<Item = &Relation> {
        self.rels_input
            .values()
            .chain(self.rels_intermediate.values())
            .chain(self.rels_output.values())
    }
}

#[derive(Eq, PartialEq, Hash, Copy, Clone)]
enum IndexMode {
    Bound,
    Free,
}

#[derive(Eq, PartialEq, Hash, Clone)]
struct Index {
    name: Ident,
    mode: Vec<IndexMode>,
}

impl Index {
    fn to_ident(&self) -> Ident {
        Ident::new(&self.to_string(), self.name.span())
    }

    fn key_type<'a>(&self, context: &'a Context) -> Vec<&'a Type> {
        let rel = context
            .get_relation(&self.name.to_string())
            .expect("could not find relation of index name");
        self.mode
            .iter()
            .zip(rel.fields.iter())
            .filter_map(|(mode, field)| match mode {
                IndexMode::Bound => Some(&field.ty),
                IndexMode::Free => None,
            })
            .collect()
    }

    fn bound_pos(&self) -> Vec<syn::Index> {
        self.mode
            .iter()
            .enumerate()
            .filter_map(|(i, mode)| match mode {
                IndexMode::Bound => Some(syn::Index::from(i)),
                IndexMode::Free => None,
            })
            .collect()
    }
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
        write!(f, "__{}_index{}", to_lowercase(&self.name), mode)
    }
}

fn make_struct_decls(context: &Context) -> proc_macro2::TokenStream {
    context
        .all_relations()
        .map(|relation| {
            let attrs = &relation.attrs;
            let struct_token = &relation.struct_token;
            let vis = &relation.visibility;
            let name = &relation.name;
            let generics = &relation.generics;
            let semi_token = &relation.semi_token;
            let fields = &relation.fields;
            quote_spanned! {name.span()=>
                #[derive(
                    ::core::marker::Copy,
                    ::core::clone::Clone,
                    ::core::cmp::Eq,
                    ::core::cmp::PartialEq,
                    ::core::hash::Hash,
                )]
                #(#attrs)*
                #vis #struct_token #name #generics (#fields)#semi_token
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
//     fn run(self) -> Output {
//         // core logic here
//     }
// }
// impl ::core::iter::Extend<Edge> for Crepe {
//     fn extend<T>(&mut self, iter: T)
//     where
//         T: ::core::iter::IntoIterator<Item = Edge>,
//     {
//         self.edge.extend(iter);
//     }
// }
// ```

fn make_runtime_decl(context: &Context) -> proc_macro2::TokenStream {
    let fields: proc_macro2::TokenStream = context
        .rels_input
        .values()
        .map(|relation| {
            // because the generics have been validated to only contain lifetimes
            // no further checking is done here.
            let rel_ty = relation_type(&relation, LifetimeUsage::Item);
            let lowercase_name = to_lowercase(&relation.name);
            quote! {
                #lowercase_name: ::std::vec::Vec<#rel_ty>,
            }
        })
        .collect();

    let lifetime = lifetime(context.has_input_lifetime);

    quote! {
        #[derive(::core::default::Default)]
        struct Crepe #lifetime {
            #fields
        }
    }
}

fn make_runtime_impl(context: &Context) -> proc_macro2::TokenStream {
    let builders = make_extend(&context);
    let run = make_run(&context);

    let lifetime = lifetime(context.has_input_lifetime);

    quote! {
        impl #lifetime Crepe #lifetime {
            fn new() -> Self {
                ::core::default::Default::default()
            }
            #run
        }
        #builders
    }
}

fn make_extend(context: &Context) -> proc_macro2::TokenStream {
    context
        .rels_input
        .values()
        .map(|relation| {
            let rel_ty = relation_type(&relation, LifetimeUsage::Item);
            let lifetime = lifetime(context.has_input_lifetime);
            let lower = to_lowercase(&relation.name);
            quote! {
                impl #lifetime ::core::iter::Extend<#rel_ty> for Crepe #lifetime {
                    fn extend<T>(&mut self, iter: T)
                    where
                        T: ::core::iter::IntoIterator<Item = #rel_ty>,
                    {
                        self.#lower.extend(iter);
                    }
                }
                impl<'a> ::core::iter::Extend<&'a #rel_ty> for Crepe #lifetime {
                    fn extend<T>(&mut self, iter: T)
                    where
                        T: ::core::iter::IntoIterator<Item = &'a #rel_ty>,
                    {
                        self.extend(iter.into_iter().copied());
                    }
                }
            }
        })
        .collect()
}

/// This is the primary method, which consumes the builder. It should compile
/// declarative Datalog into imperative logic to generate facts, essentially
/// what we signed up for!
///
/// Here's an example of what might be generated for transitive closure:
/// ```ignore
/// fn run_with_hasher<S: BuildHasher + Default>(self) -> (::std::collections::HashSet<Tc, S>,) {
///     // Relations
///     let mut __edge: ::std::collections::HashSet<Edge, S> = ::std::collections::HashSet::default();
///     let mut __edge_update: ::std::collections::HashSet<Edge, S> = ::std::collections::HashSet::default();
///     let mut __tc: ::std::collections::HashSet<Tc, S> = ::std::collections::HashSet::default();
///     let mut __tc_update: ::std::collections::HashSet<Tc, S> = ::std::collections::HashSet::default();
///
///     // Indices
///     let mut __tc_index_bf: ::std::collections::HashMap<(i32,), ::std::vec::Vec<Tc>, S> =
///         ::std::collections::HashMap::default();
///
///     // Input relations
///     __edge_update.extend(self.edge);
///
///     // Main loop, single stratum for simplicity
///     let mut __crepe_first_iteration = true;
///     while __crepe_first_iteration || !(__edge_update.is_empty() && __tc_update.is_empty()) {
///         __tc.extend(&__tc_update);
///         for ref __crepe_var_ref in __tc_update.iter() {
///             let __crepe_var = *__crepe_var_ref;
///             __tc_index_bf.entry((__crepe_var.0,)).or_default().push(*__crepe_var);
///         }
///         __edge.extend(&__edge_update);
///
///         let mut __tc_new: ::std::collections::HashSet<Tc, S> = ::std::collections::HashSet::default();
///         let mut __edge_new: ::std::collections::HashSet<Tc, S> = ::std::collections::HashSet::default();
///
///         for ref __crepe_var_0 in __edge.iter() {
///             let x = __crepe_var_0.0;
///             let y = __crepe_var_0.1;
///             let __crepe_goal = Tc(x, y);
///             if !__tc.contains(__crepe_goal) {
///                 __tc_new.insert(*__crepe_goal);
///             }
///         }
///
///         for ref __crepe_var_0 in __edge.iter() {
///             let x = __crepe_var_0.0;
///             let y = __crepe_var_0.1;
///             if let Some(__iter_1) = __tc_index_bf.get(&(y,)) {
///                 for ref __crepe_var_1 in __iter_1.iter() {
///                     let z = __crepe_var_1.1;
///                     let __crepe_goal = Tc(x, z);
///                     if !__tc.contains(__crepe_goal) {
///                         __tc_new.insert(*__crepe_goal);
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
///     (__tc,)
/// }
/// ```
/// Please note that this example uses naive evaluation for simplicity, but we
/// actually generate code for semi-naive evaluation.
fn make_run(context: &Context) -> proc_macro2::TokenStream {
    let mut indices: HashSet<Index> = HashSet::new();

    let main_loops = {
        let mut loop_wrappers = Vec::new();
        for stratum in context.strata.iter() {
            loop_wrappers.push(make_stratum(context, stratum, &mut indices));
        }
        loop_wrappers
            .iter()
            .zip(context.strata.iter())
            .map(|(f, stratum)| f(make_updates(context, stratum, &indices)))
            .collect::<proc_macro2::TokenStream>()
    };

    let initialize = {
        let input_rels = context.input_relations().map(|rel| {
            let rel_ty = relation_type(&rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let var = format_ident!("__{}", lower);
            quote! {
                let mut #var: ::std::collections::HashSet<#rel_ty> =self.#lower.into_iter().collect();
            }
        });

        let init_rels = context.non_input_relations().map(|rel| {
            let rel_ty = relation_type(&rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let var = format_ident!("__{}", lower);
            let var_update = format_ident!("__{}_update", lower);

            quote! {
                let mut #var: ::std::collections::HashSet<#rel_ty, S> =
                    ::std::collections::HashSet::default();
                let mut #var_update: ::std::collections::HashSet<#rel_ty, S> =
                    ::std::collections::HashSet::default();
            }
        });
        let init_indices = indices.iter().map(|index| {
            let rel = context
                .get_relation(&index.name.to_string())
                .expect("index relation should be found in context");
            let rel_ty = relation_type(&rel, LifetimeUsage::Local);
            let index_name = index.to_ident();
            let key_type = index.key_type(context);

            quote! {
                let mut #index_name:
                    ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_ty>, S> =
                    ::std::collections::HashMap::default();
            }
        });

        input_rels
            .chain(init_rels)
            .chain(init_indices)
            .collect::<proc_macro2::TokenStream>()
    };

    let output = {
        let output_fields = context.output_order.iter().map(|(name, _)| {
            let lower = to_lowercase(name);
            format_ident!("__{}", lower)
        });
        quote! {
            (#(#output_fields,)*)
        }
    };

    let output_ty_hasher = make_output_ty(&context, quote! { S });
    let output_ty_default = make_output_ty(&context, quote! {});
    quote! {
        fn run_with_hasher<S: ::std::hash::BuildHasher + Default>(self) -> #output_ty_hasher {
            #initialize
            #main_loops
            #output
        }

        fn run(self) -> #output_ty_default {
            self.run_with_hasher::<::std::collections::hash_map::RandomState>()
        }
    }
}

fn make_stratum(
    context: &Context,
    stratum: &[Ident],
    indices: &mut HashSet<Index>,
) -> Box<QuoteWrapper> {
    let stratum: HashSet<_> = stratum.iter().collect();
    let current_rels: Vec<_> = stratum
        .iter()
        .map(|name| {
            context
                .get_relation(&name.to_string())
                .expect("cannot find relation from stratum")
        })
        .collect();

    let empty_cond: proc_macro2::TokenStream = current_rels
        .iter()
        .filter_map(|rel| {
            if rel.relation_type() == Ok(RelationType::Input) {
                return None;
            }
            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            Some(quote! {
                #rel_update.is_empty() &&
            })
        })
        .chain(std::iter::once(quote! {true}))
        .collect();

    let new_decls: proc_macro2::TokenStream = current_rels
        .iter()
        .filter_map(|rel| {
            if rel.relation_type() == Ok(RelationType::Input) {
                return None;
            }
            let rel_ty = relation_type(&rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let rel_new = format_ident!("__{}_new", lower);
            Some(quote! {
                let mut #rel_new: ::std::collections::HashSet<#rel_ty, S> =
                    ::std::collections::HashSet::default();
            })
        })
        .collect();

    let rules: proc_macro2::TokenStream = context
        .rules
        .iter()
        .filter(|rule| stratum.contains(&rule.goal.relation))
        .map(|rule| make_rule(rule, &stratum, indices))
        .collect();

    let set_update_to_new: proc_macro2::TokenStream = current_rels
        .iter()
        .filter_map(|rel| {
            if rel.relation_type() == Ok(RelationType::Input) {
                return None;
            }

            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            let rel_new = format_ident!("__{}_new", lower);
            Some(quote! {
                #rel_update = #rel_new;
            })
        })
        .collect();

    // We can only compute the updates later, when all indices are known
    Box::new(move |updates| {
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
    })
}

fn make_updates(
    context: &Context,
    stratum: &[Ident],
    indices: &HashSet<Index>,
) -> proc_macro2::TokenStream {
    let rel_updates = stratum.iter().filter_map(|name| {
        if context.is_input_relation(name) {
            return None;
        }

        let lower = to_lowercase(name);
        let rel = format_ident!("__{}", lower);
        let rel_update = format_ident!("__{}_update", lower);
        Some(quote! {
            #rel.extend(&#rel_update);
        })
    });
    let index_updates = indices.iter().filter_map(|index| {
        if !stratum.contains(&index.name) {
            return None;
        }

        let rel = context
            .get_relation(&index.name.to_string())
            .expect("index relation should be found in context");

        if rel.relation_type() == Ok(RelationType::Input) {
            return None;
        }

        let rel_ty = relation_type(&rel, LifetimeUsage::Local);
        let rel_update = format_ident!("__{}_update", to_lowercase(&rel.name));

        let index_name = index.to_ident();
        let index_name_update = format_ident!("{}_update", index_name);
        let key_type = index.key_type(context);
        let bound_pos = index.bound_pos();
        Some(quote! {
            let mut #index_name_update:
                ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_ty>, S> =
                ::std::collections::HashMap::default();
            for ref __crepe_var_ref in #rel_update.iter() {
                let __crepe_var = *__crepe_var_ref;
                #index_name
                    .entry((#(__crepe_var.#bound_pos,)*))
                    .or_default()
                    .push(*__crepe_var);
                #index_name_update
                    .entry((#(__crepe_var.#bound_pos,)*))
                    .or_default()
                    .push(*__crepe_var);
            }
        })
    });
    rel_updates.chain(index_updates).collect()
}

fn make_rule(
    rule: &Rule,
    stratum: &HashSet<&Ident>,
    indices: &mut HashSet<Index>,
) -> proc_macro2::TokenStream {
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
            Clause::Fact(fact) => {
                if stratum.contains(&fact.relation) {
                    Some(i)
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();
    if fact_positions.is_empty() {
        // Will not change, so we only need to evaluate it once
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

fn make_clause(
    clause: Clause,
    only_update: bool,
    datalog_vars: &mut HashSet<String>,
    indices: &mut HashSet<Index>,
) -> Box<QuoteWrapper> {
    match clause {
        Clause::Fact(fact) => {
            let name = &fact.relation;
            if fact.negate.is_some() {
                // Special case: stratified negation, needs to be handled separately
                assert!(!only_update);
                let to_mode = |f: &FactField| match f {
                    FactField::Ignored(_) => IndexMode::Free,
                    FactField::Ref(_, ident) => {
                        abort!(ident, "Unable to bind values in negated clause")
                    }
                    FactField::Expr(_) => IndexMode::Bound,
                };
                let index = Index {
                    name: name.clone(),
                    mode: fact.fields.iter().map(to_mode).collect(),
                };
                let index_name = index.to_ident();
                indices.insert(index);
                let bound_fields: Vec<_> = fact
                    .fields
                    .iter()
                    .filter(|t| matches!(t, FactField::Expr(_)))
                    .cloned()
                    .collect();
                return Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        if !#index_name.contains_key(&(#(#bound_fields,)*)) {
                            #body
                        }
                    }
                });
            }
            let mut setters = Vec::new();
            let mut index_mode = Vec::new();
            for (i, field) in fact.fields.iter().enumerate() {
                let idx = syn::Index::from(i);
                match field {
                    FactField::Ignored(_) => index_mode.push(IndexMode::Free),
                    FactField::Ref(_, ident) => {
                        index_mode.push(IndexMode::Free);
                        datalog_vars.insert(ident.to_string());
                        setters.push(quote! {
                            let #ident = &__crepe_var_ref.#idx;
                        });
                    }
                    FactField::Expr(expr) => {
                        if let Some(var) = is_datalog_var(expr) {
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
                        for ref __crepe_var_ref in #rel.iter() {
                            let __crepe_var = *__crepe_var_ref;
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
                    name: name.clone(),
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
                            for ref __crepe_var_ref in __crepe_iter.iter() {
                                let __crepe_var = *__crepe_var_ref;
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
        Clause::Let(guard) => {
            assert!(!only_update);
            Box::new(move |body| {
                quote! {
                    #[allow(irrefutable_let_patterns)]
                    if #guard { #body }
                }
            })
        }
    }
}

fn make_output_ty(context: &Context, hasher: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let fields = context.output_order.iter().map(|(name, num_lifetimes)| {
        let lifetimes = (0..*num_lifetimes).map(|_| quote! { 'a });
        quote! { #name < #(#lifetimes),* > }
    });

    quote! {
        (#(::std::collections::HashSet<#fields, #hasher>,)*)
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

/// Create a tokenstream for a lifetime bound/application if it's needed
fn lifetime(needs_lifetime: bool) -> proc_macro2::TokenStream {
    if needs_lifetime {
        quote! { <'a> }
    } else {
        quote! {}
    }
}

enum LifetimeUsage {
    Item,
    Local,
}

/// Returns the type of a relation, with lifetimes set to 'a
fn relation_type(rel: &Relation, usage: LifetimeUsage) -> proc_macro2::TokenStream {
    let symbol = match rel.relation_type().unwrap() {
        RelationType::Input | RelationType::Output => "'a",
        RelationType::Intermediate => match usage {
            LifetimeUsage::Item => "'a",
            LifetimeUsage::Local => "'_",
        },
    };

    let name = &rel.name;
    let lifetimes = rel
        .generics
        .lifetimes()
        .map(|l| Lifetime::new(symbol, l.span()))
        .collect::<Vec<_>>();
    quote! { #name<#(#lifetimes),*> }
}
