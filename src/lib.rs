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
use syn::{parse_macro_input, spanned::Spanned, Expr, Ident, Lifetime, Pat, Type};

use parse::{Clause, Fact, FactField, For, Program, Relation, RelationType, Rule};
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
/// - `Crepe::run_with_hasher::<S: BuildHasher + Default>(self)`: similar to the
///   `run` method, but internally uses a custom hasher.
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
/// ```
/// # use crepe::crepe;
/// crepe! {
///     @input
///     struct Value<'a>(&'a str);
///
///     @output
/// #   #[derive(Debug)]
///     struct Squared(i32, i32);
///
///     Squared(n, x) <-
///         Value(string),
///         let Ok(n) = string.parse(),
///         let x = n * n;
/// }
/// # fn main() {
/// #     let mut rt = Crepe::new();
/// #     rt.extend([Value("hello"), Value("42")]);
/// #     let (squared,) = rt.run();
/// #     assert_eq!(squared.into_iter().collect::<Vec<_>>(), [Squared(42, 1764)]);
/// # }
/// ```
/// The last built-in control flow feature is iteration over data. Rules can
/// enumerate values from an iterator, allowing them to use data from outside of
/// Crepe without having to convert functions to use work-arounds. For example,
/// to access the characters of a string, you could write:
/// ```
/// # use crepe::crepe;
/// crepe! {
///     @input
///     struct Name<'a>(&'a str);
///
///     @output
///     struct NameContainsLetter<'a>(&'a str, char);
///
///     NameContainsLetter(name, letter) <- Name(name), for letter in name.chars();
/// }
/// ```
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
///     runtime.extend([Word("banana"), Word("bandana")]);
///     let (suffixes,) = runtime.run();
///     println!("{:?}", suffixes);
/// }
/// ```
/// We also support the `ref` keyword for binding a variable by reference rather
/// than copying it, which can improve performance in some cases.
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

/// Intermediate representation for Datalog compilation
struct Context {
    has_input_lifetime: bool,
    rels_input: HashMap<String, Relation>,
    rels_output: HashMap<String, Relation>,
    output_order: Vec<Ident>,
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
        let mut has_output_lifetime = false;

        program.relations.into_iter().for_each(|relation| {
            let name = relation.name.to_string();
            if !rel_names.insert(relation.name.clone()) {
                abort!(relation.name.span(), "Duplicate relation name: {}", name);
            }

            // Validate generic parameters
            validate_generic_params(&relation);
            
            let num_lifetimes = relation.generics.lifetimes().count();

            match relation.relation_type() {
                Ok(RelationType::Input) => {
                    rels_input.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_input_lifetime = true;
                    }
                }
                Ok(RelationType::Output) => {
                    output_order.push(relation.name.clone());
                    rels_output.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_output_lifetime = true;
                    }
                }
                Ok(RelationType::Intermediate) => {
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
        if has_output_lifetime && !has_input_lifetime {
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

            for f in &rule.goal.fields {
                match f {
                    FactField::Ignored(token) => {
                        abort!(token.span(), "Cannot have _ in goal atom of rule.")
                    }
                    FactField::Ref(token, _) => {
                        abort!(token.span(), "Cannot have `ref` in goal atom of rule.")
                    }
                    FactField::Expr(_) => (),
                }
            }
            rule.clauses.iter().for_each(|clause| {
                if let Clause::Fact(fact) = clause {
                    check(fact);
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

fn make_runtime_decl(context: &Context) -> proc_macro2::TokenStream {
    let fields: proc_macro2::TokenStream = context
        .rels_input
        .values()
        .map(|relation| {
            let rel_ty = relation_type(relation, LifetimeUsage::Item);
            let lowercase_name = to_lowercase(&relation.name);
            quote! {
                #lowercase_name: ::std::vec::Vec<#rel_ty>,
            }
        })
        .collect();

    let generics_decl = generic_params_decl(context);

    quote! {
        #[derive(::core::default::Default)]
        struct Crepe #generics_decl {
            #fields
        }

        /// Profiling statistics for individual rules
        #[derive(Debug, Clone)]
        pub struct RuleStats {
            /// Rule identifier (goal relation and rule index)
            pub rule_id: String,
            /// Total time spent executing this rule across all iterations
            pub total_duration: ::std::time::Duration,
            /// Number of times this rule was evaluated
            pub eval_count: u64,
            /// Number of new facts generated by this rule
            pub facts_generated: u64,
        }

        impl RuleStats {
            /// Get the average time per evaluation
            pub fn avg_duration(&self) -> ::std::time::Duration {
                if self.eval_count > 0 {
                    self.total_duration / self.eval_count as u32
                } else {
                    ::std::time::Duration::ZERO
                }
            }
        }

        /// Profiling results from a Datalog execution
        #[derive(Debug, Clone, Default)]
        pub struct ProfilingStats {
            /// Statistics for each rule
            pub rules: ::std::vec::Vec<RuleStats>,
            /// Total execution time
            pub total_duration: ::std::time::Duration,
        }

        impl ProfilingStats {
            /// Print a formatted report of rule timings
            pub fn report(&self) {
                println!("\n=== Crepe Profiling Report ===");
                println!("Total execution time: {:?}", self.total_duration);
                println!("\nRule timings (sorted by total duration):");
                
                let mut sorted_rules = self.rules.clone();
                sorted_rules.sort_by(|a, b| b.total_duration.cmp(&a.total_duration));
                
                println!("{:<50} {:>12} {:>12} {:>15} {:>15}", 
                    "Rule", "Total (ms)", "Calls", "Avg (μs)", "Facts Gen.");
                println!("{}", "-".repeat(110));
                
                for rule in &sorted_rules {
                    let total_ms = rule.total_duration.as_secs_f64() * 1000.0;
                    let avg_us = rule.avg_duration().as_secs_f64() * 1_000_000.0;
                    let pct = if self.total_duration.as_nanos() > 0 {
                        (rule.total_duration.as_nanos() as f64 / self.total_duration.as_nanos() as f64) * 100.0
                    } else {
                        0.0
                    };
                    
                    println!("{:<50} {:>10.2}ms {:>12} {:>13.2}μs {:>15}", 
                        rule.rule_id, total_ms, rule.eval_count, avg_us, rule.facts_generated);
                }
                println!();
            }
        }
    }
}

fn make_runtime_impl(context: &Context) -> proc_macro2::TokenStream {
    let builders = make_extend(context);
    let run = make_run(context);

    let generics_decl = generic_params_decl(context);
    let generics_args = generic_params_args(context);

    quote! {
        impl #generics_decl Crepe #generics_args {
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
            let rel_ty = relation_type(relation, LifetimeUsage::Item);
            let generics_decl = generic_params_decl(context);
            let generics_args = generic_params_args(context);
            let lower = to_lowercase(&relation.name);
            
            // For the reference impl, we need to add the lifetime to the existing generics
            let ref_impl_generics = {
                let mut items = vec![quote! { 'a }];
                for tp in collect_generic_params(context) {
                    items.push(merge_bounds_with_required(tp));
                }
                format_generics(items)
            };
            
            quote! {
                impl #generics_decl ::core::iter::Extend<#rel_ty> for Crepe #generics_args {
                    fn extend<__I>(&mut self, iter: __I)
                    where
                        __I: ::core::iter::IntoIterator<Item = #rel_ty>,
                    {
                        self.#lower.extend(iter);
                    }
                }
                impl #ref_impl_generics ::core::iter::Extend<&'a #rel_ty> for Crepe #generics_args {
                    fn extend<__I>(&mut self, iter: __I)
                    where
                        __I: ::core::iter::IntoIterator<Item = &'a #rel_ty>,
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
/// fn run_with_hasher<CrepeHasher: BuildHasher + Default>(
///     self,
/// ) -> (::std::collections::HashSet<Tc, CrepeHasher>,) {
///     // Relations
///     let mut __edge: ::std::collections::HashSet<Edge, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __edge_update: ::std::collections::HashSet<Edge, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __tc: ::std::collections::HashSet<Tc, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __tc_update: ::std::collections::HashSet<Tc, CrepeHasher> =
///         ::std::collections::HashSet::default();
///
///     // Indices
///     let mut __tc_index_bf: ::std::collections::HashMap<
///         (i32,),
///         ::std::vec::Vec<Tc>,
///         CrepeHasher,
///     > = ::std::collections::HashMap::default();
///
///     // Input relations
///     __edge_update.extend(self.edge);
///
///     // Main loop, single stratum for simplicity
///     let mut __crepe_first_iteration = true;
///     while __crepe_first_iteration || !(__edge_update.is_empty() && __tc_update.is_empty()) {
///         __tc.extend(&__tc_update);
///         for __crepe_var in &__tc_update {
///             __tc_index_bf
///                 .entry((__crepe_var.0,))
///                 .or_default()
///                 .push(*__crepe_var);
///         }
///         __edge.extend(&__edge_update);
///
///         let mut __tc_new: ::std::collections::HashSet<Tc, CrepeHasher> =
///             ::std::collections::HashSet::default();
///         let mut __edge_new: ::std::collections::HashSet<Edge, CrepeHasher> =
///             ::std::collections::HashSet::default();
///
///         for __crepe_var in &__edge {
///             let x = __crepe_var.0;
///             let y = __crepe_var.1;
///             let __crepe_goal = Tc(x, y);
///             if !__tc.contains(&__crepe_goal) {
///                 __tc_new.insert(__crepe_goal);
///             }
///         }
///
///         for __crepe_var in &__edge {
///             let x = __crepe_var.0;
///             let y = __crepe_var.1;
///             if let Some(__crepe_iter) = __tc_index_bf.get(&(y,)) {
///                 for __crepe_var in __crepe_iter {
///                     let z = __crepe_var.1;
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
        let init_rels = context.all_relations().map(|rel| {
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let var = format_ident!("__{}", lower);
            let var_update = format_ident!("__{}_update", lower);

            quote! {
                let mut #var: ::std::collections::HashSet<#rel_ty, CrepeHasher> =
                    ::std::collections::HashSet::default();
                let mut #var_update: ::std::collections::HashSet<#rel_ty, CrepeHasher> =
                    ::std::collections::HashSet::default();
            }
        });
        let init_indices = indices.iter().map(|index| {
            let rel = context
                .get_relation(&index.name.to_string())
                .expect("index relation should be found in context");
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let index_name = index.to_ident();
            let key_type = index.key_type(context);

            quote! {
                let mut #index_name:
                    ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_ty>, CrepeHasher> =
                    ::std::collections::HashMap::default();
            }
        });
        let load_inputs = context.rels_input.values().map(|rel| {
            let lower = to_lowercase(&rel.name);
            let var_update = format_ident!("__{}_update", lower);
            quote! {
                #var_update.extend(self.#lower);
            }
        });
        let init_profiling = quote! {
            let mut __crepe_rule_stats: ::std::collections::HashMap<
                String, 
                (::std::time::Duration, u64, u64)
            > = ::std::collections::HashMap::new();
        };
        init_rels
            .chain(init_indices)
            .chain(load_inputs)
            .chain(std::iter::once(init_profiling))
            .collect::<proc_macro2::TokenStream>()
    };

    let finalize_profiling = quote! {
        for (rule_id, (duration, eval_count, facts_generated)) in __crepe_rule_stats {
            __crepe_profiling_stats.rules.push(RuleStats {
                rule_id,
                total_duration: duration,
                eval_count,
                facts_generated,
            });
        }
    };

    let output = {
        let output_fields = context.output_order.iter().map(|name| {
            let lower = to_lowercase(name);
            format_ident!("__{}", lower)
        });
        quote! {
            (#(#output_fields,)*)
        }
    };

    let output_ty_hasher = make_output_ty(context, quote! { CrepeHasher });
    let output_ty_default = make_output_ty(context, quote! {});
    quote! {
        #[allow(clippy::collapsible_if)]
        fn run_with_hasher<CrepeHasher: ::std::hash::BuildHasher + ::core::default::Default>(
            self
        ) -> #output_ty_hasher {
            #initialize
            #main_loops
            #output
        }

        fn run(self) -> #output_ty_default {
            self.run_with_hasher::<::std::collections::hash_map::RandomState>()
        }

        #[allow(clippy::collapsible_if)]
        fn run_with_profiling_and_hasher<CrepeHasher: ::std::hash::BuildHasher + ::core::default::Default>(
            self
        ) -> (#output_ty_hasher, ProfilingStats) {
            let __crepe_total_start = ::std::time::Instant::now();
            let mut __crepe_profiling_stats = ProfilingStats::default();
            
            #initialize
            #main_loops
            #finalize_profiling
            
            __crepe_profiling_stats.total_duration = __crepe_total_start.elapsed();
            __crepe_profiling_stats.report();
            (#output, __crepe_profiling_stats)
        }

        fn run_with_profiling(self) -> (#output_ty_default, ProfilingStats) {
            self.run_with_profiling_and_hasher::<::std::collections::hash_map::RandomState>()
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
        .map(|rel| {
            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            quote! {
                #rel_update.is_empty() &&
            }
        })
        .chain(std::iter::once(quote! {true}))
        .collect();

    let new_decls: proc_macro2::TokenStream = current_rels
        .iter()
        .map(|rel| {
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let rel_new = format_ident!("__{}_new", lower);
            quote! {
                let mut #rel_new: ::std::collections::HashSet<#rel_ty, CrepeHasher> =
                    ::std::collections::HashSet::default();
            }
        })
        .collect();

    let rules: proc_macro2::TokenStream = context
        .rules
        .iter()
        .enumerate()
        .filter(|(_, rule)| stratum.contains(&rule.goal.relation))
        .map(|(rule_idx, rule)| make_rule(rule, rule_idx, &stratum, indices))
        .collect();

    let set_update_to_new: proc_macro2::TokenStream = current_rels
        .iter()
        .map(|rel| {
            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            let rel_new = format_ident!("__{}_new", lower);
            quote! {
                #rel_update = #rel_new;
            }
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
    let rel_updates = stratum.iter().map(|name| {
        let lower = to_lowercase(name);
        let rel = format_ident!("__{}", lower);
        let rel_update = format_ident!("__{}_update", lower);
        quote! {
            #rel.extend(&#rel_update);
        }
    });
    let index_updates = indices.iter().filter_map(|index| {
        if !stratum.contains(&index.name) {
            return None;
        }

        let rel = context
            .get_relation(&index.name.to_string())
            .expect("index relation should be found in context");

        let rel_ty = relation_type(rel, LifetimeUsage::Local);
        let rel_update = format_ident!("__{}_update", to_lowercase(&rel.name));

        let index_name = index.to_ident();
        let index_name_update = format_ident!("{}_update", index_name);
        let key_type = index.key_type(context);
        let bound_pos = index.bound_pos();
        Some(quote! {
            let mut #index_name_update: ::std::collections::HashMap<
                (#(#key_type,)*),
                ::std::vec::Vec<#rel_ty>,
                CrepeHasher
            > = ::std::collections::HashMap::default();
            for __crepe_var in &#rel_update {
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
    rule_idx: usize,
    stratum: &HashSet<&Ident>,
    indices: &mut HashSet<Index>,
) -> proc_macro2::TokenStream {
    let goal_relation_name = rule.goal.relation.to_string();
    let rule_id = format!("{}#{}", goal_relation_name, rule_idx);
    let rule_id_ident = format_ident!("__crepe_rule_{}_{}", to_lowercase(&rule.goal.relation), rule_idx);
    let stats_var = format_ident!("__crepe_stats_{}_{}", to_lowercase(&rule.goal.relation), rule_idx);
    
    let goal = {
        let relation = &rule.goal.relation;
        let fields = &rule.goal.fields;
        let name = format_ident!("__{}", to_lowercase(relation));
        let name_new = format_ident!("__{}_new", to_lowercase(relation));
        quote! {
            let __crepe_goal = #relation(#fields);
            if !#name.contains(&__crepe_goal) {
                #name_new.insert(__crepe_goal);
                #stats_var.2 += 1;
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
    
    let rule_body = if fact_positions.is_empty() {
        // Will not change, so we only need to evaluate it once
        let mut datalog_vars: HashSet<String> = HashSet::new();
        #[allow(clippy::needless_collect)]
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
            #[allow(clippy::needless_collect)]
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
    };
    
    quote! {
        {
            let #stats_var: &mut (::std::time::Duration, u64, u64) = 
                __crepe_rule_stats.entry(#rule_id.to_string())
                .or_insert((::std::time::Duration::ZERO, 0, 0));
            #stats_var.1 += 1;
            let #rule_id_ident = ::std::time::Instant::now();
            
            #rule_body
            
            #stats_var.0 += #rule_id_ident.elapsed();
        }
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
                            let #ident = &__crepe_var.#idx;
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
                        for __crepe_var in &#rel {
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
                            for __crepe_var in __crepe_iter {
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
            pat_datalog_vars(&guard.pat, datalog_vars);
            Box::new(move |body| {
                quote! {
                    #[allow(irrefutable_let_patterns)]
                    if #guard { #body }
                }
            })
        }
        Clause::For(For { pat, expr, .. }) => {
            assert!(!only_update);
            Box::new(move |body| {
                quote! {
                    for #pat in #expr { #body }
                }
            })
        }
    }
}

fn make_output_ty(context: &Context, hasher: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let fields = context.output_order.iter().map(|name| {
        let rel = context.rels_output.get(&name.to_string()).unwrap();
        relation_type(rel, LifetimeUsage::Item)
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

/// Visits a pattern in `ExprLet` position, returning all Datalog variables that
/// are bound by that pattern.
fn pat_datalog_vars(pat: &Pat, datalog_vars: &mut HashSet<String>) {
    match pat {
        Pat::Const(_) => (),
        Pat::Ident(pi) => {
            datalog_vars.insert(pi.ident.to_string());
            if let Some((_, ref p)) = pi.subpat {
                pat_datalog_vars(p, datalog_vars);
            }
        }
        Pat::Lit(_) => (),
        Pat::Macro(pm) => abort!(pm.span(), "Macros not allowed in let bindings."),
        Pat::Or(_) => (),
        Pat::Paren(pp) => pat_datalog_vars(&pp.pat, datalog_vars),
        Pat::Path(_) => (),
        Pat::Range(_) => (),
        Pat::Reference(pr) => pat_datalog_vars(&pr.pat, datalog_vars),
        Pat::Rest(_) => (),
        Pat::Slice(ps) => {
            for e in &ps.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::Struct(ps) => {
            for field_pat in &ps.fields {
                pat_datalog_vars(&field_pat.pat, datalog_vars);
            }
        }
        Pat::Tuple(pt) => {
            for e in &pt.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::TupleStruct(pts) => {
            for e in &pts.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::Type(pt) => pat_datalog_vars(&pt.pat, datalog_vars),
        Pat::Verbatim(pv) => abort!(pv.span(), "Cannot parse verbatim pattern."),
        Pat::Wild(_) => (),
        _ => abort!(pat.span(), "Unsupported pattern type."),
    }
}

/// Converts an `Ident` to lowercase, with the same `Span`
fn to_lowercase(name: &Ident) -> Ident {
    let s = name.to_string().to_lowercase();
    Ident::new(&s, name.span())
}

/// Validate generic parameters on a relation
/// Checks for unsupported features and provides helpful error messages
fn validate_generic_params(relation: &Relation) {
    // Type parameters are now supported!
    // Const parameters are not yet supported
    if let Some(c) = relation.generics.const_params().next() {
        abort!(c.span(), "Const parameters are not yet supported in relations");
    }
    
    // Where clauses are not yet supported
    if let Some(where_clause) = &relation.generics.where_clause {
        abort!(
            where_clause.where_token.span(), 
            "Where clauses are not yet supported in relations. \
             Please specify trait bounds directly on the type parameter instead, e.g., `T: Trait`"
        );
    }
    
    // Check for default type parameters (not supported)
    for type_param in relation.generics.type_params() {
        if type_param.default.is_some() {
            abort!(
                type_param.ident.span(),
                "Default type parameters are not supported in relations. \
                 Please remove the default value from type parameter `{}`",
                type_param.ident
            );
        }
    }
    
    // Check for lifetime bounds (not supported)
    for lifetime_param in relation.generics.lifetimes() {
        if !lifetime_param.bounds.is_empty() {
            abort!(
                lifetime_param.lifetime.span(),
                "Lifetime bounds are not supported in relations. \
                 Please remove bounds from lifetime parameter `{}`",
                lifetime_param.lifetime
            );
        }
    }
}

/// Collect all unique type parameters from input relations
fn collect_generic_params(context: &Context) -> Vec<&syn::TypeParam> {
    let mut seen = HashSet::new();
    let mut params = Vec::new();
    
    for relation in context.rels_input.values() {
        for param in relation.generics.type_params() {
            if seen.insert(param.ident.to_string()) {
                params.push(param);
            }
        }
    }
    
    params
}

/// Check if a type parameter has a specific trait bound
fn has_bound(tp: &syn::TypeParam, bound_name: &str) -> bool {
    tp.bounds.iter().any(|b| match b {
        syn::TypeParamBound::Trait(trait_bound) => {
            trait_bound.path.segments.last()
                .map_or(false, |seg| seg.ident == bound_name)
        }
        _ => false,
    })
}

/// Required trait bounds for all generic types in Datalog relations
const REQUIRED_BOUNDS: &[&str] = &["Hash", "Eq", "Clone", "Copy", "Default"];

/// Get the TokenStream for a required bound
fn required_bound_token(name: &str) -> proc_macro2::TokenStream {
    match name {
        "Hash" => quote! { ::std::hash::Hash },
        "Eq" => quote! { ::std::cmp::Eq },
        "Clone" => quote! { ::std::clone::Clone },
        "Copy" => quote! { ::std::marker::Copy },
        "Default" => quote! { ::std::default::Default },
        _ => panic!("Unknown required bound: {}", name),
    }
}

/// Merge user bounds with required bounds, avoiding duplicates
fn merge_bounds_with_required(tp: &syn::TypeParam) -> proc_macro2::TokenStream {
    let ident = &tp.ident;
    let user_bounds = &tp.bounds;
    
    // Collect missing required bounds
    let missing_bounds: Vec<_> = REQUIRED_BOUNDS.iter()
        .filter(|&req| !has_bound(tp, req))
        .map(|req| required_bound_token(req))
        .collect();
    
    // Combine user bounds + missing required bounds
    match (user_bounds.is_empty(), missing_bounds.is_empty()) {
        (true, true) => quote! { #ident },  // No bounds at all (shouldn't happen)
        (true, false) => quote! { #ident: #(#missing_bounds)+* },
        (false, true) => quote! { #ident: #user_bounds },
        (false, false) => quote! { #ident: #user_bounds + #(#missing_bounds)+* },
    }
}

/// Helper to format generic parameters with angle brackets
/// Returns `<item1, item2, ...>` or empty if the list is empty
fn format_generics(items: Vec<proc_macro2::TokenStream>) -> proc_macro2::TokenStream {
    if items.is_empty() { quote! {} } else { quote! { <#(#items),*> } }
}

/// Create a tokenstream for generic parameters (lifetimes + type params)
fn generic_params_decl(context: &Context) -> proc_macro2::TokenStream {
    let mut items = Vec::new();
    if context.has_input_lifetime {
        items.push(quote! { 'a });
    }
    items.extend(collect_generic_params(context).into_iter().map(merge_bounds_with_required));
    format_generics(items)
}

/// Create a tokenstream for generic arguments (just the names, no bounds)
fn generic_params_args(context: &Context) -> proc_macro2::TokenStream {
    let mut items = Vec::new();
    if context.has_input_lifetime {
        items.push(quote! { 'a });
    }
    items.extend(collect_generic_params(context).into_iter().map(|tp| {
        let ident = &tp.ident;
        quote! { #ident }
    }));
    format_generics(items)
}

enum LifetimeUsage {
    Item,
    Local,
}

/// Returns the type of a relation, with appropriate lifetimes and type parameters
fn relation_type(rel: &Relation, usage: LifetimeUsage) -> proc_macro2::TokenStream {
    let symbol = match rel.relation_type().unwrap() {
        RelationType::Input | RelationType::Output => "'a",
        RelationType::Intermediate => match usage {
            LifetimeUsage::Item => "'a",
            LifetimeUsage::Local => "'_",
        },
    };

    let name = &rel.name;
    
    // Build list of generic arguments
    let mut items = Vec::new();
    items.extend(rel.generics.lifetimes().map(|l| {
        let lifetime = Lifetime::new(symbol, l.span());
        quote! { #lifetime }
    }));
    items.extend(rel.generics.type_params().map(|tp| {
        let ident = &tp.ident;
        quote! { #ident }
    }));
    
    // Format with angle brackets if there are any generics
    if items.is_empty() {
        quote! { #name }
    } else {
        quote! { #name<#(#items),*> }
    }
}
