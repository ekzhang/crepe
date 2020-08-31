**(WORK IN PROGRESS)**

# Crepe

Crepe is a library that allows you to write declarative logic programs in
Rust, with a [Datalog](https://en.wikipedia.org/wiki/Datalog)-like syntax.
It provides a procedural macro that generates efficient, safe code and
interoperates seamlessly with Rust programs.

## Example

The program below computes the transitive closure of a directed graph. Note
the use of the `runtime!` macro.

```rust
mod datalog {
    use crepe::runtime;

    runtime! {
        @input
        struct Edge(i32, i32);

        @output
        struct Tc(i32, i32);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z);
    }

    pub fn run(edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
        let output = Runtime::new()
            .edge(edges.iter().map(|&(a, b)| Edge(a, b)))
            .run();
        output.tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
    }
}

fn main() {
    let edges = vec![(1, 2), (2, 3), (3, 4), (2, 5)];
    let result = datalog::run(&edges);
    println!("{:?}", result);
}
```

## Features

- Automatic generation of indices for relations
- Arbitrary Rust expression syntax allowed in rules
- Builder pattern for setting `@input` relations
- Very fast, compiled directly with the rest of your Rust code

In the future, we want to support:

- Semi-naive evaluation
- Stratified negation

## Acknowledgements

This work was heavily inspired by [Souffle](https://souffle-lang.github.io/)
and [Formulog](https://github.com/HarvardPL/formulog), which both use similar
models of Datalog compilation for static analysis.
