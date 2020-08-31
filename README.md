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
use crepe::runtime;

runtime! {
    @input
    struct Edge(i32, i32);

    @output
    struct Reachable(i32, i32);

    Reachable(x, y) <- Edge(x, y);
    Reachable(x, z) <- Edge(x, y), Reachable(y, z);
}

fn main() {
    let edges = vec![Edge(1, 2), Edge(2, 3), Edge(3, 4), Edge(2, 5)];
    let result = Runtime::new().edge(edges).run();
    for Reachable(x, y) in result.reachable {
        println!("node {} can reach node {}", x, y);
    }
}
```

## Features

- Semi-naive evaluation
- Automatic generation of indices for relations
- Arbitrary Rust expression syntax allowed in rules
- Builder pattern for setting `@input` relations
- Very fast, compiled directly with the rest of your Rust code

In the future, we want to support:

- Stratified negation

## Acknowledgements

This work was heavily inspired by [Souffle](https://souffle-lang.github.io/)
and [Formulog](https://github.com/HarvardPL/formulog), which both use similar
models of Datalog compilation for static analysis.
