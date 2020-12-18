# Crepe &emsp; [![Latest Version]][crates.io]

[latest version]: https://img.shields.io/crates/v/crepe.svg
[crates.io]: https://crates.io/crates/crepe

Crepe is a library that allows you to write declarative logic programs in
Rust, with a [Datalog](https://en.wikipedia.org/wiki/Datalog)-like syntax.
It provides a procedural macro that generates efficient, safe code and
interoperates seamlessly with Rust programs.

## Features

- Semi-naive evaluation
- Stratified negation
- Automatic generation of indices for relations
- Easily call Rust functions from within Datalog rules
- Typesafe way to initialize `@input` relations
- Very fast, compiled directly with the rest of your Rust code

## Example

The program below computes the transitive closure of a directed graph. Note
the use of the `crepe!` macro.

```rust
use crepe::crepe;

crepe! {
    @input
    struct Edge(i32, i32);

    @output
    struct Reachable(i32, i32);

    Reachable(x, y) <- Edge(x, y);
    Reachable(x, z) <- Edge(x, y), Reachable(y, z);
}

fn main() {
    let mut runtime = Crepe::new();
    runtime.extend(&[Edge(1, 2), Edge(2, 3), Edge(3, 4), Edge(2, 5)]);

    let (reachable,) = runtime.run();
    for Reachable(x, y) in reachable {
        println!("node {} can reach node {}", x, y);
    }
}
```

Output:

```
node 1 can reach node 2
node 1 can reach node 3
node 1 can reach node 4
node 1 can reach node 5
node 2 can reach node 3
node 2 can reach node 4
node 2 can reach node 5
node 3 can reach node 4
```

You can do much more with Crepe. The next example shows how you can use
stratified negation, Rust expression syntax, and semi-naive evaluation to find
all paths in a weighted graph with length at most `MAX_PATH_LEN`.

```rust
use crepe::crepe;

const MAX_PATH_LEN: u32 = 20;

crepe! {
    @input
    struct Edge(i32, i32, u32);

    @output
    struct Walk(i32, i32, u32);

    @output
    struct NoWalk(i32, i32);

    struct Node(i32);

    Node(x) <- Edge(x, _, _);
    Node(x) <- Edge(_, x, _);

    Walk(x, x, 0) <- Node(x);
    Walk(x, z, len1 + len2) <-
        Edge(x, y, len1),
        Walk(y, z, len2),
        (len1 + len2 <= MAX_PATH_LEN);

    NoWalk(x, y) <- Node(x), Node(y), !Walk(x, y, _);
}

fn main() {
    let n = 256;
    let mut edges = Vec::new();
    for i in 0..n {
        for j in 0..n {
            if rand::random::<f32>() < 0.02 {
                edges.push(Edge(i, j, 5));
            }
        }
    }

    let mut runtime = Crepe::new();
    runtime.extend(edges);
    let (walk, nowalk) = runtime.run();
    println!("Walk: {}", walk.len());
    println!("NoWalk: {}", nowalk.len());
}
```

Output:

```
Walk: 89203
NoWalk: 8207
```

## Notes

From initial testing, the generated code is very fast. Variants of transitive
closure for large graphs (~1000 nodes) run at comparable speed to compiled
[Souffle](https://souffle-lang.github.io/), and at a fraction of the
compilation time.

For benchmarks, see the [`benches/` directory](benches/).
The benchmarks can be run using `cargo bench`.

This macro generates a `Crepe` struct in the current module, as well as structs
for all of the declared relations. This means that to integrate Crepe inside a
larger program, you should put it in its own module with related code. See the
documentation for more information.

## Acknowledgements

This project was heavily inspired by [Souffle](https://souffle-lang.github.io/)
and [Formulog](https://github.com/HarvardPL/formulog), which both use similar
models of Datalog compilation for static analysis.
