# Changelog

## 0.1.8 - 2023-03-19

- Update syn dependency to v2.0

## 0.1.7 - 2023-01-01

- Change library and examples to use Rust 2021 array `IntoIterator` impls
- Update petgraph dependency to v0.6

## 0.1.6 - 2022-02-22

- Implement support for iteration through `for` clauses in rules

## 0.1.5 - 2021-01-19

- Bugfix: register Datalog variables bound in `let` patterns (#14)

## 0.1.4 - 2021-01-10

- Add support for lifetimes in relations and the `ref` keyword (#9)
- Add benchmarks and support for custom hashers (#9)

## 0.1.3 - 2020-11-21

- Add shorter syntax for defining fact-rules (#6)
- Add visibility modifiers to structs and fields, support struct attributes (#7)

## 0.1.2 - 2020-09-13

- Implement support for destructuring and `let` bindings in rules
- Add a span for more specific "invalid relation" error messages
- Hygiene: write full paths for derived traits
- Add documentation for the generated runtime
- Add more comprehensive tests: `&static str` in relation, `f64` in relation
- Make clippy happy

## 0.1.1 - 2020-09-01

- Fix bug causing docs to not render properly

## 0.1.0 - 2020-09-01

Initial release - `crepe!` macro, Datalog runtime, semi-naive evaluation,
stratified negation.
