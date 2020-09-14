# Changelog

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
