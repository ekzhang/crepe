#[test]
fn tests() {
    let t = trybuild::TestCases::new();
    t.pass("tests/01-parse.rs");
    t.pass("tests/02-declare-structs.rs");
    t.compile_fail("tests/03-unbound-variable.rs");
    t.compile_fail("tests/04-invalid-arity.rs");
    t.compile_fail("tests/05-bad-goal-input.rs");
    t.pass("tests/06-transitive-closure.rs");
    t.pass("tests/07-fibonacci.rs");
}
