// This tests destructuring and assignment guards in rules.

use crepe::crepe;

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
enum Token {
    String(&'static str),
    Integer(i32),
    Fraction(i32, i32),
}

crepe! {
    @input
    struct ProgramToken(Token);

    @output
    struct ProgramString(&'static str);

    @output
    struct ProgramInteger(i32);

    ProgramString(s) <-
        ProgramToken(t),
        let Token::String(s) = t;

    ProgramInteger(x) <-
        ProgramToken(t),
        let Token::Integer(x) = t;

    ProgramInteger(q) <-
        ProgramToken(t),
        let Token::Fraction(x, y) = t,
        (y != 0 && x % y == 0),
        let q = x / y;
}

#[test]
fn test_destructure() {
    let mut runtime = Crepe::new();
    runtime.extend(&[
        ProgramToken(Token::String("hello")),
        ProgramToken(Token::String("world")),
        ProgramToken(Token::Integer(42)),
        ProgramToken(Token::Integer(1200)),
        ProgramToken(Token::Fraction(10, 1)),
        ProgramToken(Token::Fraction(3, 2)),
        ProgramToken(Token::Fraction(-42, 21)),
    ]);

    let (program_string, program_integer) = runtime.run();
    let mut strs: Vec<_> = program_string
        .into_iter()
        .map(|ProgramString(s)| s)
        .collect();
    let mut ints: Vec<_> = program_integer
        .into_iter()
        .map(|ProgramInteger(x)| x)
        .collect();

    strs.sort();
    assert_eq!(strs, vec!["hello", "world"]);
    ints.sort();
    assert_eq!(ints, vec![-2, 10, 42, 1200]);
}
