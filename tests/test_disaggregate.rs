// This test checks the functionality of disaggregates, or the `for` keyword.

use crepe::crepe;

crepe! {
    @input
    struct Name<'a>(&'a str);

    @output
    #[derive(Debug, PartialOrd, Ord)]
    struct NameContainsLetter<'a>(&'a str, char);

    NameContainsLetter(name, letter) <- Name(name), for letter in name.chars();
}

#[test]
fn test_disaggregate() {
    let mut rt = Crepe::new();
    rt.extend(&[Name("al"), Name("bob")]);
    let (res,) = rt.run();
    let mut res: Vec<_> = res.into_iter().collect();
    res.sort();
    assert_eq!(
        res,
        vec![
            NameContainsLetter("al", 'a'),
            NameContainsLetter("al", 'l'),
            NameContainsLetter("bob", 'b'),
            NameContainsLetter("bob", 'o'),
        ],
    );
}
