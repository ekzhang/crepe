// This test checks string operations and pattern matching.
// It demonstrates working with string slices and comparisons.

use crepe::crepe;

crepe! {
    @input
    struct Word<'a>(&'a str);

    @output
    struct ShortWord<'a>(&'a str);

    @output
    struct LongWord<'a>(&'a str);

    @output
    struct StartsWith<'a>(&'a str, char);

    @output
    struct Palindrome<'a>(&'a str);

    // Words with length <= 4
    ShortWord(w) <- Word(w), (w.len() <= 4);

    // Words with length > 8
    LongWord(w) <- Word(w), (w.len() > 8);

    // Track first character
    StartsWith(w, c) <- Word(w), let c = w.chars().next().unwrap();

    // Check for palindromes
    Palindrome(w) <- 
        Word(w), 
        let reversed = w.chars().rev().collect::<String>(),
        (w == reversed.as_str());
}

#[test]
fn test_string_operations() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Word("hello"),
        Word("world"),
        Word("rust"),
        Word("programming"),
        Word("code"),
        Word("data"),
        Word("a"),
        Word("racecar"),
        Word("level"),
        Word("test"),
    ]);

    let (short, long, starts, palindromes) = runtime.run();
    
    let mut short_vec: Vec<_> = short
        .into_iter()
        .map(|ShortWord(w)| w)
        .collect();
    short_vec.sort_unstable();
    
    assert_eq!(short_vec, vec!["a", "code", "data", "rust", "test"]);

    let mut long_vec: Vec<_> = long
        .into_iter()
        .map(|LongWord(w)| w)
        .collect();
    long_vec.sort_unstable();
    
    assert_eq!(long_vec, vec!["programming"]);

    let starts_vec: Vec<_> = starts
        .into_iter()
        .map(|StartsWith(w, c)| (w, c))
        .collect();
    
    assert!(starts_vec.contains(&("hello", 'h')));
    assert!(starts_vec.contains(&("world", 'w')));
    assert!(starts_vec.contains(&("rust", 'r')));
    assert!(starts_vec.contains(&("programming", 'p')));

    let mut pal_vec: Vec<_> = palindromes
        .into_iter()
        .map(|Palindrome(w)| w)
        .collect();
    pal_vec.sort_unstable();
    
    assert_eq!(pal_vec, vec!["a", "level", "racecar"]);
}
