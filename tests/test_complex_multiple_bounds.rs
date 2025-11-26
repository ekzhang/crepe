// Test multiple type parameters each with multiple trait bounds

use crepe::crepe;
use std::fmt::{Debug, Display};

trait KeyTrait {
    fn key_value(&self) -> u32;
}

trait ValueTrait {
    fn value_text(&self) -> &'static str;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Default)]
struct MyKey(u32);

#[derive(Hash, Eq, PartialEq, Clone, Copy, Default)]
struct MyValue(&'static str);

impl KeyTrait for MyKey {
    fn key_value(&self) -> u32 { self.0 }
}

impl Debug for MyKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Key({})", self.0)
    }
}

impl Display for MyKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "K{}", self.0)
    }
}

impl ValueTrait for MyValue {
    fn value_text(&self) -> &'static str { self.0 }
}

impl Debug for MyValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Value({})", self.0)
    }
}

impl Display for MyValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V:{}", self.0)
    }
}

crepe! {
    @input
    struct Mapping<K: KeyTrait + Debug + Display, V: ValueTrait + Debug + Display>(K, V);

    @output
    struct Reversed<K: KeyTrait + Debug + Display, V: ValueTrait + Debug + Display>(V, K);

    Reversed(v, k) <- Mapping(k, v);
}

#[test]
fn test_complex_multiple_bounds() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Mapping(MyKey(1), MyValue("one")),
        Mapping(MyKey(2), MyValue("two")),
        Mapping(MyKey(3), MyValue("three")),
    ]);
    
    let (reversed,) = runtime.run();
    let mut results: Vec<_> = reversed
        .into_iter()
        .map(|Reversed(v, k)| (v.value_text(), k.key_value()))
        .collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![
        ("one", 1),
        ("three", 3),
        ("two", 2),
    ]);
}
