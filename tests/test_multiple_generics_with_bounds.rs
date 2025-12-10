// Test multiple generic parameters with custom trait bounds

use crepe::crepe;

trait Key {
    fn key_id(&self) -> u32;
}

trait Value {
    fn value_id(&self) -> u32;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct MyKey(u32);

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct MyValue(u32);

impl Key for MyKey {
    fn key_id(&self) -> u32 { self.0 }
}

impl Value for MyValue {
    fn value_id(&self) -> u32 { self.0 }
}

crepe! {
    @input
    struct Entry<K: Key, V: Value>(K, V);

    @output
    struct Flipped<K: Key, V: Value>(V, K);

    Flipped(v, k) <- Entry(k, v);
}

#[test]
fn test_multiple_generics_with_trait_bounds() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Entry(MyKey(1), MyValue(10)),
        Entry(MyKey(2), MyValue(20)),
        Entry(MyKey(3), MyValue(30)),
    ]);
    
    let (flipped,) = runtime.run();
    let mut results: Vec<_> = flipped
        .into_iter()
        .map(|Flipped(v, k)| (v.value_id(), k.key_id()))
        .collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![
        (10, 1),
        (20, 2),
        (30, 3),
    ]);
}
