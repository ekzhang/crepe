// Test multiple generic type parameters

use crepe::crepe;

crepe! {
    @input
    struct Pair<K, V>(K, V);

    @output
    struct Swapped<K, V>(V, K);

    Swapped(v, k) <- Pair(k, v);
}

#[test]
fn test_multiple_generics() {
    let mut runtime = Crepe::new();
    runtime.extend([Pair(1, "one"), Pair(2, "two"), Pair(3, "three")]);

    let (swapped,) = runtime.run();
    let mut results: Vec<_> = swapped.into_iter().map(|Swapped(v, k)| (v, k)).collect();
    results.sort_unstable();

    assert_eq!(results, vec![("one", 1), ("three", 3), ("two", 2),]);
}

#[test]
fn test_multiple_generics_same_type() {
    let mut runtime = Crepe::new();
    runtime.extend([Pair(1, 10), Pair(2, 20), Pair(3, 30)]);

    let (swapped,) = runtime.run();
    let mut results: Vec<_> = swapped.into_iter().map(|Swapped(v, k)| (v, k)).collect();
    results.sort_unstable();

    assert_eq!(results, vec![(10, 1), (20, 2), (30, 3),]);
}
