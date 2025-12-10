// Test generic transitive closure

use crepe::crepe;

crepe! {
    @input
    struct Edge<T>(T, T);

    @output
    struct Reachable<T>(T, T);

    Reachable(x, y) <- Edge(x, y);
    Reachable(x, z) <- Edge(x, y), Reachable(y, z);
}

#[test]
fn test_generic_transitive_closure() {
    let mut runtime = Crepe::new();
    runtime.extend([Edge(1, 2), Edge(2, 3), Edge(3, 4), Edge(2, 5)]);

    let (reachable,) = runtime.run();
    let mut results: Vec<_> = reachable
        .into_iter()
        .map(|Reachable(x, y)| (x, y))
        .collect();
    results.sort_unstable();

    let expected = vec![
        (1, 2),
        (1, 3),
        (1, 4),
        (1, 5),
        (2, 3),
        (2, 4),
        (2, 5),
        (3, 4),
    ];

    assert_eq!(results, expected);
}

#[test]
fn test_generic_with_strings() {
    let mut runtime = Crepe::new();
    runtime.extend([Edge("a", "b"), Edge("b", "c"), Edge("c", "d")]);

    let (reachable,) = runtime.run();
    let mut results: Vec<_> = reachable
        .into_iter()
        .map(|Reachable(x, y)| (x, y))
        .collect();
    results.sort_unstable();

    assert!(results.contains(&("a", "b")));
    assert!(results.contains(&("a", "c")));
    assert!(results.contains(&("a", "d")));
    assert!(results.contains(&("b", "c")));
    assert!(results.contains(&("b", "d")));
    assert!(results.contains(&("c", "d")));
}
