// This test checks path finding in a graph with multiple paths.
// It demonstrates connectivity analysis with isolated nodes.

use crepe::crepe;

crepe! {
    @input
    struct Road(&'static str, &'static str);

    @input
    struct City(&'static str);

    @output
    struct Connected(&'static str, &'static str);

    @output
    struct Isolated(&'static str);

    // Bidirectional connectivity
    Connected(x, y) <- Road(x, y);
    Connected(x, y) <- Road(y, x);
    Connected(x, z) <- Connected(x, y), Connected(y, z);

    // A city is isolated if it has no road connections
    Isolated(x) <- City(x), !Road(x, _), !Road(_, x);
}

#[test]
fn test_graph_connectivity() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Road("seattle", "portland"),
        Road("portland", "san_francisco"),
        Road("san_francisco", "los_angeles"),
        Road("denver", "salt_lake"),
        Road("salt_lake", "las_vegas"),
    ]);
    runtime.extend([
        City("seattle"),
        City("portland"),
        City("san_francisco"),
        City("los_angeles"),
        City("denver"),
        City("salt_lake"),
        City("las_vegas"),
        City("miami"),  // isolated city with no roads
    ]);

    let (connected, isolated) = runtime.run();
    
    let mut conn_vec: Vec<_> = connected
        .into_iter()
        .map(|Connected(a, b)| (a, b))
        .collect();
    conn_vec.sort_unstable();
    
    // Check west coast connectivity
    assert!(conn_vec.contains(&("seattle", "portland")));
    assert!(conn_vec.contains(&("seattle", "san_francisco")));
    assert!(conn_vec.contains(&("seattle", "los_angeles")));
    assert!(conn_vec.contains(&("portland", "los_angeles")));
    
    // Check mountain region connectivity
    assert!(conn_vec.contains(&("denver", "salt_lake")));
    assert!(conn_vec.contains(&("denver", "las_vegas")));
    
    // Verify no cross-region connections
    assert!(!conn_vec.contains(&("seattle", "denver")));
    assert!(!conn_vec.contains(&("portland", "salt_lake")));
    
    let iso_vec: Vec<_> = isolated
        .into_iter()
        .map(|Isolated(x)| x)
        .collect();
    
    // Miami is isolated - it's a city but has no road connections
    assert_eq!(iso_vec, vec!["miami"]);
}
