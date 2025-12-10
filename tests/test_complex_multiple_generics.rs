// Test combining multiple generics with different relations

use crepe::crepe;

trait Label {
    fn label(&self) -> &'static str;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Node(u32);

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Tag(&'static str);

impl Label for Tag {
    fn label(&self) -> &'static str {
        self.0
    }
}

crepe! {
    @input
    struct Edge<T>(T, T);

    @input
    struct Tagged<T, L: Label>(T, L);

    @output
    struct Reachable<T>(T, T);

    @output
    struct LabeledPath<T, L: Label>(T, T, L);

    // Transitive closure
    Reachable(x, y) <- Edge(x, y);
    Reachable(x, z) <- Edge(x, y), Reachable(y, z);

    // Labeled paths
    LabeledPath(x, y, l) <- Edge(x, y), Tagged(x, l);
}

#[test]
fn test_complex_multiple_generics() {
    let mut runtime = Crepe::new();

    // Add edges
    runtime.extend([
        Edge(Node(1), Node(2)),
        Edge(Node(2), Node(3)),
        Edge(Node(3), Node(4)),
    ]);

    // Add tags
    runtime.extend([
        Tagged(Node(1), Tag("start")),
        Tagged(Node(2), Tag("middle")),
    ]);

    let (reachable, labeled) = runtime.run();

    // Check reachability
    let reach_vec: Vec<_> = reachable
        .into_iter()
        .map(|Reachable(x, y)| (x.0, y.0))
        .collect();

    assert!(reach_vec.contains(&(1, 2)));
    assert!(reach_vec.contains(&(1, 3)));
    assert!(reach_vec.contains(&(1, 4)));
    assert!(reach_vec.contains(&(2, 3)));
    assert!(reach_vec.contains(&(2, 4)));
    assert!(reach_vec.contains(&(3, 4)));

    // Check labeled paths
    let labeled_vec: Vec<_> = labeled
        .into_iter()
        .map(|LabeledPath(x, y, l)| (x.0, y.0, l.label()))
        .collect();

    assert!(labeled_vec.contains(&(1, 2, "start")));
    assert!(labeled_vec.contains(&(2, 3, "middle")));
}
