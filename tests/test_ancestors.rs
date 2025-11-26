// This test checks ancestor relationships using recursive rules.
// It tests multiple recursive paths and demonstrates family tree queries.

use crepe::crepe;

crepe! {
    @input
    struct Parent(&'static str, &'static str);

    @output
    struct Ancestor(&'static str, &'static str);

    @output
    struct Sibling(&'static str, &'static str);

    // Base case: parents are ancestors
    Ancestor(x, y) <- Parent(x, y);
    
    // Recursive case: if x is parent of z and z is ancestor of y, then x is ancestor of y
    Ancestor(x, y) <- Parent(x, z), Ancestor(z, y);

    // Siblings share a parent
    Sibling(a, b) <- Parent(p, a), Parent(p, b), (a != b);
}

#[test]
fn test_ancestors() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Parent("alice", "bob"),
        Parent("alice", "charlie"),
        Parent("bob", "dave"),
        Parent("bob", "eve"),
        Parent("charlie", "frank"),
        Parent("dave", "grace"),
    ]);

    let (ancestors, siblings) = runtime.run();
    
    let mut ancestor_vec: Vec<_> = ancestors
        .into_iter()
        .map(|Ancestor(a, b)| (a, b))
        .collect();
    ancestor_vec.sort_unstable();
    
    // Check that all ancestor relationships are correct
    assert!(ancestor_vec.contains(&("alice", "bob")));
    assert!(ancestor_vec.contains(&("alice", "charlie")));
    assert!(ancestor_vec.contains(&("alice", "dave")));
    assert!(ancestor_vec.contains(&("alice", "eve")));
    assert!(ancestor_vec.contains(&("alice", "frank")));
    assert!(ancestor_vec.contains(&("alice", "grace")));
    assert!(ancestor_vec.contains(&("bob", "dave")));
    assert!(ancestor_vec.contains(&("bob", "eve")));
    assert!(ancestor_vec.contains(&("bob", "grace")));
    assert!(ancestor_vec.contains(&("charlie", "frank")));
    assert!(ancestor_vec.contains(&("dave", "grace")));
    
    let mut sibling_vec: Vec<_> = siblings
        .into_iter()
        .map(|Sibling(a, b)| (a, b))
        .collect();
    sibling_vec.sort_unstable();
    
    // Check siblings (note: both directions)
    assert!(sibling_vec.contains(&("bob", "charlie")));
    assert!(sibling_vec.contains(&("charlie", "bob")));
    assert!(sibling_vec.contains(&("dave", "eve")));
    assert!(sibling_vec.contains(&("eve", "dave")));
}
