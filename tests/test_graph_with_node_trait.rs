// Test generic graph with custom node type and trait

use crepe::crepe;
use std::fmt::Display;

// Custom trait for graph nodes
trait Node: Display {
    fn id(&self) -> u32;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct City {
    id: u32,
    name: &'static str,
}

impl Node for City {
    fn id(&self) -> u32 {
        self.id
    }
}

impl Display for City {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.name, self.id)
    }
}

crepe! {
    @input
    struct Connection<T: Node>(T, T);

    @output
    struct Connected<T: Node>(T, T);

    Connected(x, y) <- Connection(x, y);
    Connected(x, z) <- Connection(x, y), Connected(y, z);
}

#[test]
fn test_graph_with_custom_node_trait() {
    let seattle = City { id: 1, name: "Seattle" };
    let portland = City { id: 2, name: "Portland" };
    let sf = City { id: 3, name: "SF" };
    let la = City { id: 4, name: "LA" };
    
    let mut runtime = Crepe::new();
    runtime.extend([
        Connection(seattle, portland),
        Connection(portland, sf),
        Connection(sf, la),
    ]);
    
    let (connected,) = runtime.run();
    let mut results: Vec<_> = connected
        .into_iter()
        .map(|Connected(x, y)| (x.id(), y.id()))
        .collect();
    results.sort_unstable();
    
    // Check all connections
    assert!(results.contains(&(1, 2))); // Seattle -> Portland
    assert!(results.contains(&(1, 3))); // Seattle -> SF
    assert!(results.contains(&(1, 4))); // Seattle -> LA
    assert!(results.contains(&(2, 3))); // Portland -> SF
    assert!(results.contains(&(2, 4))); // Portland -> LA
    assert!(results.contains(&(3, 4))); // SF -> LA
    
    assert_eq!(results.len(), 6);
}
