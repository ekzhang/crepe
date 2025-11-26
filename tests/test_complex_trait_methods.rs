// Test more complex trait method usage

use crepe::crepe;

trait Node {
    fn id(&self) -> u32;
    fn priority(&self) -> u32;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Task {
    task_id: u32,
    prio: u32,
}

impl Node for Task {
    fn id(&self) -> u32 {
        self.task_id
    }
    
    fn priority(&self) -> u32 {
        self.prio
    }
}

crepe! {
    @input
    struct Edge<T: Node>(T, T);

    @output
    struct Path<T: Node>(T, T, u32);
    
    @output
    struct HighPriorityPath<T: Node>(T, T);

    // Calculate path with combined priority
    Path(x, y, p) <- 
        Edge(x, y), 
        let p = x.priority() + y.priority();
    
    // Transitive paths with priority sum
    Path(x, z, p) <- 
        Edge(x, y), 
        Path(y, z, p2),
        let p = x.priority() + p2;
    
    // Filter high priority paths
    HighPriorityPath(x, y) <- 
        Path(x, y, p),
        (p > 10);
}

#[test]
fn test_complex_trait_methods() {
    let t1 = Task { task_id: 1, prio: 3 };
    let t2 = Task { task_id: 2, prio: 5 };
    let t3 = Task { task_id: 3, prio: 7 };
    
    let mut runtime = Crepe::new();
    runtime.extend([
        Edge(t1, t2),
        Edge(t2, t3),
    ]);
    
    let (paths, high_prio) = runtime.run();
    
    // Check path priorities
    let path_vec: Vec<_> = paths
        .into_iter()
        .map(|Path(x, y, p)| (x.id(), y.id(), p))
        .collect();
    
    // t1 -> t2: priority 3 + 5 = 8
    assert!(path_vec.contains(&(1, 2, 8)));
    
    // t2 -> t3: priority 5 + 7 = 12
    assert!(path_vec.contains(&(2, 3, 12)));
    
    // t1 -> t3: priority 3 + 12 = 15
    assert!(path_vec.contains(&(1, 3, 15)));
    
    // Check high priority paths (> 10)
    let high_vec: Vec<_> = high_prio
        .into_iter()
        .map(|HighPriorityPath(x, y)| (x.id(), y.id()))
        .collect();
    
    // t2 -> t3 has priority 12 > 10
    assert!(high_vec.contains(&(2, 3)));
    
    // t1 -> t3 has priority 15 > 10
    assert!(high_vec.contains(&(1, 3)));
    
    // t1 -> t2 has priority 8 < 10 (should not be in high_prio)
    assert!(!high_vec.contains(&(1, 2)));
}
