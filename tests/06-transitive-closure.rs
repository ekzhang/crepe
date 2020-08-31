// This test checks the output of a pure-Datalog, transitive closure program.
// No extensions like Rust operators or arithmetic are used, but this requires
// correct indices to be generated for the `Tc` relation.

mod datalog {
    use crepe::runtime;

    runtime! {
        @input
        struct Edge(i32, i32);

        @output
        struct Tc(i32, i32);

        Tc(x, y) :- Edge(x, y);
        Tc(x, z) :- Edge(x, y), Tc(y, z);
    }

    pub fn run(edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
        let output = Runtime::new()
            .edge(edges.iter().map(|&(a, b)| Edge(a, b)))
            .run();
        output.tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
    }
}

fn main() {
    let edges = vec![(1, 2), (2, 3), (3, 4), (2, 5)];
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
    let mut result = datalog::run(&edges);
    result.sort();
    assert_eq!(result, expected);
}
