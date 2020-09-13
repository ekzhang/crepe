// This test checks the output of a pure-Datalog, transitive closure program.
// No extensions like Rust operators or arithmetic are used, but this requires
// correct indices to be generated for the `Tc` relation.

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge(i32, i32);

        @output
        struct Tc(i32, i32);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z);
    }

    pub fn run(edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
        let mut runtime = Crepe::new();
        runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
        let (tc,) = runtime.run();
        tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
    }
}

#[test]
fn test_transitive_closure() {
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

// Version of the above test with &'static str

mod datalog_str {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge(&'static str, &'static str);

        @output
        struct Tc(&'static str, &'static str);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z);
    }

    pub fn run(edges: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
        let mut runtime = Crepe::new();
        runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
        let (tc,) = runtime.run();
        tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
    }
}

#[test]
fn test_transitive_closure_str() {
    let edges = [("hello", "world"), ("world", "foo"), ("world", "bar")];
    let expected = [
        ("hello", "bar"),
        ("hello", "foo"),
        ("hello", "world"),
        ("world", "bar"),
        ("world", "foo"),
    ];
    let mut result = datalog_str::run(&edges);
    result.sort();
    assert_eq!(result, expected);
}
