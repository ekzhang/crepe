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

mod datalog_clauses_swapped {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge(i32, i32);

        @output
        struct Tc(i32, i32);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Tc(y, z), Edge(x, y);
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
    result.sort_unstable();
    assert_eq!(result, expected);
}

// make sure that clauses can be swapped and still get the same result.
#[test]
fn test_transitive_closure_same_as_with_clauses_swapped() {
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
    let mut result_a = datalog::run(&edges);
    result_a.sort_unstable();
    assert_eq!(result_a, expected);

    let mut result_b = datalog_clauses_swapped::run(&edges);
    result_b.sort_unstable();
    assert_eq!(result_b, expected);

    assert_eq!(result_a, result_b);
}

// Version of the above test with &'a str

mod datalog_str {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge<'a>(&'a str, &'a str);

        @output
        struct Tc<'a>(&'a str, &'a str);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z);
    }

    pub fn run<'a>(edges: &[(&'a str, &'a str)]) -> Vec<(&'a str, &'a str)> {
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
    result.sort_unstable();
    assert_eq!(result, expected);
}
