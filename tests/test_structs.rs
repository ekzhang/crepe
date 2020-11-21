// This test checks if structs declared inside the datalog module are actually
// declared, and furthermore, if they're accessible and constructible outside
// of the module as normal tuple-structs.

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge(i32, i32);

        @output
        pub struct Tc(pub i32, pub i32);

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z);
    }

    pub fn run(_edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
        // accessible here in the same module
        let _ = (Edge(2, 3), Tc(2, 3));
        vec![]
    }
}

#[test]
fn test_declare_structs() {
    assert_eq!(datalog::run(&[]), vec![]);
    // check that the Tc struct and its fields are public
    let _ = datalog::Tc(2, 3);
}
