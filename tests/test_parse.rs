// This test defines the basic Datalog syntax and ensures it parses.
//
// Not much is done besides checking that crepe::crepe! is defined,
// as well as not self-destructing with a compilation error.

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        #[derive(Debug)]
        pub(crate) struct Edge(pub i32, pub i32);

        @output
        struct Tc(i32, i32);

        struct Intermediate(i32, u64, char);
        struct Unit();

        Tc(x, y) <- Edge(x, y);
        Tc(x, z) <- Edge(x, y), Tc(y, z), (z > 5);

        Tc(x, y) <- let (x, y) = (3, 4);

        Intermediate(_x, crepe, z) <- (true), (false), Intermediate(_x, crepe, z);
        Intermediate(42, y, 'c') <- (true), (false), Intermediate(_x, y, _z);
        Intermediate(21, 85, 'q');

        @output
        struct Node(i32);
        Node(x) <- Edge(x, _);
        Node(x) <- Edge(_, x);
        Unit() <- Edge(_, _);
    }
}

#[test]
fn test_parse() {}
