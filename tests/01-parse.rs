// This test defines the basic Datalog syntax and ensures it parses.
//
// Not much is done besides checking that datalog_runtime! is defined,
// as well as not self-destructing with a compilation error.

mod datalog {
    use crepe::runtime;

    runtime! {
        @input
        struct Edge(i32, i32);

        @output
        struct Tc(i32, i32);

        struct Intermediate(i32, u64, char);
        struct Unit();

        Tc(x, y) :- Edge(x, y);
        Tc(x, z) :- Edge(x, y), Tc(y, z), (z > 5);
    }
}

fn main() {}
