// In this test, the relation `In` is inappropriately derived in a rule, even
// though it is marked as an @input.

mod datalog {
    use crepe::runtime;

    runtime! {
        @input
        struct In(u32, u32);

        In(0, 0) <- (true);
    }
}

fn main() {}
