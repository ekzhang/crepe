// In this test, the variable named 'n' is used before binding in a clause.

mod datalog {
    use crepe::runtime;

    runtime! {
        @output
        struct Fib(u32, u32);

        Fib(0, 0) :- (true);
        Fib(1, 1) :- (true);

        Fib(n, x + y) :- Fib(n - 1, x), Fib(n - 2, y), (n <= 25);
    }
}

fn main() {}
