// In this test, the variable named 'n' is used before binding in a clause.

mod datalog {
    use crepe::crepe;

    crepe! {
        @output
        struct Fib(u32, u32);

        Fib(0, 0);
        Fib(1, 1);

        Fib(n, x + y) <- Fib(n - 1, x), Fib(n - 2, y), (n <= 25);
    }
}

fn main() {}
