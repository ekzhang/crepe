// This test is a Datalog program that generates Fibonacci numbers F_{0..25}.
//
// It tests that the main loop is run at least once even if no input relations
// are provided, as well as arithmetic operators, Rust expression conditions,
// and interpolation.

mod datalog {
    use crepe::crepe;

    crepe! {
        @output
        struct Fib(u32, u32);

        Fib(0, 0) <- (true);
        Fib(1, 1) <- (true);

        Fib(n + 2, x + y) <- Fib(n, x), Fib(n + 1, y), (n <= 23);
    }

    pub fn run() -> Vec<(u32, u32)> {
        let mut output = Crepe::new()
            .run()
            .fib
            .into_iter()
            .map(|Fib(x, y)| (x, y))
            .collect::<Vec<_>>();
        output.sort();
        output
    }
}

fn main() {
    let results = datalog::run();
    assert_eq!(
        results,
        [
            (0, 0),
            (1, 1),
            (2, 1),
            (3, 2),
            (4, 3),
            (5, 5),
            (6, 8),
            (7, 13),
            (8, 21),
            (9, 34),
            (10, 55),
            (11, 89),
            (12, 144),
            (13, 233),
            (14, 377),
            (15, 610),
            (16, 987),
            (17, 1597),
            (18, 2584),
            (19, 4181),
            (20, 6765),
            (21, 10946),
            (22, 17711),
            (23, 28657),
            (24, 46368),
            (25, 75025)
        ]
    );
}
