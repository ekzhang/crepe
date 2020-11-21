// In this test, the relation 'Fib' is given the wrong number of arguments.

mod datalog {
    use crepe::crepe;

    crepe! {
        @output
        struct Fib(u32, u32);

        Fib(0, 0, 2);
        Fib(1, 1);
    }
}

fn main() {}
