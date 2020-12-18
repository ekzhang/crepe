// In this test, the relation `Out` refers to data inside the `In` relation by
// taking a reference to its contents.
// Since that lifetime is related to input data which is moved and consumed
// within the `run(self)` function, the reference would out-live it's lifetime.

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        struct Input(u32, u32);

        @output
        struct Output<'a>(&'a u32);

        Output(&a) <- Input(a, _);
    }
}

fn main() {}
