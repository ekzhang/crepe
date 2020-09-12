// This test tries to declare an invalid relation struct with a type that does
// not implement the `Hash` or `Eq` traits, and ensures the error message
// points to the relation, rather than a generic span.

use crepe::crepe;

crepe! {
    struct Ok(f64);
}

fn main() {}
