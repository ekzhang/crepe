// This test has a negated clause, but it is not stratified.

use crepe::crepe;

crepe! {
    struct Ok();

    Ok() <- !Ok();
}

fn main() {}
