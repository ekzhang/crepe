// This test checks behavior that identifiers starting with 'A'..'Z' are not
// treated as Datalog variables.

use crepe::crepe;

crepe! {
    struct Ok(i32);
    Ok(Not_a_variable) <- Ok(Not_a_variable);
}

fn main() {}
