// This test tries to derive a rule with an ignored variable "_"

use crepe::crepe;

crepe! {
    struct Ok(i32);
    Ok(_) <- Ok(_);
}

fn main() {}
