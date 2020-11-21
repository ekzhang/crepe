// In this test the visibility modifiers of relation structs and their fields
// are checked to be translated into the final Rust code properly.

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        struct Test(u32);

        @input
        pub struct MoreTest(bool);

        @input
        pub struct FullyPublic(pub i8);
    }
}

fn main() {
    let _ = datalog::FullyPublic(21);
    let _ = datalog::Test(1);
    let _ = datalog::MoreTest(false);
}
