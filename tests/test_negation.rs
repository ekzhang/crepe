// This program tests stratified negation

use crepe::crepe;

crepe! {
    struct R1(u32, u32);
    R1(2, 3);

    struct Ok1();
    Ok1() <- R1(2, 3), !R1(2, 2);

    struct Bad2();
    Bad2() <- !R1(_, _);

    struct Ok3();
    Ok3() <- R1(x, y), !R1(y, x);

    @output
    struct Ok();
    Ok() <- Ok1(), !Bad2(), Ok3();
}

#[test]
fn test_negation() {
    let (ok,) = Crepe::new().run();
    assert_eq!(ok.len(), 1);
}
