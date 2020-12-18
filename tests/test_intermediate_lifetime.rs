// This test uses input values by reference inside an intermediate relation
// and copies it into the output relation.
// Binding with `ref name` captures a value by reference.

use crepe::crepe;

crepe! {
    @input
    struct Input([usize; 4]);

    struct Value<'a>(&'a usize);

    @output
    struct Output(usize);

    Value(&x[0]) <- Input(ref x);
    Value(&x[2]) <- Input(ref x);

    Output(*x) <- Value(x);
}

#[test]
fn test_intermediate_lifetime() {
    let mut rt = Crepe::new();
    rt.extend(&[Input([0, 1, 2, 3]), Input([1, 2, 3, 4])]);
    let (res,) = rt.run();
    let mut res = res.into_iter().map(|Output(n)| n).collect::<Vec<_>>();
    res.sort_unstable();
    assert_eq!(res, [0, 1, 2, 3]);
}
