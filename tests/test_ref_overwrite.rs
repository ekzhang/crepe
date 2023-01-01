// This test ensures that variables bound with `ref` are always bound,
// overwriting previous variables of the same name.
//
// Behavior may change in the future, since this is an edge case.

use crepe::crepe;

crepe! {
    @input
    struct Input(i32);

    @output
    #[derive(Debug, Ord, PartialOrd)]
    struct Output(i32);

    Output(*_x + *_x) <- Input(_x), Input(ref _x);
}

#[test]
fn test_ref_overwrite() {
    let mut rt = Crepe::new();
    rt.extend([Input(2), Input(3)]);
    let (res,) = rt.run();
    let mut res: Vec<_> = res.into_iter().collect();
    res.sort_unstable();
    assert_eq!(res, vec![Output(4), Output(6)]);
}
