// Test that duplicate bounds are not added

use crepe::crepe;
use std::hash::Hash;

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Value(i32);

crepe! {
    @input
    struct Input<T: Hash>(T);

    @output
    struct Output<T: Hash>(T);

    Output(x) <- Input(x);
}

#[test]
fn test_no_duplicate_bounds() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Input(Value(1)),
        Input(Value(2)),
        Input(Value(3)),
    ]);
    
    let (output,) = runtime.run();
    let results: Vec<_> = output
        .into_iter()
        .map(|Output(x)| x.0)
        .collect();
    
    assert_eq!(results.len(), 3);
}
