// Test basic generic type parameter support

use crepe::crepe;

crepe! {
    @input
    struct Input<T>(T);

    @output
    struct Output<T>(T);

    Output(x) <- Input(x);
}

#[test]
fn test_basic_generic() {
    let mut runtime = Crepe::new();
    runtime.extend([Input(1), Input(2), Input(3)]);
    
    let (output,) = runtime.run();
    let mut results: Vec<_> = output.into_iter().map(|Output(x)| x).collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![1, 2, 3]);
}
