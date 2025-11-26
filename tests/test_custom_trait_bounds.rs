// Test generic with custom trait bounds

use crepe::crepe;

// Custom trait
trait Valuable {
    fn value(&self) -> i32;
}

// Type that implements the custom trait and required traits
#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug)]
struct Item(i32);

impl Valuable for Item {
    fn value(&self) -> i32 {
        self.0
    }
}

impl Default for Item {
    fn default() -> Self {
        Item(0)
    }
}

crepe! {
    @input
    struct Input<T: Valuable>(T);

    @output
    struct Output<T: Valuable>(T);

    Output(x) <- Input(x);
}

#[test]
fn test_custom_trait_bound() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Input(Item(1)),
        Input(Item(2)),
        Input(Item(3)),
    ]);
    
    let (output,) = runtime.run();
    let mut results: Vec<_> = output
        .into_iter()
        .map(|Output(x)| x.value())
        .collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![1, 2, 3]);
}

#[test]
fn test_custom_trait_with_integers() {
    // Create a simple wrapper that implements Valuable
    #[derive(Hash, Eq, PartialEq, Clone, Copy, Debug)]
    struct Val(i32);
    
    impl Valuable for Val {
        fn value(&self) -> i32 { self.0 }
    }
    
    impl Default for Val {
        fn default() -> Self { Val(0) }
    }
    
    let mut runtime = Crepe::new();
    runtime.extend([
        Input(Val(10)),
        Input(Val(20)),
        Input(Val(30)),
    ]);
    
    let (output,) = runtime.run();
    let results: Vec<_> = output
        .into_iter()
        .map(|Output(x)| x.value())
        .collect();
    
    assert_eq!(results.len(), 3);
    assert!(results.contains(&10));
    assert!(results.contains(&20));
    assert!(results.contains(&30));
}
