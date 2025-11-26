// Test multiple trait bounds on a single type parameter

use crepe::crepe;
use std::fmt::{Debug, Display};

trait Custom {
    fn custom_id(&self) -> u32;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Default)]
struct Item(u32);

impl Custom for Item {
    fn custom_id(&self) -> u32 { self.0 }
}

impl Debug for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Item({})", self.0)
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

crepe! {
    @input
    struct Input<T: Custom + Debug + Display>(T);

    @output
    struct Output<T: Custom + Debug + Display>(T);

    Output(x) <- Input(x);
}

#[test]
fn test_multiple_trait_bounds() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Input(Item(1)),
        Input(Item(2)),
        Input(Item(3)),
    ]);
    
    let (output,) = runtime.run();
    let mut results: Vec<_> = output
        .into_iter()
        .map(|Output(x)| x.custom_id())
        .collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![1, 2, 3]);
}
