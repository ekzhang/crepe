// Test calling trait methods in Datalog rules

use crepe::crepe;

trait Cost {
    fn cost(&self) -> u32;
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Item {
    id: u32,
    price: u32,
}

impl Cost for Item {
    fn cost(&self) -> u32 {
        self.price
    }
}

crepe! {
    @input
    struct Product<T: Cost>(T);

    @output
    struct PriceInfo<T: Cost>(T, u32);

    // Try calling trait method in rule
    PriceInfo(x, c) <- Product(x), let c = x.cost();
}

#[test]
fn test_trait_method_call() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Product(Item { id: 1, price: 100 }),
        Product(Item { id: 2, price: 200 }),
        Product(Item { id: 3, price: 300 }),
    ]);
    
    let (price_info,) = runtime.run();
    let mut results: Vec<_> = price_info
        .into_iter()
        .map(|PriceInfo(item, price)| (item.id, price))
        .collect();
    results.sort_unstable();
    
    assert_eq!(results, vec![
        (1, 100),
        (2, 200),
        (3, 300),
    ]);
}
