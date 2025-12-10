// Test multiple trait methods in expressions

use crepe::crepe;

trait Measurable {
    fn weight(&self) -> u32;
    fn volume(&self) -> u32;
    fn density(&self) -> u32 {
        if self.volume() > 0 {
            self.weight() / self.volume()
        } else {
            0
        }
    }
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug, Default)]
struct Package {
    id: u32,
    w: u32,
    v: u32,
}

impl Measurable for Package {
    fn weight(&self) -> u32 { self.w }
    fn volume(&self) -> u32 { self.v }
}

crepe! {
    @input
    struct Item<T: Measurable>(T);

    @output
    struct ItemStats<T: Measurable>(T, u32, u32, u32);
    
    @output
    struct Dense<T: Measurable>(T);

    // Extract stats using multiple trait methods
    ItemStats(x, w, v, d) <- 
        Item(x),
        let w = x.weight(),
        let v = x.volume(),
        let d = x.density();
    
    // Filter dense items (density > 5)
    Dense(x) <- 
        Item(x),
        let d = x.density(),
        (d > 5);
}

#[test]
fn test_multiple_trait_methods() {
    let p1 = Package { id: 1, w: 100, v: 10 };  // density = 10
    let p2 = Package { id: 2, w: 50, v: 20 };   // density = 2
    let p3 = Package { id: 3, w: 200, v: 25 };  // density = 8
    
    let mut runtime = Crepe::new();
    runtime.extend([
        Item(p1),
        Item(p2),
        Item(p3),
    ]);
    
    let (stats, dense) = runtime.run();
    
    // Check stats
    let stats_vec: Vec<_> = stats
        .into_iter()
        .map(|ItemStats(pkg, w, v, d)| (pkg.id, w, v, d))
        .collect();
    
    assert!(stats_vec.contains(&(1, 100, 10, 10)));
    assert!(stats_vec.contains(&(2, 50, 20, 2)));
    assert!(stats_vec.contains(&(3, 200, 25, 8)));
    
    // Check dense items (density > 5)
    let dense_vec: Vec<_> = dense
        .into_iter()
        .map(|Dense(pkg)| pkg.id)
        .collect();
    
    assert!(dense_vec.contains(&1));  // density 10 > 5
    assert!(dense_vec.contains(&3));  // density 8 > 5
    assert!(!dense_vec.contains(&2)); // density 2 < 5
}
