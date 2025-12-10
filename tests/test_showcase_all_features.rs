// Showcase: All generic features working together

use crepe::crepe;
use std::fmt::{Debug, Display};

// Multiple trait definitions
trait Node: Debug + Display {
    fn id(&self) -> u32;
    fn name(&self) -> &'static str;
}

trait Weighted {
    fn weight(&self) -> u32;
}

// Concrete type implementing multiple traits
#[derive(Hash, Eq, PartialEq, Clone, Copy, Default)]
struct City {
    id: u32,
    city_name: &'static str,
    population: u32,
}

impl Node for City {
    fn id(&self) -> u32 { self.id }
    fn name(&self) -> &'static str { self.city_name }
}

impl Weighted for City {
    fn weight(&self) -> u32 { self.population / 1000 }
}

impl Debug for City {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "City{{id={}, name={}}}", self.id, self.city_name)
    }
}

impl Display for City {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.city_name)
    }
}

crepe! {
    // Multiple type parameters with multiple bounds each
    @input
    struct Connection<N: Node + Weighted, W: Weighted>(N, N, W);
    
    @input
    struct Location<N: Node + Weighted>(N);
    
    @output
    struct Route<N: Node + Weighted>(N, N, u32);
    
    @output
    struct WeightedRoute<N: Node + Weighted>(N, N, u32);
    
    @output
    struct HeavyNode<N: Node + Weighted>(N);
    
    // Basic rule with trait method
    Route(x, y, d) <- 
        Connection(x, y, distance),
        let d = distance.weight();
    
    // Transitive closure with trait methods and arithmetic
    Route(x, z, total) <- 
        Connection(x, y, d1),
        Route(y, z, d2),
        let w1 = d1.weight(),
        let total = w1 + d2;
    
    // Complex expression with multiple trait methods
    WeightedRoute(x, y, score) <- 
        Route(x, y, d),
        let wx = x.weight(),
        let wy = y.weight(),
        let score = d + wx + wy;
    
    // Filter using trait method in condition
    HeavyNode(n) <- 
        Location(n),
        let w = n.weight(),
        (w > 500);
}

#[test]
fn test_showcase_all_features() {
    let seattle = City { id: 1, city_name: "Seattle", population: 750000 };
    let portland = City { id: 2, city_name: "Portland", population: 650000 };
    let sf = City { id: 3, city_name: "SF", population: 900000 };
    
    // Distance is also weighted
    #[derive(Hash, Eq, PartialEq, Clone, Copy, Default)]
    struct Distance(u32);
    
    impl Weighted for Distance {
        fn weight(&self) -> u32 { self.0 }
    }
    
    let mut runtime = Crepe::new();
    
    // Add connections
    runtime.extend([
        Connection(seattle, portland, Distance(100)),
        Connection(portland, sf, Distance(200)),
    ]);
    
    // Add locations
    runtime.extend([
        Location(seattle),
        Location(portland),
        Location(sf),
    ]);
    
    let (routes, weighted_routes, heavy_nodes) = runtime.run();
    
    // Test routes with trait methods
    let route_vec: Vec<_> = routes
        .into_iter()
        .map(|Route(x, y, d)| (x.name(), y.name(), d))
        .collect();
    
    assert!(route_vec.contains(&("Seattle", "Portland", 100)));
    assert!(route_vec.contains(&("Portland", "SF", 200)));
    assert!(route_vec.contains(&("Seattle", "SF", 300)));
    
    // Test weighted routes
    let weighted_vec: Vec<_> = weighted_routes
        .into_iter()
        .map(|WeightedRoute(x, y, s)| (x.name(), y.name(), s))
        .collect();
    
    // Seattle->Portland: distance(100) + seattle.weight(750) + portland.weight(650) = 1500
    assert!(weighted_vec.iter().any(|(x, y, s)| 
        *x == "Seattle" && *y == "Portland" && *s == 1500
    ));
    
    // Test heavy nodes (weight > 500)
    let heavy_vec: Vec<_> = heavy_nodes
        .into_iter()
        .map(|HeavyNode(n)| n.name())
        .collect();
    
    assert!(heavy_vec.contains(&"Seattle"));  // 750 > 500
    assert!(heavy_vec.contains(&"Portland")); // 650 > 500
    assert!(heavy_vec.contains(&"SF"));       // 900 > 500
}
