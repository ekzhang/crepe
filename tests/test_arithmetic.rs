// This test checks mathematical operations and numeric comparisons.
// It tests arithmetic expressions, multiple conditions, and range queries.

use crepe::crepe;

crepe! {
    @input
    struct Number(i32);

    @output
    struct Square(i32, i32);

    @output
    struct Even(i32);

    @output
    struct PerfectSquare(i32);

    @output
    struct InRange(i32);

    // Calculate squares
    Square(x, y) <- Number(x), let y = x * x;

    // Find even numbers
    Even(x) <- Number(x), (x % 2 == 0);

    // Find perfect squares within the input numbers
    PerfectSquare(x) <- Number(x), Number(y), (y * y == x);

    // Numbers in a specific range [10, 30]
    InRange(x) <- Number(x), (x >= 10), (x <= 30);
}

#[test]
fn test_arithmetic() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Number(1),
        Number(2),
        Number(3),
        Number(4),
        Number(5),
        Number(9),
        Number(16),
        Number(20),
        Number(25),
        Number(30),
        Number(35),
    ]);

    let (squares, evens, perfect_squares, in_range) = runtime.run();
    
    let mut square_vec: Vec<_> = squares
        .into_iter()
        .map(|Square(x, y)| (x, y))
        .collect();
    square_vec.sort_unstable();
    
    assert_eq!(square_vec, vec![
        (1, 1),
        (2, 4),
        (3, 9),
        (4, 16),
        (5, 25),
        (9, 81),
        (16, 256),
        (20, 400),
        (25, 625),
        (30, 900),
        (35, 1225),
    ]);

    let mut even_vec: Vec<_> = evens
        .into_iter()
        .map(|Even(x)| x)
        .collect();
    even_vec.sort_unstable();
    
    assert_eq!(even_vec, vec![2, 4, 16, 20, 30]);

    let mut perfect_vec: Vec<_> = perfect_squares
        .into_iter()
        .map(|PerfectSquare(x)| x)
        .collect();
    perfect_vec.sort_unstable();
    
    assert_eq!(perfect_vec, vec![1, 4, 9, 16, 25]);

    let mut range_vec: Vec<_> = in_range
        .into_iter()
        .map(|InRange(x)| x)
        .collect();
    range_vec.sort_unstable();
    
    assert_eq!(range_vec, vec![16, 20, 25, 30]);
}
