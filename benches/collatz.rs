use criterion::{black_box, criterion_group, criterion_main, Criterion};

use crepe::crepe;

crepe! {
    @input
    struct Start(u128);

    struct Intermediate(u128, u128);

    @output
    struct Col(u128);

    Intermediate(0, n) <- Start(n);
    Intermediate(n + 1, if x % 2 == 0 { x / 2 } else { 3 * x + 1 }) <- Intermediate(n, x), (x != 1);

    Col(n) <- Intermediate(n, x), (x != 1);
}

// Return the stopping time for the given starting number.
fn collatz_length(n: u128) -> usize {
    let mut rt = Crepe::new();

    rt.extend(&[Start(n)]);

    let (cols,) = rt.run_with_hasher::<fnv::FnvBuildHasher>();
    cols.len()
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "collatz",
        |b, n| {
            b.iter(|| collatz_length(black_box(*n)));
        },
        vec![9, 77_031, 9_780_657_630],
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
