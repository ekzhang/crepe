use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use crepe::crepe;

crepe! {
    @input
    struct Depth(u128);

    @output
    struct Fib(u128, u128);

    Fib(0, 0) <- (true);
    Fib(1, 1) <- (true);

    Fib(n + 2, x + y) <-
        Depth(depth),
        Fib(n, x), Fib(n + 1, y), (n <= depth);
}

// Doesn't return the fibonacci number but instead the number of relations generated.
fn fibonacci_length(n: u128) -> usize {
    let mut rt = Crepe::new();

    rt.extend([Depth(n)]);

    let (fibs,) = rt.run_with_hasher::<fnv::FnvBuildHasher>();
    fibs.len()
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    for n in [50, 100, 150] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter(|| fibonacci_length(black_box(n)));
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
