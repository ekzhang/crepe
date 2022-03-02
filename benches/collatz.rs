use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use crepe::crepe;

crepe! {
    @input
    struct Start(u128);

    @output
    struct Col(u128);

    Col(x) <- Start(x);
    Col(x / 2) <- Col(x), (x % 2 == 0);
    Col(3 * x + 1) <- Col(x), (x % 2 != 0), (x != 1);
}

// Return the stopping time for the given starting number.
fn collatz_length(n: u128) -> usize {
    let mut rt = Crepe::new();

    rt.extend(&[Start(n)]);

    let (cols,) = rt.run_with_hasher::<fnv::FnvBuildHasher>();
    cols.len() - 1
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("collatz");
    for n in [9, 77_031, 9_780_657_630] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter(|| collatz_length(black_box(n)));
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
