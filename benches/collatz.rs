use criterion::{black_box, criterion_group, criterion_main, Criterion};

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
