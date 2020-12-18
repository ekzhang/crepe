use criterion::{black_box, criterion_group, criterion_main, Criterion};

use crepe::crepe;

const MAX_PATH_LEN: u32 = 50;

crepe! {
    @input
    struct Edge(i32, i32, u32);

    @output
    struct Walk(i32, i32, u32);

    @output
    struct NoWalk(i32, i32);

    struct Node(i32);

    Node(x) <- Edge(x, _, _);
    Node(x) <- Edge(_, x, _);

    Walk(x, x, 0) <- Node(x);
    Walk(x, z, len1 + len2) <-
        Edge(x, y, len1),
        Walk(y, z, len2),
        (len1 + len2 <= MAX_PATH_LEN);

    NoWalk(x, y) <- Node(x), Node(y), !Walk(x, y, _);
}

fn walk(n: usize) -> (usize, usize) {
    let n = n as i32;
    let mut edges = Vec::new();
    for i in 0..n {
        for j in 0..n {
            if i + j % 50 < 2 {
                edges.push(Edge(i, j, 5));
            }
        }
    }

    let mut runtime = Crepe::new();
    runtime.extend(edges);
    let (walk, nowalk) = runtime.run_with_hasher::<fnv::FnvBuildHasher>();
    (walk.len(), nowalk.len())
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "walk",
        |b, input| {
            b.iter(|| walk(black_box(*input)));
        },
        vec![128, 256, 512],
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
