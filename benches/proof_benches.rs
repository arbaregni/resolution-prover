use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use resolution_prover::{find_proof};

pub fn bench_theorems(c: &mut Criterion) {
    let mut group = c.benchmark_group("Theorems (No givens)");
    let goals = [
        "(forall x: forall y: P(x, y)) <=> (forall y: forall x: P(x, y))"
    ];
    for goal in goals.into_iter() {
        group.bench_with_input(BenchmarkId::new("find proof", goal), goal,
            |b, goal| {
                b.iter(|| find_proof(&[], goal))
            });
    }
}
pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

