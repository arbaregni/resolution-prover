use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use resolution_prover::{find_proof};

macro_rules! bench {
    (
        $name:ident,
        GIVENS: $($given:expr),* $(,)*
        =>
        GOAL: $goal:expr $(,)*
    ) => {
        fn $name(c: &mut Criterion) {
            let givens = criterion::black_box(vec![
                $( $given ),*
            ]);
            let goal = criterion::black_box($goal);
            c.bench_function(stringify!($name), |b| b.iter(|| {
                find_proof(givens.as_slice(), goal)
            }));
        }
    };
}

bench!(switching_thm,
    GIVENS:
           =>
    GOAL: "(forall x: forall y: P(x, y)) <=> (forall y: forall x: P(x, y))",
);


bench!(first_order_0,
      GIVENS: "forall x: P(x) implies Q(x)",
              "P(a)",
              =>
      GOAL:   "Q(a)"
);

bench!(first_order_1,
      GIVENS: =>
      GOAL:   "(forall x: forall y: P(x, y)) <=> (forall y: forall x: P(x, y))"
);

bench!(pathing_proof_0,
    GIVENS: "forall x: forall y: forall z: (Path(x,y) & Path(y, z)) => Path(x, z)",
            "Path(a,b)",
            "Path(b,c)",
           =>
    GOAL:   "Path(a,c)",
);

bench!(many_implications,
    GIVENS: "a",
            "a => b",
            "b => c",
            "c => d",
            "d => e",
            "e => f",
            "f => g",
            "g => h",
            "h => i",
            "i => j",
            =>
    GOAL:   "j",
);

/*
bench!(pathing_proof_1,
    GIVENS: "forall x: forall y: forall z: (Path(x,y) & Path(y, z)) => Path(x, z)",
            "Path(a,b)",
            "Path(b,c)",
           =>
    GOAL:   "Path(d,e)",
);

bench!(pathing_proof_2,
    GIVENS: "forall x: forall y: forall z: (Path(x,y) & Path(y, z)) => Path(x, z)",
            "Path(a,b)",
            "Path(b,c)",
            "Path(c, a)"
           =>
    GOAL:   "Path(a,a)",
);
*/

criterion_group!(benches, switching_thm, first_order_0, first_order_1, many_implications, pathing_proof_0); 
criterion_main!(benches);

