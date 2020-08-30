fn main() {
    let givens = vec![
        "forall x: forall y: forall z: (Path(x,y) & Path(y,z)) => Path(x,z)",
    ];
    let goal = "Path(d, e)";
    let result = resolution_prover::find_proof(givens.as_slice(), goal);
    println!("result: {:?}", result);
}