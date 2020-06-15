
#[macro_use]
mod prover;
mod ast;

use std::env;

/// Parse and the givens and the goal,
/// search for a proof, returning `Some(true)` on success, `Some(false)` otherwise
/// returns `None` upon error
fn service_proof_request(givens: &[&str], goal: &str) -> Result<bool, ()> {
    let givens = givens
        .iter()
        .map(|&source| ast::parse(source))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| {
            eprintln!("{}", e);
        })?;
    let goal = ast::parse(goal)
        .map_err(|e| {
            eprintln!("{}", e);
        })?;
    Ok( prover::find_proof(givens, goal) )
}

fn main() -> Result<(), ()> {
    let givens = vec![
    ];
    let goal = env::args().nth(1).expect("expected argument");
    let success = service_proof_request(givens.as_slice(), goal.as_str())?;
    if success {
        println!("found proof!");
    } else {
        println!("could not find proof.");
    }
    Ok( () )
}
