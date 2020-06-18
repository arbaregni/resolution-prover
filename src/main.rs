
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

#[cfg(test)]
mod tests {
    use crate::service_proof_request;

    #[test]
    fn simple_proof_0() {
        let givens = vec![
            "fire and ice"
        ];
        let goal = "ice";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        // if both fire and ice are true, then clearly, ice is true
        assert_eq!(success, true);
    }
    #[test]
    fn simple_proof_1() {
        let givens = vec![
            "fire and ice"
        ];
        let goal = "lukewarm-water";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        // we can say nothing about lukewarm-water
        assert_eq!(success, false);
    }
    #[test]
    fn simple_proof_2() {
        let givens = vec![
            "human implies mortal",
            "mortal implies death",
            "socrates implies human",
        ];
        let goal = "socrates implies death";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        assert_eq!(success, true);
    }
    #[test]
    fn simple_proof_3() {
        let givens = vec![
            "(king implies ace) or (not king implies ace)",
            "not ( (king implies ace) and (not king implies ace) )",
            "king",
        ];
        let goal = "ace";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        // king/ace cognitive illusion, thanks selmer bringsjord:
        // (king implies ace) xor (not king implies ace)  . given
        // king                                           . given
        // not king implies ace                           . vacuous implication
        // not (king implies ace)                         . by the xor
        // king and not ace                               . negation of implication
        assert_eq!(success, false);
    }
    #[test]
    fn simple_proof_4() {
        let givens = vec![
            "(king implies ace) or (not king implies ace)",
            "not ( (king implies ace) and (not king implies ace) )",
            "king",
        ];
        let goal = "not ace";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        // king/ace cognitive illusion, thanks selmer bringsjord:
        // (king implies ace) xor (not king implies ace)  . given
        // king                                           . given
        // not king implies ace                           . vacuous implication
        // not (king implies ace)                         . by the xor
        // king and not ace                               . negation of implication
        assert_eq!(success, true);
    }
}
