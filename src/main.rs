
#[macro_use]
mod prover;
mod ast;
mod client;

use std::env;



fn main() -> Result<(), ()> {
    if let Err(why) = client::start() {
        eprintln!("{}", why);
    };

    Ok( () )
}

#[cfg(test)]
mod tests {
    use crate::prover::service_proof_request;

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
        // we should NOT be able to prove that `ace` is true
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
    #[test]
    fn medium_proof_0() {
        let givens = vec![
            "(red and blue and green) or (red and blue and yellow) or (blue and green and orange) or (blue)",
            "(red and lightning) or (red and fire) or (red and anger)",
            "(blue implies water) or (blue implies sadness)",
            "(yellow and orange) or (zeta and not zeta)",
            "(yellow and orange) implies (not red and not green)",
            "(water or sadness) implies tears"
        ];
        let goal = "tears";
        let success = service_proof_request(givens.as_slice(), goal).expect("should not error");
        // (yellow and orange) or (zeta and not zeta)           given
        // (yellow and orange)                                  in either case, it follows trivially or by explosion
        // (yellow and orange) implies (not red and not green)  given
        // (not red and not green)                              follows from above
        // blue                                                 blue is the only option from the first given since red and green are both false
        // (blue implies water) or (blue implies sadness)       given
        // (water or sadness)                                   since blue is true, it follows from the cases above
        // (water or sadness) implies tears                     given
        // tears  QED
        assert_eq!(success, true);
    }
}
