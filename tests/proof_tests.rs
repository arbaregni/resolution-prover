#[cfg(test)]

use resolution_prover::find_proof;

#[test]
fn simple_proof_0() {
    let givens = vec![
        "fire and ice"
    ];
    let goal = "ice";
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
    // if both fire and ice are true, then clearly, ice is true
    assert_eq!(success, true);
}
#[test]
fn simple_proof_1() {
    let givens = vec![
        "fire and ice"
    ];
    let goal = "lukewarm_water";
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
    // we can say nothing about lukewarm_water
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
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
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
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
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
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
    // king/ace cognitive illusion, thanks selmer bringsjord:
    // (king implies ace) xor (not king implies ace)  . given
    // king                                           . given
    // not king implies ace                           . vacuous implication
    // not (king implies ace)                         . by the xor
    // king and not ace                               . negation of implication
    assert_eq!(success, true);
}
#[test]
fn simple_proof_5() {
    let givens = vec![];
    let goal = "(a xor b) iff not (a iff b)";
    /*
    let g = ast::parse(goal).expect("should parse");
    let not_g = g.negate().normalize_negations().distribute_ors_inward();
    let mut clause_set = ClosedClauseSet::new();
    not_g.make_clause_set(&mut clause_set);
    println!("before: {:#?}", clause_set);
    let _ = clause_set.has_contradiction();
    println!("================\nafter: {:#?}\n================", clause_set);
     */
    let success = find_proof(givens.as_slice(), goal).expect("should not happen");
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
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
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

#[test]
fn first_order_0() {
    let givens = vec![
        "forall x: P(x) implies Q(x)",
        "P(a)",
    ];
    let goal = "Q(a)";
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
    assert_eq!(success, true);
}

#[test]
fn first_order_10() {
    let givens = vec![];
    let goal = "(forall x: forall y: P(x, y)) <=> (forall y: forall x: P(x, y))";
    let success = find_proof(givens.as_slice(), goal).expect("should not error");
    assert_eq!(success, true);
}
