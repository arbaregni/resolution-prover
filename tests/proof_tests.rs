#[cfg(test)]

use resolution_prover::find_proof;

macro_rules! test {
    (
        $name:ident, $success:expr, 
        GIVENS: $($given:expr),* $(,)*
        =>
        GOAL: $goal:expr $(,)*
    ) => {
        #[test]
        fn $name() {
            let givens = vec![
                $( $given ),*
            ];
            let success = find_proof(givens.as_slice(), $goal).expect("should not error");
            assert_eq!(success, $success);
        }
    };
}

// if both fire and ice are true, then clearly, ice is true
test!(prop_calc_0, true,
    GIVENS: "fire and ice",
        =>  
    GOAL:  "ice"
);

// if both fire and ice are true, then clearly, ice is true
test!(prop_calc_1, true,
    GIVENS: "fire and ice",
        =>  
    GOAL:  "ice"
);

test!(prop_calc_2, true,
      GIVENS: "human implies mortal",
              "mortal implies death",
              "socrates implies human",
              =>
      GOAL:   "socrates implies death"
);

// king/ace cognitive illusion, thanks selmer bringsjord:
// (king implies ace) xor (not king implies ace)  . given
// king                                           . given
// not king implies ace                           . vacuous implication
// not (king implies ace)                         . by the xor
// king and not ace                               . negation of implication
// we should NOT be able to prove that `ace` is true
test!(king_ace_neg, false,
      GIVENS: "(king implies ace) or (not king implies ace)",
              "not ( (king implies ace) and (not king implies ace) )",
              "king",
              =>
      GOAL:   "ace"
);

// we SHOULD be able to prove `not ace`
test!(king_ace_pos, true,
      GIVENS: "(king implies ace) or (not king implies ace)",
              "not ( (king implies ace) and (not king implies ace) )",
              "king",
              =>
      GOAL:   "not ace"
);

test!(prop_calc_3, true,
      GIVENS: 
              =>
      GOAL:   "(a xor b) iff not (a iff b)"
);

// (yellow and orange) or (zeta and not zeta)           given
// (yellow and orange)                                  in either case, it follows trivially or by explosion
// (yellow and orange) implies (not red and not green)  given
// (not red and not green)                              follows from above
// blue                                                 blue is the only option from the first given since red and green are both false
// (blue implies water) or (blue implies sadness)       given
// (water or sadness)                                   since blue is true, it follows from the cases above
// (water or sadness) implies tears                     given
// tears  QED
test!(large_prop_calc_0, true,
      GIVENS: "(red and blue and green) or (red and blue and yellow) or (blue and green and orange) or (blue)",
              "(red and lightning) or (red and fire) or (red and anger)",
              "(blue implies water) or (blue implies sadness)",
              "(yellow and orange) or (zeta and not zeta)",
              "(yellow and orange) implies (not red and not green)",
              "(water or sadness) implies tears"
              =>
      GOAL:   "tears"
);

test!(first_order_0, true,
      GIVENS: "forall x: P(x) implies Q(x)",
              "P(a)",
              =>
      GOAL:   "Q(a)"
);

test!(first_order_1, true,
      GIVENS: =>
      GOAL:   "(forall x: forall y: P(x, y)) <=> (forall y: forall x: P(x, y))"
);

test!(first_order_2, true,
      GIVENS: =>
      GOAL:   "forall x: P(x) -> exists x: P(x)"
);

test!(first_order_3, true,
      GIVENS: =>
      GOAL:   "(forall x: P(x)) -> P(c)"
);

test!(first_order_4, true,
      GIVENS: =>
      GOAL:   "P(c) -> exists x: P(x)"
);

test!(first_order_5, true,
      GIVENS: =>
      GOAL:   "forall x: (P(x) <=> ~~P(x))"
);

test!(first_order_6, true,
      GIVENS: =>
      GOAL:   "forall x: (not (P(x) and Q(x))) => (~P(x) or ~Q(x))"
);

test!(first_order_8, false,
      GIVENS: =>
      GOAL:   "P(c) -> forall x: P(x)"
);

test!(pathing_proof_0, false,
      GIVENS: "forall x: forall y: Path(x, y) => Path(y, x)",
              "forall x: forall y: forall z: (Path(x, y) and Path(y, z)) => Path(x, z)",
              =>
      GOAL:   "Path(a, c) or Path(z, m)"
);

test!(pathing_proof_1, false,
      GIVENS: "forall x: forall y: Path(x, y) => Path(y, x)",
              "forall x: forall y: forall z: (Path(x, y) and Path(y, z)) => Path(x, z)",
              =>
      GOAL:   "exists c: Path(c, c)"
);

test!(pathing_proof_2, true,
      GIVENS: "forall x: forall y: Path(x, y) => Path(y, x)",
              "forall x: forall y: forall z: (Path(x, y) and Path(y, z)) => Path(x, z)",
              "forall x: forall y: (Broken(x) and Path(x, y)) => Broken(y)",
              "Path(a, b)",
              "Path(b, c) or Path(d, b)",
              "Broken(c) and Broken(d)",
              =>
      GOAL:   "Broken(a)",
);

