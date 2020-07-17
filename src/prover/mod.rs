#[macro_use]
mod clause;
pub use clause::*;

mod term_tree;
pub use term_tree::*;

mod clause_set;
pub use clause_set::*;

use crate::ast;
use crate::error::BoxedErrorTrait;
use crate::ast::Expr;

/// Parse and the givens and the goal,
/// search for a proof, returning `Some(true)` on success, `Some(false)` otherwise
/// returns `None` upon error
pub fn service_proof_request(givens: &[&str], goal: &str) -> Result<bool, BoxedErrorTrait> {
    let givens = givens
        .iter()
        .map(|&source| ast::parse(source))
        .collect::<Result<Vec<_>, _>>()?;
    let goal = ast::parse(goal)?;
    let success = find_proof(givens, goal)?;
    Ok( success )
}

/// search for a proof of `query` from `givens`
fn find_proof(givens: Vec<Expr<'_>>, goal: Expr<'_>) -> Result<bool, BoxedErrorTrait> {
    let mut clause_set = ClosedClauseSet::new();
    // enter all the givens
    for expr in givens {
        expr.into_clauses(&mut clause_set)?;
    }
    // we do proof by contradiction
    // negate the goal, and if we find a contradiction, that's a proof
    goal
        .negate()
        .into_clauses(&mut clause_set)?;
    println!("clause_set: {:#?}", clause_set);
    // search for the contradiction
    let success = clause_set.has_contradiction();

    println!("after: {:#?}", clause_set);
    Ok( success )
}

#[cfg(test)]
mod tests {
    use crate::prover::{Clause, ClosedClauseSet, find_proof, ClauseBuilder};
    use crate::ast::{ExprKind, Term};

    #[test]
    fn clause_builder_0() {
        let clause = ClauseBuilder::new()
            .set("p", true)
            .set("q", false)
            .set("r", false)
            .set("s", true)
            .finish().expect("not a tautology");
        assert_eq!(clause!(p, ~q, ~r, s), clause);
    }
    #[test]
    fn clause_builder_1() {
        let clause = ClauseBuilder::new()
            .set("p", false)
            .set("q", true)
            .set("r", false)
            .set("s", true)
            .set("t", false)
            .finish().expect("not a tautology");
        assert_eq!(clause!(~p, q, ~r, s, ~t), clause);
    }
    #[test]
    fn clause_builder_2() {
        let clause = ClauseBuilder::new()
            .finish().expect("not a tautology");
        assert_eq!(clause!(), clause);
    }

    #[test]
    fn resolution_simple_0() {
        let a = clause!(p, q);
        let b = clause!(~q, r);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(p, r)));
    }
    #[test]
    fn resolution_simple_1() {
        let a = clause!(~p, q); // equivalent to p -> q
        let b = clause!(p);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(q)));
    }
    #[test]
    fn resolution_simple_2() {
        let a = clause!(p);
        let b = clause!(~p);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!()));
    }
    #[test]
    fn resolution_simple_3() {
        let a = clause!(~m, p, q);
        let b = clause!(~p, q);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(~m, q)));
    }

    #[test]
    fn builder_tautology_0() {
        let opt_clause = ClauseBuilder::new()
            .set("p", true)
            .set("p", false)
            .finish();
        assert_eq!(opt_clause, None);
    }
    #[test]
    fn builder_redundant_0() {
        let opt_clause = ClauseBuilder::new()
            .set("q", true)
            .set("q", true)
            .set("p", false)
            .finish();
        let expected = Some(clause!(~p, q));
        assert_eq!(opt_clause, expected);
    }

    #[test]
    fn clause_intern_0() {
        let mut interner = ClosedClauseSet::new();

        let a = interner.integrate_clause(clause!(p, ~q, r));
        let b = interner.integrate_clause(clause!(p, ~q, r));
        assert_eq!(a, b);
    }


    #[test]
    fn satisfy_simple_0() {
        let mut clause_set = ClosedClauseSet::new();

        clause_set.integrate_clause(clause!()); // contradiction immediately

        assert_eq!(clause_set.has_contradiction(), true); // make sure we recognize the falso in the premise
    }
    #[test]
    fn satisfy_simple_1() {
        let mut clause_set = ClosedClauseSet::new();

        clause_set.integrate_clause(clause!(p));
        clause_set.integrate_clause(clause!(~p));

        assert_eq!(clause_set.has_contradiction(), true); // both p and ~p is a contradiction
    }
    #[test]
    fn satisfy_simple_2() {
        let mut clause_set = ClosedClauseSet::new();

        clause_set.integrate_clause(clause!(p, q)); // p or q
        clause_set.integrate_clause(clause!(~p));   // not p, so q is true
        clause_set.integrate_clause(clause!(~q));   // q is not true

        assert_eq!(clause_set.has_contradiction(), true); // both q and ~q is a contradiction
    }
    #[test]
    fn satisfy_simple_3() {
        let mut clause_set= ClosedClauseSet::new();

        clause_set.integrate_clause(clause!(~p, q)); // p => q
        clause_set.integrate_clause(clause!(p));     // p is true
        clause_set.integrate_clause(clause!(q));     // q is true

        assert_eq!(clause_set.has_contradiction(), false);         // there is no contradiction
    }
    #[test]
    fn satisfy_simple_4() {
        let mut clause_set  = ClosedClauseSet::new();

        clause_set.integrate_clause(clause!(~p, q));  // p => q
        clause_set.integrate_clause(clause!(~q, r));  // q => r
        clause_set.integrate_clause(clause!(p));      // p is true
        clause_set.integrate_clause(clause!(~r));     // r is false

        assert_eq!(clause_set.has_contradiction(), true);        // there is a contradiction, because we can derive r
    }
    #[test]
    fn satisfy_simple_5() {
        let mut clause_set = ClosedClauseSet::new();

        clause_set.integrate_clause(clause!(p, q));   // p or q
        clause_set.integrate_clause(clause!(~p, r));  // not p or r
        clause_set.integrate_clause(clause!(~p, ~r)); // not p or not r
        clause_set.integrate_clause(clause!(p, ~q));  // p or not q

        // derivation of paradox:
        // (1) p or q       given
        // (2) p or ~q      given
        // (3) p            resolution (1, 2)
        // (4) ~p or r      given
        // (5) r            resolution (3, 4)
        // (6) ~p or ~r     given
        // (7) ~r           resolution (3, 6)
        // (8) {}           resolution (5, 7)

        assert_eq!(clause_set.has_contradiction(), true);        // there is a contradiction
    }
    #[test]
    fn satisfy_fol_0() {
        let mut clause_set = ClosedClauseSet::new();

        // P(x) implies Q(x)
        let clause = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::variable("x"),
            ]), false)
            .set_lit(Term::predicate("Q", vec![
                Term::variable("x"),
            ]), true)
            .finish().expect("not a tautology");
        clause_set.integrate_clause(clause);

        // P(a)
        let clause = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::atom("a"),
            ]), true)
            .finish().expect("not a tautology");
        clause_set.integrate_clause(clause);

        assert_eq!(clause_set.has_contradiction(), false);

        // make sure that we've derived what Q(a)
        let clause = ClauseBuilder::new()
            .set_lit(Term::predicate("Q", vec![
                Term::atom("a"),
            ]), true)
            .finish().expect("not a tautology");

        println!("{:#?}", clause_set);
        assert!(clause_set.clauses.contains(&clause));
    }
    #[test]
    fn satisfy_fol_1() {
        let mut clause_set = ClosedClauseSet::new();

        // P(x) or P(y)
        let clause = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::variable("x"),
            ]), true)
            .set_lit(Term::predicate("P", vec![
                Term::variable("y"),
            ]), true)
            .finish().expect("not a tautology");
        clause_set.integrate_clause(clause);

        // ~P(a)
        let clause = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::atom("a"),
            ]), false)
            .finish().expect("not a tautology");
        clause_set.integrate_clause(clause);

        let success = clause_set.has_contradiction();
        // derivation:
        // P(x) or P(y)
        // P(x)           reduce (factor) by unifying x and y
        // P(a)           unify x with a
        // ~P(a)
        // contradiction!
        println!("{:#?}", clause_set);
        assert_eq!(success, true);
    }
    #[test]
    fn satisfy_fol_2() {
        // P(u) or P(f(u))
        let clause_0 = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::variable("u")
            ]), true)
            .set_lit(Term::predicate("P", vec![
                Term::predicate("f", vec![
                    Term::variable("u")
                ])
            ]), true)
            .finish().expect("not a tautology");
        // ~P(v) or P(f(w))
        let clause_1 = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::variable("v")
            ]), false)
            .set_lit(Term::predicate("P", vec![
                Term::predicate("f", vec![
                    Term::variable("w")
                ])
            ]), true)
            .finish().expect("not a tautology");
        // ~P(x) or not P(f(x))
        let clause_2 = ClauseBuilder::new()
            .set_lit(Term::predicate("P", vec![
                Term::variable("x")
            ]), false)
            .set_lit(Term::predicate("P", vec![
                Term::predicate("f", vec![
                    Term::variable("x")
                ])
            ]), false)
            .finish().expect("not a tautology");
        let mut clause_set = ClosedClauseSet::new();
        clause_set.integrate_clause(clause_0);
        clause_set.integrate_clause(clause_1);
        clause_set.integrate_clause(clause_2);
        let success = clause_set.has_contradiction();
        // derivation of a contradiction:
        // 0.  P(u) or  P(f(u))  given 0
        // 1. ~P(v) or  P(f(w))  given 1
        // 2. ~P(x) or ~P(f(x))  given 2
        // 3.  P(u) or P(f(w))   resolve (0) and (1), with v = f(u)
        // 4.  P(f(w))           factor (3) with u = f(w)
        // 5. ~P(f(f(w)))        resolve (4) and (2) with x = f(w)
        // 6. :(

        println!("{:#?}", clause_set);
        assert_eq!(success, true);

    }

    #[test]
    fn provability_simple_0() {
        let givens = vec![
            ExprKind::If(
                Term::atom("it-rains").into(),
                Term::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                Term::atom("get-wet").into(),
                Term::atom("will-fall").into(),
            ).into(),
            Term::atom("it-rains").into(),
        ];
        let goal = Term::atom("will-fall").into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, true);
    }
    #[test]
    fn provability_simple_1() {
        let givens = vec![
            ExprKind::If(
                Term::atom("it-rains").into(),    // if it-rains, you will get wet
                Term::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                Term::atom("get-wet").into(),    // if you get wet, you will fall
                Term::atom("will-fall").into(),
            ).into(),
        ];
        let goal = ExprKind::If( // therefore, if it-rains, you will fall
            Term::atom("it-rains").into(),
                                 Term::atom("will-fall").into(),
        ).into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, true);
    }
    #[test]
    fn provability_simple_2() {
        let givens = vec![
            ExprKind::If(
                Term::atom("it-rains").into(),    // if it-rains, you will get wet
                Term::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                Term::atom("get-wet").into(),    // if you get wet, you will fall
                Term::atom("will-fall").into(),
            ).into(),
        ];
        let goal = Term::atom("will-fall").into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, false); // we can't prove definitely that you will fall
    }
    #[test]
    fn provability_simple_3() {
        let givens = vec![
            ExprKind::Or(vec![
                Term::atom("p").into(),
                ExprKind::Not(
                    Term::atom("q").into(),
                ).into(),
             ]).into(),
            ExprKind::Or(vec![
                Term::atom("q").into(),
                ExprKind::Not(
                    Term::atom("p").into(),
                ).into(),
            ]).into(),
        ];
        // this is a consistent set of givens
        // we should NOT be able to prove an arbitrary formula
        let goal = Term::atom("zeta").into();

        let success = find_proof(givens, goal).expect("should not error");
        assert_eq!(success, false);
    }

    #[test]
    fn provability_medium_0() {
        let givens = vec![
            // if it rains, you will get wet
            ExprKind::If(
                Term::atom("it-rains").into(),
                Term::atom("get-wet").into(),
            ).into(),
            // if you get wet, you will fall
            ExprKind::If(
                Term::atom("get-wet").into(),
                Term::atom("will-fall").into(),
            ).into(),
            // if it lightnings, you will be scared
            ExprKind::If(
                Term::atom("it-lightnings").into(),
                Term::atom("will-be-scared").into(),
            ).into(),
            // if you're scared, you will fall
            ExprKind::If(
                Term::atom("will-be-scared").into(),
                Term::atom("will-fall").into(),
            ).into(),
            // if it hails or snows, you will be slippery
            ExprKind::If(
                ExprKind::Or(vec![
                    Term::atom("it-hails").into(),
                    Term::atom("it-snows").into(),
                ]).into(),
                Term::atom("will-be-slippery").into(),
            ).into(),
            // if you're slippery, you will fall
            ExprKind::If(
                Term::atom("will-be-slippery").into(),
                Term::atom("will-fall").into(),
            ).into(),
            // one of these will happen
            ExprKind::Or(vec![
                // it will rain, ...
                Term::atom("it-rains").into(),
                // or will be clear skies, ...
                Term::atom("clear-skies").into(),
                // or, will be one of these:
                ExprKind::Or(vec![
                    // all of these will happen:
                    ExprKind::And(vec![
                        // it rains, ...
                        Term::atom("it-rains").into(),
                        // and, if it rains, it thunders, ...
                        ExprKind::If(
                            Term::atom("it-rains").into(),
                            Term::atom("it-thunders").into(),
                        ).into(),
                        // and, if it thunders, it lightnings
                        ExprKind::If(
                            Term::atom("it-thunders").into(),
                            Term::atom("it-lightnings").into(),
                        ).into()
                    ]).into(),
                    // or, it will hail
                    Term::atom("it-hails").into(),
                    // or, it will snow
                    Term::atom("it-snows").into(),
                ]).into()
            ]).into(),
        ];
        let goal = ExprKind::Or(vec![
            Term::atom("clear-skies").into(),
            Term::atom("will-fall").into()
        ]).into();
        let success = find_proof(givens, goal).expect("should not error");
        assert_eq!(success, true);
    }

}
