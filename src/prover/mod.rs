#[macro_use]
mod clause;

pub use clause::*;

mod search;
pub use search::*;
use crate::ast;
use crate::error::BoxedErrorTrait;

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

#[cfg(test)]
mod tests {
    use crate::prover::{Clause, ClosedClauseSet, find_proof, ClauseBuilder};
    use crate::ast::{ExprKind, LiteralExpr};

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
        assert_eq!(Clause::resolve(&a, &b), clause!(p, r));
    }
    #[test]
    fn resolution_simple_1() {
        let a = clause!(~p, q); // equivalent to p -> q
        let b = clause!(p);
        assert_eq!(Clause::resolve(&a, &b), clause!(q));
    }
    #[test]
    fn resolution_simple_2() {
        let a = clause!(p);
        let b = clause!(~p);
        assert_eq!(Clause::resolve(&a, &b), clause!());
    }
    #[test]
    fn resolution_simple_3() {
        let a = clause!(~m, p, q);
        let b = clause!(~p, q);
        assert_eq!(Clause::resolve(&a, &b), clause!(~m, q));
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
    fn provability_simple_0() {
        let givens = vec![
            ExprKind::If(
                LiteralExpr::atom("it-rains").into(),
                LiteralExpr::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                LiteralExpr::atom("get-wet").into(),
                LiteralExpr::atom("will-fall").into(),
            ).into(),
            LiteralExpr::atom("it-rains").into(),
        ];
        let goal = LiteralExpr::atom("will-fall").into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, true);
    }
    #[test]
    fn provability_simple_1() {
        let givens = vec![
            ExprKind::If(
                LiteralExpr::atom("it-rains").into(),    // if it-rains, you will get wet
                LiteralExpr::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                LiteralExpr::atom("get-wet").into(),    // if you get wet, you will fall
                LiteralExpr::atom("will-fall").into(),
            ).into(),
        ];
        let goal = ExprKind::If( // therefore, if it-rains, you will fall
            LiteralExpr::atom("it-rains").into(),
                                 LiteralExpr::atom("will-fall").into(),
        ).into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, true);
    }
    #[test]
    fn provability_simple_2() {
        let givens = vec![
            ExprKind::If(
                LiteralExpr::atom("it-rains").into(),    // if it-rains, you will get wet
                LiteralExpr::atom("get-wet").into(),
            ).into(),
            ExprKind::If(
                LiteralExpr::atom("get-wet").into(),    // if you get wet, you will fall
                LiteralExpr::atom("will-fall").into(),
            ).into(),
        ];
        let goal = LiteralExpr::atom("will-fall").into();

        let success = find_proof(givens, goal).expect("should not fail");
        assert_eq!(success, false); // we can't prove definitely that you will fall
    }
    #[test]
    fn provability_simple_3() {
        let givens = vec![
            ExprKind::Or(vec![
                LiteralExpr::atom("p").into(),
                ExprKind::Not(
                    LiteralExpr::atom("q").into(),
                ).into(),
             ]).into(),
            ExprKind::Or(vec![
                LiteralExpr::atom("q").into(),
                ExprKind::Not(
                    LiteralExpr::atom("p").into(),
                ).into(),
            ]).into(),
        ];
        // this is a consistent set of givens
        // we should NOT be able to prove an arbitrary formula
        let goal = LiteralExpr::atom("zeta").into();

        let success = find_proof(givens, goal).expect("should not error");
        assert_eq!(success, false);
    }

    #[test]
    fn provability_medium_0() {
        let givens = vec![
            // if it rains, you will get wet
            ExprKind::If(
                LiteralExpr::atom("it-rains").into(),
                LiteralExpr::atom("get-wet").into(),
            ).into(),
            // if you get wet, you will fall
            ExprKind::If(
                LiteralExpr::atom("get-wet").into(),
                LiteralExpr::atom("will-fall").into(),
            ).into(),
            // if it lightnings, you will be scared
            ExprKind::If(
                LiteralExpr::atom("it-lightnings").into(),
                LiteralExpr::atom("will-be-scared").into(),
            ).into(),
            // if you're scared, you will fall
            ExprKind::If(
                LiteralExpr::atom("will-be-scared").into(),
                LiteralExpr::atom("will-fall").into(),
            ).into(),
            // if it hails or snows, you will be slippery
            ExprKind::If(
                ExprKind::Or(vec![
                    LiteralExpr::atom("it-hails").into(),
                    LiteralExpr::atom("it-snows").into(),
                ]).into(),
                LiteralExpr::atom("will-be-slippery").into(),
            ).into(),
            // if you're slippery, you will fall
            ExprKind::If(
                LiteralExpr::atom("will-be-slippery").into(),
                LiteralExpr::atom("will-fall").into(),
            ).into(),
            // one of these will happen
            ExprKind::Or(vec![
                // it will rain, ...
                LiteralExpr::atom("it-rains").into(),
                // or will be clear skies, ...
                LiteralExpr::atom("clear-skies").into(),
                // or, will be one of these:
                ExprKind::Or(vec![
                    // all of these will happen:
                    ExprKind::And(vec![
                        // it rains, ...
                        LiteralExpr::atom("it-rains").into(),
                        // and, if it rains, it thunders, ...
                        ExprKind::If(
                            LiteralExpr::atom("it-rains").into(),
                            LiteralExpr::atom("it-thunders").into(),
                        ).into(),
                        // and, if it thunders, it lightnings
                        ExprKind::If(
                            LiteralExpr::atom("it-thunders").into(),
                            LiteralExpr::atom("it-lightnings").into(),
                        ).into()
                    ]).into(),
                    // or, it will hail
                    LiteralExpr::atom("it-hails").into(),
                    // or, it will snow
                    LiteralExpr::atom("it-snows").into(),
                ]).into()
            ]).into(),
        ];
        let goal = ExprKind::Or(vec![
            LiteralExpr::atom("clear-skies").into(),
            LiteralExpr::atom("will-fall").into()
        ]).into();
        let success = find_proof(givens, goal).expect("should not error");
        assert_eq!(success, true);
    }

}
