#[macro_use]
mod clause;

pub use clause::*;

mod search;
pub use search::*;

#[cfg(test)]
mod tests {
    use crate::prover::{Clause, ClosedClauseSet, find_proof, ClauseBuilder};
    use crate::ast::ExprKind;

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
                ExprKind::Literal("it-rains").into(),
                ExprKind::Literal("get-wet").into(),
            ).into(),
            ExprKind::If(
                ExprKind::Literal("get-wet").into(),
                ExprKind::Literal("will-fall").into(),
            ).into(),
            ExprKind::Literal("it-rains").into(),
        ];
        let goal = ExprKind::Literal("will-fall").into();

        assert_eq!(find_proof(givens, goal), true);
    }
    #[test]
    fn provability_simple_1() {
        let givens = vec![
            ExprKind::If(
                ExprKind::Literal("it-rains").into(),    // if it-rains, you will get wet
                ExprKind::Literal("get-wet").into(),
            ).into(),
            ExprKind::If(
                ExprKind::Literal("get-wet").into(),    // if you get wet, you will fall
                ExprKind::Literal("will-fall").into(),
            ).into(),
        ];
        let goal = ExprKind::If( // therefore, if it-rains, you will fall
            ExprKind::Literal("it-rains").into(),
            ExprKind::Literal("will-fall").into(),
        ).into();

        assert_eq!(find_proof(givens, goal), true);
    }
    #[test]
    fn provability_simple_2() {
        let givens = vec![
            ExprKind::If(
                ExprKind::Literal("it-rains").into(),    // if it-rains, you will get wet
                ExprKind::Literal("get-wet").into(),
            ).into(),
            ExprKind::If(
                ExprKind::Literal("get-wet").into(),    // if you get wet, you will fall
                ExprKind::Literal("will-fall").into(),
            ).into(),
        ];
        let goal = ExprKind::Literal("will-fall").into();

        assert_eq!(find_proof(givens, goal), false); // we can't prove definitely that you will fall
    }
    #[test]
    fn provability_simple_3() {
    }
    #[test]
    fn provability_medium_0() {
        let givens = vec![
            // if it rains, you will get wet
            ExprKind::If(
                ExprKind::Literal("it-rains").into(),
                ExprKind::Literal("get-wet").into(),
            ).into(),
            // if you get wet, you will fall
            ExprKind::If(
                ExprKind::Literal("get-wet").into(),
                ExprKind::Literal("will-fall").into(),
            ).into(),
            // if it lightnings, you will be scared
            ExprKind::If(
                ExprKind::Literal("it-lightnings").into(),
                ExprKind::Literal("will-be-scared").into(),
            ).into(),
            // if you're scared, you will fall
            ExprKind::If(
                ExprKind::Literal("will-be-scared").into(),
                ExprKind::Literal("will-fall").into(),
            ).into(),
            // if it hails or snows, you will be slippery
            ExprKind::If(
                ExprKind::Or(vec![
                    ExprKind::Literal("it-hails").into(),
                    ExprKind::Literal("it-snows").into(),
                ]).into(),
                ExprKind::Literal("will-be-slippery").into(),
            ).into(),
            // if you're slippery, you will fall
            ExprKind::If(
                ExprKind::Literal("will-be-slippery").into(),
                ExprKind::Literal("will-fall").into(),
            ).into(),
            // one of these will happen
            ExprKind::Or(vec![
                // it will rain, ...
                ExprKind::Literal("it-rains").into(),
                // or will be clear skies, ...
                ExprKind::Literal("clear-skies").into(),
                // or, will be one of these:
                ExprKind::Or(vec![
                    // all of these will happen:
                    ExprKind::And(vec![
                        // it rains, ...
                        ExprKind::Literal("it-rains").into(),
                        // and, if it rains, it thunders, ...
                        ExprKind::If(
                            ExprKind::Literal("it-rains").into(),
                            ExprKind::Literal("it-thunders").into(),
                        ).into(),
                        // and, if it thunders, it lightnings
                        ExprKind::If(
                            ExprKind::Literal("it-thunders").into(),
                            ExprKind::Literal("it-lightnings").into(),
                        ).into()
                    ]).into(),
                    // or, it will hail
                    ExprKind::Literal("it-hails").into(),
                    // or, it will snow
                    ExprKind::Literal("it-snows").into(),
                ]).into()
            ]).into(),
        ];
        let goal = ExprKind::Or(vec![
            ExprKind::Literal("clear-skies").into(),
            ExprKind::Literal("will-fall").into()
        ]).into();

        assert_eq!(find_proof(givens, goal), true);
    }

}
