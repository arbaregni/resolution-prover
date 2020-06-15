#[macro_use]
mod clause;

pub use clause::*;

use indexmap::set::IndexSet;
use crate::ast::Expr;

/// search for a proof of `query` from `givens`
pub fn find_proof(givens: Vec<Expr<'_>>, goal: Expr<'_>) -> bool {
    let mut interner = ClauseInterner::new();
    let mut clause_set = IndexSet::new();
    // enter all the givens
    for expr in givens {
        expr.into_clauses(&mut clause_set, &mut interner);
    }
    // we do proof by contradiction
    // negate the goal, and if we find a contradiction, that's a proof
    goal
        .negate()
        .into_clauses(&mut clause_set, &mut interner);
    println!("interner: {:#?},\n clause_set: {:#?}", interner, clause_set);
    // search for the contradiction
    has_contradiction(clause_set, &mut interner)
}

pub fn has_contradiction(clause_set: IndexSet<ClauseId>, interner: &mut ClauseInterner) -> bool {
    let mut seen_before = IndexSet::new();
    let mut to_search = clause_set;

    // println!("{:#?}", interner);
    // println!("seen_before: {:#?}", seen_before);
    // println!("to_search: {:#?}", to_search);

    while let Some(clause_id) = to_search.pop() {
        let clause = interner.get(clause_id);
        if clause.is_empty() {
            return true; // found a contradiction!
        }
        // resolve this clause with each clause that we've seen before
        let resolvants = seen_before.iter()
            .map(|id| interner.get(*id))
            .filter_map(|prev| clause.resolve(prev))
            .collect::<Vec<_>>();

        // println!("============================================================");
        // println!("resolving {:?} produced: {:?}", clause, resolvants);

        for resolved in resolvants {
            if resolved.is_empty() {
                return true; // we found a contradiction
            }
            let id = interner.intern_clause(resolved);
            if seen_before.contains(&id) { continue; }
            to_search.insert(id);
        }
        // now that we are done with this id, we can insert it into the seen_before
        seen_before.insert(clause_id);

        // println!("{:#?}", interner);
        // println!("seen_before: {:#?}", seen_before);
        // println!("to_search: {:#?}", to_search);
    }
    false
}

#[cfg(test)]
mod tests {
    use indexmap::set::IndexSet;
    use crate::prover::{Clause, ClauseInterner, has_contradiction, find_proof};
    use crate::ast;
    use crate::ast::{Expr, ExprKind};

    #[test]
    fn clause_builder_0() {
        let clause = Clause::empty()
            .set("p".to_string(), true)
            .set("q".to_string(), false)
            .set("r".to_string(), false)
            .set("s".to_string(), true);
        assert_eq!(clause!(p, ~q, ~r, s), clause);
    }
    #[test]
    fn clause_builder_1() {
        let clause = Clause::empty()
            .set("p".to_string(), false)
            .set("q".to_string(), true)
            .set("r".to_string(), false)
            .set("s".to_string(), true)
            .set("t".to_string(), false);
        assert_eq!(clause!(~p, q, ~r, s, ~t), clause);
    }
    #[test]
    fn clause_builder_2() {
        assert_eq!(clause!(), Clause::empty());
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
    fn resolution_tautology_0() {
        let a = clause!(p, q);
        let b = clause!(~p, ~q);
        assert_eq!(Clause::resolve(&a, &b), None);
    }
    #[test]
    fn resolution_tautology_1() {
        let a = clause!(s, r, t, p, q);
        let b = clause!(~p, ~q);
        assert_eq!(Clause::resolve(&a, &b), None);
    }
    #[test]
    fn resolution_tautology_2() {
        let a = clause!(~s, ~r, p, q);
        let b = clause!(~p, ~q, s, r);
        assert_eq!(Clause::resolve(&a, &b), None);
    }

    #[test]
    fn clause_intern_0() {
        let mut interner = ClauseInterner::new();

        let a = clause!(p, ~q, r).intern(&mut interner);
        let b = clause!(p, ~q, r).intern(&mut interner);
        assert_eq!(a, b);
    }

    #[test]
    fn satisfy_simple_0() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!()); // contradiction immediately

        assert_eq!(has_contradiction(clauses, &mut interner), true); // make sure we recognize the falso in the premise
    }
    #[test]
    fn satisfy_simple_1() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p));
        interner.intern_and_insert(&mut clauses, clause!(~p));

        assert_eq!(has_contradiction(clauses, &mut interner), true); // both p and ~p is a contradiction
    }
    #[test]
    fn satisfy_simple_2() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p, q)); // p or q
        interner.intern_and_insert(&mut clauses, clause!(~p));   // not p, so q is true
        interner.intern_and_insert(&mut clauses, clause!(~q));   // q is not true

        assert_eq!(has_contradiction(clauses, &mut interner), true); // both q and ~q is a contradiction
    }
    #[test]
    fn satisfy_simple_3() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(~p, q)); // p => q
        interner.intern_and_insert(&mut clauses, clause!(p));     // p is true
        interner.intern_and_insert(&mut clauses, clause!(q));     // q is true

        assert_eq!(has_contradiction(clauses, &mut interner), false);         // there is no contradiction
    }
    #[test]
    fn satisfy_simple_4() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(~p, q));  // p => q
        interner.intern_and_insert(&mut clauses, clause!(~q, r));  // q => r
        interner.intern_and_insert(&mut clauses, clause!(p));      // p is true
        interner.intern_and_insert(&mut clauses, clause!(~r));     // r is false

        assert_eq!(has_contradiction(clauses, &mut interner), true);        // there is a contradiction, because we can derive r
    }
    #[test]
    fn satisfy_simple_5() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p, q));   // p or q
        interner.intern_and_insert(&mut clauses, clause!(~p, r));  // not p or q
        interner.intern_and_insert(&mut clauses, clause!(~p, ~r)); // not p or not r
        interner.intern_and_insert(&mut clauses, clause!(p, ~q));  // p or not q

        assert_eq!(has_contradiction(clauses, &mut interner), true);        // there is a contradiction
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
