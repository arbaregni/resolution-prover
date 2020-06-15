use indexmap::set::IndexSet;
use crate::ast::Expr;
use crate::prover::{ClauseInterner, ClauseId};

/// search for a proof of `query` from `givens`
#[allow(dead_code)]
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

#[allow(dead_code)]
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