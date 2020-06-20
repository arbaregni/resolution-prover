use crate::ast::Expr;
use crate::prover::{ClosedClauseSet, Clause};

/// search for a proof of `query` from `givens`
#[allow(dead_code)]
pub fn find_proof(givens: Vec<Expr<'_>>, goal: Expr<'_>) -> bool {
    let mut clause_set = ClosedClauseSet::new();
    // enter all the givens
    for expr in givens {
        expr.into_clauses(&mut clause_set);
    }
    // we do proof by contradiction
    // negate the goal, and if we find a contradiction, that's a proof
    goal
        .negate()
        .into_clauses(&mut clause_set);
    // println!("clause_set: {:#?}", clause_set);
    // search for the contradiction
    clause_set.has_contradiction()
}

impl ClosedClauseSet<'_> {
    pub fn has_contradiction(&mut self) -> bool {
        // every clause strictly before the cutoff has been completely resolved
        let mut cutoff = 0;
        loop {
            if let Some(clause) = self.clauses.get_index(cutoff) {
                if clause.is_empty() {
                    return true; // found a contradiction!
                }
                let to_resolve = self.clauses_with_one_conflict(clause);
                let resolvants = to_resolve
                    .into_iter()
                    .map(|id| self.get(id))
                    .map(|prev| clause.resolve(prev))
                    .collect::<Vec<Clause>>();

                // println!("============================================================");
                // println!("resolving {:?} produced: {:?}", clause, resolvants);

                for resolvant in resolvants.into_iter() {
                    if resolvant.is_empty() {
                        return true; // found a contradiction
                    }
                    self.integrate_clause(resolvant);
                }

                // println!("current set: {:#?}", self);

                // advance the cutoff
                cutoff += 1;

            } else {
                // the cut off has reached the end, and we haven't found an empty clause
                // because everything all the clauses before the cutoff is closed,
                // we know there is no way to get the empty clause
                return false;
            }
        }
    }
}

/*
#[allow(dead_code)]
pub fn has_contradiction(clause_set: IndexSet<ClauseId>, interner: &mut ClosedClauseSet) -> bool {
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
        // resolve this clause with each clause that has exactly one conflict with it
        let to_resolve = interner.clauses_with_one_conflict(clause);
        let resolvants = to_resolve
            .into_iter()
            .map(|id| interner.get(id))
            .filter_map(|prev| clause.resolve(prev))
            .collect::<Vec<_>>();

        println!("============================================================");
        println!("resolving {:?} produced: {:?}", clause, resolvants);

        for resolved in resolvants {
            if resolved.is_empty() {
                return true; // we found a contradiction
            }
            let id = interner.integrate_clause(resolved);
            if seen_before.contains(&id) { continue; }
            to_search.insert(id);
        }
        // now that we are done with this id, we can insert it into the seen_before
        seen_before.insert(clause_id);

        println!("{:#?}", interner);
        println!("seen_before: {:#?}", seen_before);
        println!("to_search: {:#?}", to_search);
    }
    false
}
 */