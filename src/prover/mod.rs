#[macro_use]
mod clause;

pub use clause::*;

use indexmap::set::IndexSet;

pub fn is_satisfiable(clauses: IndexSet<ClauseId>, interner: &mut ClauseInterner) -> bool {
    let mut seen_before = IndexSet::new();
    let mut to_search = clauses;

    // println!("{:#?}", interner);
    // println!("seen_before: {:#?}", seen_before);
    // println!("to_search: {:#?}", to_search);

    while let Some(clause_id) = to_search.pop() {
        let clause = interner.get(clause_id);
        if clause.is_empty() {
            return false; // found a contradiction!
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
                return false; // we found a contradiction
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
    true
}
