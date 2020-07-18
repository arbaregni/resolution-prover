use crate::prover::{Clause, TermTree, ClauseBuilder};
use indexmap::set::IndexSet;
use std::collections::HashMap;
use crate::ast::{Term};
use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// id's used to reference interned clauses
pub struct ClauseId(usize);

#[derive(Debug)]
/// interns clauses, and provides lookup by variable and truth value
pub struct ClosedClauseSet {
    /// the set of all clauses we have encountered thus far
    pub clauses: IndexSet<Clause>,

    /// retrieve terms that could be unifiable
    term_tree: TermTree,

    /// maps terms to their positive/negative occurrences in clauses
    occurrences: HashMap<Term, Occurrences>
}

impl ClosedClauseSet {
    pub fn new() -> ClosedClauseSet {
        ClosedClauseSet {
            clauses: IndexSet::new(),
            term_tree: TermTree::new(),
            occurrences: HashMap::new(),
        }
    }
    /// Returns a vector of all clauses we can get by applying unifying terms inside the clause
    /// For instance:
    ///    `{P($x), P($y), Q($x, $y)}` may be factored to:
    ///     `{P($x), Q($x, $x)}` via `$y -> $x`
    ///     `{P($y), Q($y, $y)}` via `$x -> $y`
    pub fn factors(&self, clause: &Clause) -> Vec<Clause> {
        // test pairwise for possible unifiers
        let mut subs = Vec::new();
        for (x, x_truth) in clause.iter() {
            for (y, y_truth) in clause.iter() {
                if *x_truth != *y_truth { continue; }
                if let Some(sub) = x.unify(y) {
                    if sub.is_empty() { continue; }
                    subs.push(sub);
                }
            }
        }
        // apply each of those unifiers to our clause and reduce
        subs.into_iter()
            .filter_map(|sub| {
                let mut builder = ClauseBuilder::new();
                for (term, truth_value) in clause.iter() {
                    // apply the substitution and insert the term
                    let mapped = term.substitute(&sub);
                    builder.insert(mapped, *truth_value);
                }
                builder.finish() // tautologies will get filtered out
            })
            .collect::<Vec<_>>()
    }
    /// Inserts the clause, providing the index into the set
    /// Does not search for resolutions and factoring yet
    pub fn integrate_clause(&mut self, clause: Clause) -> ClauseId {
        let (idx, _) = self.clauses.insert_full(clause);
        let clause_id = ClauseId(idx);
        let clause: &Clause = self.clauses.get_index(idx).expect("missing clause");
        for (term, truth_value) in clause.iter() {
            // lookup the literal, and insert a new reference
            self.term_tree.update(term.clone());
            self.occurrences
                .entry(term.clone())
                .or_insert(Occurrences::new())
                .insert(*truth_value, clause_id)
        }
        // println!("integrated new clause, clauses: {:#?}", self.clauses);
        clause_id
    }
    pub fn get<'s>(&'s self, id: ClauseId) -> &'s Clause {
        self.clauses.get_index(id.0).expect("an invalid ClauseId was created")
    }
    pub fn has_contradiction(&mut self) -> bool {
        // every clause strictly before the cutoff has been completely resolved
        let mut cutoff = 0;
        loop {
            if let Some(clause) = self.clauses.get_index(cutoff) {
                if clause.is_empty() {
                    return true; // found a contradiction!
                }
                let mut products = vec![];
                // get all the resolvants
                for (query_term, truth_value) in clause.iter() {
                    // increment the count of each clause with the same name, but opposite truth_value
                    // get the terms for the *opposite* truth value
                    println!("searching for candidates to unify: {:?}", query_term);
                    for term in self.term_tree.unification_candidates(query_term.clone()) {
                        if let Some(sub) = query_term.unify(&term) {
                            println!("unifying {:?} & {:?} via {:?}", query_term, term, sub);
                            let occr = self.occurrences.get(&term).expect("expected occurrences to be complete");
                            for id in occr.get(!truth_value) {
                                println!("present in {:?}", id);
                                let other = self.get(*id);
                                if let Some(resolvant) = clause.resolve_under_substitution(other, &sub) {
                                    products.push(resolvant);
                                }
                            }
                        }
                    }
                }
                // add every reduction of a clause (factoring rule) to the vector
                products.extend_from_slice(&self.factors(clause));

                println!("============================================================");
                println!("resolving {:?} produced: {:?}", clause, products);

                for product in products.into_iter() {
                    if product.is_empty() {
                        return true; // found a contradiction
                    }
                    self.integrate_clause(product);
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

#[derive(Debug, Clone)]
struct Occurrences {
    truthy: Vec<ClauseId>,
    falsy: Vec<ClauseId>,
}
impl Occurrences {
    fn new() -> Occurrences {
        Occurrences {
            truthy: vec![],
            falsy: vec![]
        }
    }
    fn get(&self, truth_value: bool) -> &[ClauseId] {
        if truth_value {
            self.truthy.as_slice()
        } else {
            self.falsy.as_slice()
        }
    }
    fn insert(&mut self, truth_value: bool, clause_id: ClauseId) {
        let ids = if truth_value {
            &mut self.truthy
        } else {
            &mut self.falsy
        };
        ids.push(clause_id);
        ids.dedup();
    }
}

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Clause {}", self.0)
    }
}
