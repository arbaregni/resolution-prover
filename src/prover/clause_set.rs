use crate::prover::{Clause, TermTree};
use indexmap::set::IndexSet;
use std::collections::{HashMap, BinaryHeap};
use crate::ast::{Term, Substitution};
use std::{fmt};
use crate::error::BoxedErrorTrait;
use serenity::static_assertions::_core::cmp::Ordering;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// id's used to reference interned clauses
pub struct ClauseId(usize);

#[derive(Debug)]
/// interns clauses, and provides lookup by variable and truth value
pub struct ClosedClauseSet {
    /// the set of all clauses we have encountered thus far
    pub clauses: IndexSet<Clause>,

    /// retrieve terms that could be unifiable
    pub term_tree: TermTree,

    /// Represent actions which lead to other states in a search space
    action_queue: BinaryHeap<Action>,

    /// maps terms to their positive/negative occurrences in clauses
    occurrences: HashMap<Term, Occurrences>,

    /// Set to true if the empty set is contained here
    is_inconsistent: bool,
}

impl ClosedClauseSet {
    pub fn new() -> ClosedClauseSet {
        ClosedClauseSet {
            clauses: IndexSet::new(),
            term_tree: TermTree::new(),
            action_queue: BinaryHeap::new(),
            occurrences: HashMap::new(),
            is_inconsistent: false,
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
                clause.factor_under_substitution(&sub)
            })
            .collect::<Vec<_>>()
    }
    /// Inserts the clause, providing the index into the set
    /// Updates the term tree and occurrences with all of its terms,
    /// Then updates the action queue with possible resolution partners and factorings
    pub fn integrate_clause(&mut self, clause: Clause) -> Result<ClauseId, BoxedErrorTrait> {
        // println!("integrating {:?}", clause);

        let (idx, _) = self.clauses.insert_full(clause);
        let clause_id = ClauseId(idx);
        let clause: &Clause = self.clauses.get_index(idx).expect("missing clause");

        if clause.is_empty() {
            self.is_inconsistent = true;
            // return early: the empty clause doesn't have any terms to manipulate
            return Ok(clause_id);
        }
        // println!("before updating term_tree = {:#?}", self.term_tree);

        for (term, truth_value) in clause.iter() {
            // lookup the literal, and insert a new reference
            self.term_tree.update(term.clone());
            self.occurrences
                .entry(term.clone())
                .or_insert(Occurrences::new())
                .insert(*truth_value, clause_id)
        }
        // println!("after updating term_tree = {:#?}", self.term_tree);

        // search for possible resolution partners or ways to factor this clause
        // map clauses that share at least one term of opposing truth value, up to unification
        // to pairs of substitutions and a count of the number of times that clauses & unifier has appeared
        let mut partners = HashMap::new();

        // substitutions that could reduce the given clause
        let mut factorizations = Vec::new();

        for (query_term, truth_value) in clause.iter() {
            for term in self.term_tree.unification_candidates(query_term.clone())? {
                // anything with `term` as an opposite truth value is a possible resolution partner
                let occr = self.occurrences.get(&term).expect("expected occurrences to be complete");
                for id in occr.get(!truth_value) {
                    // no point trying to resolve with your self
                    if *id == clause_id { continue; }
                    let new_sub = match query_term.unify(&term) {
                        Some(sub) => sub,
                        None => continue,
                    };
                    let hits = partners.entry(*id)
                        .or_insert(Vec::with_capacity(1));
                    // find our substitution (if it already exists) and increment the count, or create a count of 1
                    update_or_insert(hits, new_sub, 1, |count| {
                        *count += 1;
                    });
                }
                // if we found a DIFFERENT term that we could unify with in the same clause,
                // its possible to reduce the clause
                if term != *query_term && clause.contains(&term, *truth_value) {
                    if let Some(sub) = query_term.unify(&term) {
                        // insert the sub unless it already exists
                        update_or_insert(&mut factorizations, sub, (), |_| { });
                    }
                }

            }
        }
        // stick the resolution partners into the priority queue
        for (other_id, sub) in partners.into_iter()
            .flat_map(|(other_id, hits)| {
                hits.into_iter()
                    .filter_map(move |(sub, count)| {
                        // if a given resolution partner and unifying substitution has appeared more than 1 time,
                        // we will only resolve into a tautology so nip that right now
                        if count == 1 {
                            Some( (other_id, sub) )
                        } else {
                            None
                        }
                    })
            })
        {
            // the size of the resolvant is the total number of terms minus the one being filtered out
            let estimate = self.clauses.get_index(other_id.0).expect("clause id for non-existent clause").num_terms() + clause.num_terms() - 1;
            let action = Action::Resolve{
                estimate,
                ids: (clause_id, other_id),
                sub
            };
            self.action_queue.push(action);
        }

        for (sub, _) in factorizations.into_iter() {
            let estimate = clause.num_terms() - 1;
            let action = Action::Factor {
                estimate,
                clause_id,
                sub,
            };
            self.action_queue.push(action);
        }

        Ok(clause_id)
    }
    pub fn get(&self, id: ClauseId) -> &Clause {
        self.clauses.get_index(id.0).expect("an invalid ClauseId was created")
    }
    pub fn has_contradiction(&mut self) -> Result<bool, BoxedErrorTrait> {
        if self.is_inconsistent {
            // we can return early in this case
            return Ok(true);
        }
        // every clause strictly before the cutoff has been completely resolved
        loop {
            let maybe_clause = match self.action_queue.pop() {
                None => return Ok(false), // no further actions to take means empty clause is not in here

                Some(Action::Resolve{ estimate: _, ids: (left_id, right_id), sub }) => {
                    let left = self.clauses.get_index(left_id.0).expect("clause id for non existent clause");
                    let right = self.clauses.get_index(right_id.0).expect("clause id for non existent clause");
                    left.resolve_under_substitution(&right, &sub)
                }

                Some(Action::Factor{ estimate: _, clause_id, sub }) => {
                    let clause = self.clauses.get_index(clause_id.0).expect("clause id for non existent clause");
                    clause.factor_under_substitution(&sub)
                }
            };
            let clause = match maybe_clause {
                Some(clause) => clause,
                None => continue,
            };
            self.integrate_clause(clause)?;
            if self.is_inconsistent {
                // the clause was the empty clause
                return Ok(true);
            }

            // println!("current set: {:#?}", self);
        }
    }
}

/// The type of the distance heuristic
type EstimateType = u32;

/// Represents a branch from the current state of a ClosedClauseSet in the search space
#[derive(Debug, Clone)]
enum Action {
    /// Resolving two clauses by unifying two opposing terms
    Resolve{
        estimate: EstimateType,
        ids: (ClauseId, ClauseId),
        sub: Substitution,
    },
    Factor{
        estimate: EstimateType,
        clause_id: ClauseId,
        sub: Substitution,
    },
}
impl Action {
    /// Provide a heuristic of how close this action is to deriving the empty clause
    fn estimate(&self) -> EstimateType {
        match self {
            Action::Resolve{estimate, ..} => *estimate,
            Action::Factor{estimate, ..} => *estimate,
        }
    }
}
/// `Action`s are ordered by the estimate we provide them,
/// we want the "greatest" action (i.e., the one prioritized by the binary heap) to be the one with the smallest estimate
impl Eq for Action { }
impl PartialEq for Action {
    fn eq(&self, other: &Self) -> bool {
        other.estimate() == self.estimate()
    }
}
impl Ord for Action {
    fn cmp(&self, other: &Self) -> Ordering {
        other.estimate().cmp(&self.estimate())
    }
}
impl PartialOrd for Action {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        other.estimate().partial_cmp(&self.estimate())
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

fn update_or_insert<K, V, F>(this: &mut Vec<(K, V)>, key: K, default: V, updator: F)
    where F: Fn(&mut V),
          K: Eq
{
    for (key_in_vec, value) in this.iter_mut() {
        if *key_in_vec == key {
            updator(value);
            return;
        }
    }
    this.push((key, default));
}

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Clause {}", self.0)
    }
}
