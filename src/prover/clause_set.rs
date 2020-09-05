use crate::prover::{Clause, TermTree, ClauseBuilder};
use indexmap::set::IndexSet;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::ast::{Term, Substitution};
use crate::error::BoxedErrorTrait;
use crate::prover::feature_index::SubsumptionTree;
use std::rc::Rc;

// current AGE:WEIGHT ratio:
// for every 5 clauses, 2 will be selected due to their age, and 3 will be selected due to their weight
const SELECTED_BY_AGE: u32 = 2;
const SELECTED_BY_WEIGHT: u32 = 3;

#[derive(Debug)]
/// interns clauses, and provides lookup by variable and truth value
pub struct KeptClauseSet {
    /// the set of all clauses we have processed thus far
    pub clauses:  HashSet<Rc<Clause>>,

    /// retrieve terms that could be unifiable
    pub term_tree: TermTree,

    /// maps terms to their positive/negative occurrences in clauses
    occurrences: HashMap<Term, Occurrences>,

    inferences: VecDeque<Inference>,
}

impl KeptClauseSet {
    pub fn new() -> KeptClauseSet {
        KeptClauseSet {
            clauses: HashSet::new(),
            term_tree: TermTree::new(),
            occurrences: HashMap::new(),
            inferences: VecDeque::new(),
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
    /// Inserts the clause, updating the record-keeping data structures
    pub fn integrate_clause(&mut self, clause: Rc<Clause>) -> Result<(), BoxedErrorTrait> {
        println!("integrating clause: {:?}", clause);

        let made_insertion = self.clauses.insert(Rc::clone(&clause));
        if !made_insertion {
            return Ok(()); // the clause was already present so there is no need to do further processing
        }
        for (term, truth_value) in clause.iter() {
            // lookup the literal, and insert a new reference
            self.term_tree.update(term.clone());
            self.occurrences
                .entry(term.clone())
                .or_insert(Occurrences::new())
                .insert(*truth_value, Rc::clone(&clause))
        }
        // search for inferences by testing each term in the query clause in turn
        println!("term_tree: {:#?}", self.term_tree);

        let mut partners = HashMap::new(); // maps clauses -> pairs of unifiers & a count of the number of terms that lead us to include that clause and unifier
        let mut factors = Vec::new(); // substitutions that could factor the query clause

        for (query_term, truth_value) in clause.iter() {
            for term in self.term_tree.unification_candidates(query_term.clone())? {
                println!("  query term: {:?} unifies with {:?}", query_term, term);
                let occr = self.occurrences.get(&term).expect("missing occurrences for term");
                // each clause with the same term (up to unification) but opposite truth value is a potential partner
                for partner_clause in occr.get(!*truth_value) {
                    if *partner_clause == clause { continue; }
                    println!("  possible partner: {:?}", partner_clause);
                    let sub = match query_term.unify(&term) {
                        Some(sub) => sub,
                        None => continue,
                    };
                    let hits = partners.entry(partner_clause).or_insert(Vec::with_capacity(1));
                    // find our subsitution (if it already exists) and increment the count, or create it with a count of one
                    let count = get_mut_or_insert(hits, sub, 0);
                    *count += 1;
                }
                // if the term matched another term in the same clause, we could have a factor
                if term != *query_term && clause.contains(&term, *truth_value) {
                    if let Some(sub) = query_term.unify(&term) {
                        // insert the sub unless it already exists
                        let _ = get_mut_or_insert(&mut factors, sub, ());
                    }
                }
            }
        }
        let query_clause = &clause;
        println!("  resolution partners: {:?}", partners);
        let resolutions = partners.into_iter()
            .flat_map(|(partner_clause, hits)| {
                hits.into_iter()
                    .filter_map(|(sub, count)| {
                        if count == 1 {
                            Some( sub )
                        } else {
                            None
                        }
                    })
                    .map(move |sub| {
                        Inference::Resolution {
                            fst: Rc::clone(query_clause),
                            sec: Rc::clone(partner_clause),
                            sub
                        }
                    })
            });
        println!("  factors: {:?}", factors);
        let factorizations = factors.into_iter()
            .map(|(sub, ())| {
                Inference::Factorization {
                    clause: Rc::clone(query_clause),
                    sub
                }
            });
        self.inferences.extend(resolutions);
        self.inferences.extend(factorizations);
        Ok(())
    }
    /// Make an as-yet unseen before inference between 2 clauses in the set
    pub fn make_inference(&mut self) -> Option<Rc<Clause>> {
       self.inferences.pop_front()
           .and_then(|inference| inference.conclusion().map(Rc::new))
    }
}

#[derive(Debug)]
pub struct UnprocessedClauseSet {
    pub clauses: IndexSet<Rc<Clause>>,
}
impl UnprocessedClauseSet {
    pub fn new() -> UnprocessedClauseSet {
        UnprocessedClauseSet {
            clauses: IndexSet::new(),
        }
    }
    /// Add a new clause to be processed
    pub fn insert(&mut self, clause: Rc<Clause>) {
        self.clauses.insert(clause);
    }
    /// Get the next clause to be processed in accordance with the SELECT_BY_AGE AND SELECT_BY_WEIGHT ratios
    pub fn select_next(&mut self) -> Option<Rc<Clause>> {
        // todo: round robin
        self.clauses.pop()
    }
    pub fn has_contradiction(self) -> Result<bool,BoxedErrorTrait> {
       search_contradiction(self)
    }
}
pub fn search_contradiction(clauses: UnprocessedClauseSet) -> Result<bool, BoxedErrorTrait> {
    let mut kept = KeptClauseSet::new();
    let mut unprocessed = clauses;
    let mut subsumption_tree = SubsumptionTree::new();
    loop {
        while let Some(new) = unprocessed.select_next() {
            println!("processing: {:?}", new);
            if new.is_empty() {
                return Ok(true); // FOUND EMPTY CLAUSE
            }
            // apply deletion rules (subsumption, ...)
            // here, we might be able to discard clauses which are too big. BUT, we would need to flag this somehow
            let is_retained = subsumption_tree.insert(Rc::clone(&new));
            if is_retained {
                kept.integrate_clause(new)?;
                // here we could simplify `new` by clauses in `kept` (forward simplify)
                // if new.is_empty() {
                //    return Ok(true); // FOUND EMPTY CLAUSE
                // }
                // if retained(&new) {
                //    // delete and simplify clauses in `kept` by `new` (backwards simplify)
                //    // move simplified clauses from `kept` to `unprocessed`
                //    kept.insert(new);
                // }
            }
        }
        if let Some(conclusion) = kept.make_inference() {
            unprocessed.insert(conclusion);
        } else {
            // todo: return "unkown" if a non-redundant clause was discarded
            return Ok(false); // NO MORE INFERENCES TO MAKE
        }
    }
}

#[derive(Debug)]
enum Inference {
    Resolution {
        fst: Rc<Clause>,
        sec: Rc<Clause>,
        sub: Substitution,
    },
    Factorization {
        clause: Rc<Clause>,
        sub: Substitution,
    }
}
impl Inference {
    pub fn conclusion(&self) -> Option<Clause> {
        match self {
            Inference::Resolution {fst, sec, sub } => {
                fst.resolve_under_substitution(sec, sub)
            },
            Inference::Factorization { clause, sub } => {
                clause.factor_under_substitution(sub)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Occurrences {
    truthy: Vec<Rc<Clause>>,
    falsy: Vec<Rc<Clause>>,
}

impl Occurrences {
    fn new() -> Occurrences {
        Occurrences {
            truthy: vec![],
            falsy: vec![]
        }
    }
    fn get(&self, truth_value: bool) -> &[Rc<Clause>] {
        if truth_value {
            self.truthy.as_slice()
        } else {
            self.falsy.as_slice()
        }
    }
    fn insert(&mut self, truth_value: bool, clause: Rc<Clause>) {
        let ids = if truth_value {
            &mut self.truthy
        } else {
            &mut self.falsy
        };
        ids.push(clause);
        ids.dedup();
    }
}

fn get_mut_or_insert<K,V>(vec: &mut Vec<(K, V)>, key: K, default: V) -> &mut V
    where K: std::cmp::Eq
{
    // find the index of the key if it exists
    let maybe_idx = vec.iter().position(|(k, _)| *k == key);
    let idx = match maybe_idx {
        Some(idx) => idx,
        None => {
            vec.push((key, default));
            vec.len() - 1
        }
    };
    let (_, v) = &mut vec[idx];
    v
}