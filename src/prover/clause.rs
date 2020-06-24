use std::collections::btree_map::Entry;
use std::collections::{HashMap};
use indexmap::set::IndexSet;
use std::fmt::Formatter;
use std::fmt;
use std::collections::BTreeMap;
use itertools::Itertools;
use std::cmp::Ordering;

/// A recursive macro that builds a clause from terms
#[allow(unused_macros)]
macro_rules! clause_builder {
    // the base case: the empty clause
    () => {
        crate::prover::ClauseBuilder::new()
    };
    ($term:ident) => {
        $crate::prover::ClauseBuilder::new().set( stringify!($term), true)
    };
    ( ~ $term:ident) => {
        crate::prover::ClauseBuilder::new().set( stringify!($term), false)
    };
    // the recursive, truthy case
    ( $term:ident, $($tail:tt)*) => {
        clause_builder!( $($tail)+ ).set( stringify!($term), true)
    };
    // the recursive, falsy case
    ( ~ $term:ident, $($tail:tt)*) => {
        clause_builder!( $($tail)* ).set( stringify!($term), false)
    };
}
/// Creates and finishes a clause builder on the given terms
#[macro_export]
macro_rules! clause {
    ( $($term:tt)* ) => {
        clause_builder!( $($term)* ).finish().expect("hard-coded tautology")
    }
}

/// Any number of terms, at least one of which is true
/// (the empty clause, of course, represents paradox)
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Clause<'a> {
    /// sorted vector of `(variable_name, truth_value)`, no duplicate variable names
    terms: Vec<(&'a str, bool)>,
}

pub struct ClauseBuilder<'a> {
    terms: BTreeMap<&'a str, bool>,
    is_tautology: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// id's used to reference interned clauses
pub struct ClauseId(usize);

#[derive(Debug)]
/// interns clauses, and provides lookup by variable and truth value
pub struct ClosedClauseSet<'a> {
    /// the set of all clauses we have encountered thus far
    pub clauses: IndexSet<Clause<'a>>,
    /// maps `(variable_name, truth_value)` to vectors of clauses,
    /// which contain that `variable_name` with that `truth_value`
    term_map: HashMap<(&'a str, bool), Vec<ClauseId>>
}

impl <'a> ClauseBuilder<'a> {
    /// Creates the empty clause
    pub fn new() -> ClauseBuilder<'a> {
        ClauseBuilder {
            terms: BTreeMap::new(),
            is_tautology: false
        }
    }
    /// Set a variable name to a specific truth-value, returning `self`
    #[allow(dead_code)]
    pub fn set(mut self, var_name: &'a str, truth_value: bool) -> ClauseBuilder {
        self.insert(var_name, truth_value);
        self
    }
    /// Inserts a specific variable name with its truth-value,
    /// returns `true` if a tautology is created
    pub fn insert(&mut self, var_name: &'a str, truth_value: bool) {
        if self.is_tautology { return; }
        match self.terms.entry(var_name) {
            Entry::Vacant(entry) => {
                entry.insert(truth_value);
            },
            Entry::Occupied(entry) => {
                if *entry.get() != truth_value {
                    self.is_tautology = true;
                }
            },
        }
    }
    pub fn finish(self) -> Option<Clause<'a>> {
        if self.is_tautology { return None; }
        let terms = self.terms
            .into_iter()
            .collect_vec();
        Some(Clause { terms })
    }
}
impl <'a> Clause<'a> {
    /// apply the resolution rule to two clauses, which are guaranteed to have EXACTLY one conflict
    /// the new clause contains all non-complementary terms
    /// For example, suppose we have
    ///     `{p, q}` (p is true OR q is true)
    ///    `{~q, r}` (q is false OR r is true)
    /// Then, it must be the case that p is true, OR r is true,
    ///       and we don't know anything about q. This gives us:
    ///     `{p, r}` (p is true OR r is true)
    pub fn resolve(&self, other: &Clause<'a>) -> Clause<'a> {
        // we know at least one term will conflict, otherwise the new clause could have everything in both
        let capacity = self.terms.len() + other.terms.len() - 1;
        let mut resolvant_terms = Vec::with_capacity(capacity);
        let mut left_iter = self.terms.iter().peekable();
        let mut right_iter = other.terms.iter().peekable();
        loop {
            match (left_iter.peek(), right_iter.peek()) {
                // there are two sides
                ( Some((lname, ltruth)), Some((rname, rtruth)) ) => match lname.cmp(rname) {
                    Ordering::Less => {
                        // process the left side
                        left_iter.next();
                        resolvant_terms.push( (*lname, *ltruth));
                    },
                    Ordering::Greater => {
                        // process the right side
                        right_iter.next();
                        resolvant_terms.push( (*rname, *rtruth));
                    },
                    Ordering::Equal => {
                        // present the same variable, process both
                        left_iter.next(); right_iter.next();
                        if ltruth == rtruth {
                            // terms are the same, it's just a redundancy
                            resolvant_terms.push( (*lname, *rtruth));
                        } else {
                            // these are the conflicting terms, and we do not include them
                        }
                    },
                },
                // there is only the left to process
                ( Some((name, truth)), None ) => {
                    left_iter.next();
                    resolvant_terms.push((*name, *truth));
                }
                // there is only the right to process
                ( None, Some((name, truth)) ) => {
                    right_iter.next();
                    resolvant_terms.push((*name, *truth));
                }
                (None, None) => { break; }
            }
        }
        Clause { terms: resolvant_terms }
    }
    /// Returns true if this is the empty clause, i.e falso
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
}

impl <'a> ClosedClauseSet<'a> {
    pub fn new() -> ClosedClauseSet<'a> {
        ClosedClauseSet {
            clauses: IndexSet::new(),
            term_map: HashMap::new(),
        }
    }
    /// get all clauses who have exactly one conflict with `clause`
    pub fn clauses_with_one_conflict<'s>(&self, clause: &Clause<'a>) -> Vec<ClauseId>
        where 'a: 's
    {
        // count the number of times we visit each clause id
        let num_clauses = self.clauses.len();
        let mut counts = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses { counts.push(0); }

        // iterate over the terms in `clause`
        for (name, truth_value) in clause.terms.iter() {
            // increment the count of each clause with the same name, but opposite truth_value
            for clause_id in self.term_map[&(*name, !*truth_value)].iter() {
                counts[clause_id.0] += 1;
            }
        }
        // now, we take only those with exactly `1` count
        counts.iter()
            .enumerate()
            .filter_map(|(idx, count)| {
                if *count == 1 {
                    Some( ClauseId(idx) )
                } else {
                    None
                }
            })
            .collect()

    }
    /// Inserts the clause, providing the index into the set
    pub fn integrate_clause(&mut self, clause: Clause<'a>) -> ClauseId {
        let (idx, _) = self.clauses.insert_full(clause);
        let clause_id = ClauseId(idx);
        let clause: &Clause = self.clauses.get_index(idx).expect("missing clause");
        for (name, truth_value) in clause.terms.iter() {
            // add the name, and truth value to the term map
            let cache = self.term_map
                .entry((*name, *truth_value))
                .or_insert(Vec::with_capacity(1));
            // this clause has that (name, truth_value)
            cache.push(clause_id);
            // since we expect to call this on ever higher indices, it should be sorted
            // thus, this removes all the duplicates
            cache.dedup();
            // make sure the negation also exists
            self.term_map.entry((*name, !*truth_value))
                .or_insert(Vec::new());
        }
        // println!("integrated new clause, clauses: {:#?}", self.clauses);
        clause_id
    }
    pub fn get<'s>(&'s self, id: ClauseId) -> &'s Clause<'a> {
        self.clauses.get_index(id.0).expect("an invalid ClauseId was created")
    }
}


impl fmt::Debug for Clause<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (term, truth_value) in self.terms.iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            if *truth_value {
                write!(f, "{}", term)?;
            } else {
                write!(f, "~{}", term)?;
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Clause {}", self.0)
    }
}
/*
impl fmt::Debug for ClosedClauseSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {

    }
}
 */
