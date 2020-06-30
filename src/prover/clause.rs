use std::collections::btree_map::Entry;
use indexmap::set::IndexSet;
use std::fmt::Formatter;
use std::fmt;
use std::collections::BTreeMap;
use itertools::Itertools;
use std::cmp::Ordering;

use crate::ast::{LiteralExpr, Substitution};
use crate::prover::TermMap;

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
    terms: Vec<(LiteralExpr<'a>, bool)>,
}

pub struct ClauseBuilder<'a> {
    terms: BTreeMap<LiteralExpr<'a>, bool>,
    is_tautology: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// id's used to reference interned clauses
pub struct ClauseId(pub usize);

#[derive(Debug)]
/// interns clauses, and provides lookup by variable and truth value
pub struct ClosedClauseSet<'a> {
    /// the set of all clauses we have encountered thus far
    pub clauses: IndexSet<Clause<'a>>,
    /// maps `(variable_name, truth_value)` to vectors of clauses,
    /// which contain that `variable_name` with that `truth_value`
    term_map_true: TermMap<'a>,
    term_map_false: TermMap<'a>,
}

impl <'a> ClauseBuilder<'a> {
    /// Creates the empty clause
    pub fn new() -> ClauseBuilder<'a> {
        ClauseBuilder {
            terms: BTreeMap::new(),
            is_tautology: false
        }
    }
    /// Set a variable name to a specific truth-value, returning `self`, used in macros
    #[allow(dead_code)]
    pub fn set(mut self, var_name: &'a str, truth_value: bool) -> ClauseBuilder {
        self.insert(LiteralExpr::atom(var_name), truth_value);
        self
    }
    pub fn set_lit(mut self, literal: LiteralExpr<'a>, truth_value: bool) -> ClauseBuilder {
        self.insert(literal, truth_value);
        self
    }
    /// Inserts a specific variable name with its truth-value,
    /// returns `true` if a tautology is created
    pub fn insert(&mut self, literal: LiteralExpr<'a>, truth_value: bool) {
        if self.is_tautology { return; }
        match self.terms.entry(literal) {
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
    pub fn resolve(&self, other: &Clause<'a>) -> Option<Clause<'a>> {
        let sub = Substitution::new();
        self.resolve_under_substitution(other, &sub)
    }
    /// apply the resolution rule to two clauses, which are guaranteed to have EXACTLY one conflict,
    /// upto the substitution `sub` which is passed to it, and applied to every term before resolving
    /// For example, suppose we have
    ///    `{~P($x), Q($x)}` (P($x) is false OR Q($x) is true)
    ///    `{P(a)}`          (P(a) is true)
    /// And we resolve under the substitution {$x => a}, we get:
    ///    `{~P(a), Q(a)}`
    ///    `{P(a)}`
    /// And resolution proceeds as normal, giving us:
    ///    `{Q(a)}`
    pub fn resolve_under_substitution(&self, other: &Clause<'a>, sub: &Substitution<'a>) -> Option<Clause<'a>> {
        // we know at least one term will conflict, otherwise the new clause could have everything in both
        let capacity = self.terms.len() + other.terms.len() - 1;
        let mut resolvant_terms = Vec::with_capacity(capacity);
        let mut left_iter = self.terms
            .iter()
            .map(|(term, truth)| {
                (term.substitute(sub), *truth)
            })
            .peekable();
        let mut right_iter = other.terms
            .iter()
            .map(|(term, truth)| {
                (term.substitute(sub), *truth)
            })
            .peekable();
        let mut canceled = false;
        loop {
            match (left_iter.peek(), right_iter.peek()) {
                // there are two sides
                ( Some((lname, ltruth)), Some((rname, rtruth)) ) => match lname.cmp(rname) {
                    Ordering::Less => {
                        // process the left side
                        resolvant_terms.push( (lname.clone(), *ltruth));
                        left_iter.next();
                    },
                    Ordering::Greater => {
                        // process the right side
                        resolvant_terms.push( (rname.clone(), *rtruth));
                        right_iter.next();
                    },
                    Ordering::Equal => {
                        // present the same variable, process both
                        if ltruth == rtruth {
                            // terms are the same, it's just a redundancy
                            resolvant_terms.push( (lname.clone(), *rtruth));
                        } else {
                            // these are the conflicting terms, and we do not include them
                            if canceled {
                                return None; // we've already canceled terms: just return `None` right now
                            }
                            canceled = true;
                        }
                        left_iter.next(); right_iter.next();
                    },
                },
                // there is only the left to process
                ( Some((name, truth)), None ) => {
                    resolvant_terms.push((name.clone(), *truth));
                    left_iter.next();
                }
                // there is only the right to process
                ( None, Some((name, truth)) ) => {
                    resolvant_terms.push((name.clone(), *truth));
                    right_iter.next();
                }
                (None, None) => { break; }
            }
        }
        Some( Clause { terms: resolvant_terms } )
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
            term_map_true: TermMap::new(),
            term_map_false: TermMap::new(),
        }
    }
    /// get all clauses who have have conflicts with `clause` under some unififer
    pub fn possible_resolution_partners<'s>(&self, clause: &Clause<'a>) -> Vec<(ClauseId, Substitution<'a>)>
        where 'a: 's
    {
        // count the number of times we visit each clause id
        let mut result = Vec::new();
        // iterate over the terms in `clause`
        for (term, truth_value) in clause.terms.iter() {
            // increment the count of each clause with the same name, but opposite truth_value
            // get the terms for the *opposite* truth value
            let term_map = if !*truth_value { &self.term_map_true } else { &self.term_map_false };
            for (uses, sub) in term_map.unifies_with(term).into_iter() {
                for clause_id in uses {
                    let entry = (*clause_id, sub.clone());
                    result.push(entry);
                }
            }
        }
        result
    }
    /// Returns a vector of all clauses we can get by applying unifying terms inside the clause
    /// For instance:
    ///    `{P($x), P($y), Q($x, $y)}` may be factored to:
    ///     `{P($x), Q($x, $x)}` via `$y -> $x`
    ///     `{P($y), Q($y, $y)}` via `$x -> $y`
    pub fn factors(&self, clause: &Clause<'a>) -> Vec<Clause<'a>> {
        // test pairwise for possible unifiers
        let mut subs = Vec::new();
        for (x, x_truth) in clause.terms.iter() {
            for (y, y_truth) in clause.terms.iter() {
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
                for (term, truth_value) in clause.terms.iter() {
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
    pub fn integrate_clause(&mut self, clause: Clause<'a>) -> ClauseId {
        let (idx, _) = self.clauses.insert_full(clause);
        let clause_id = ClauseId(idx);
        let clause: &Clause = self.clauses.get_index(idx).expect("missing clause");
        for (literal, truth_value) in clause.terms.iter() {
            // lookup the literal, and insert a new reference
            let term_map = if *truth_value { &mut self.term_map_true } else { &mut self.term_map_false };
            term_map.update(literal, clause_id);
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
                write!(f, "{:?}", term)?;
            } else {
                write!(f, "~{:?}", term)?;
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
