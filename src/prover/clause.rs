use std::collections::btree_map::Entry;
use std::fmt::Formatter;
use std::fmt;
use std::collections::{BTreeMap};
use itertools::Itertools;
use std::cmp::Ordering;

use crate::ast::{Term, Substitution};

/// A recursive macro that builds a clause from terms
#[allow(unused_macros)]
macro_rules! clause_builder {
    // the base case: the empty clause
    () => {
        crate::prover::ClauseBuilder::new()
    };
    ($term:ident) => {
        $crate::prover::ClauseBuilder::new().set( Term::atom($term), true )
    };
    ( ~ $term:ident) => {
        crate::prover::ClauseBuilder::new().set( Term::atom($term), false )
    };
    // the recursive, truthy case
    ( $term:ident, $($tail:tt)*) => {
        clause_builder!( $($tail)+ ).set( Term::atom($term), true )
    };
    // the recursive, falsy case
    ( ~ $term:ident, $($tail:tt)*) => {
        clause_builder!( $($tail)* ).set( Term::atom($term), false )
    };
}
/// Creates and finishes a clause builder on the given terms
#[macro_export]
macro_rules! clause {
    ( $($term:tt)* ) => {
        clause_builder!( $($term)* ).finish().expect("hard_coded tautology")
    }
}

/// Any number of terms, at least one of which is true
/// (the empty clause, of course, represents paradox)
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    /// sorted vector of `(variable_name, truth_value)`, no duplicate variable names
    terms: Vec<(Term, bool)>,
}

pub struct ClauseBuilder {
    terms: BTreeMap<Term, bool>,
    is_tautology: bool,
}

impl ClauseBuilder {
    /// Creates the empty clause
    pub fn new() -> ClauseBuilder {
        ClauseBuilder {
            terms: BTreeMap::new(),
            is_tautology: false
        }
    }
    #[allow(dead_code)]
    pub fn set(mut self, term: Term, truth_value: bool) -> ClauseBuilder {
        self.insert(term, truth_value);
        self
    }
    /// Inserts a specific variable name with its truth_value,
    /// returns `true` if a tautology is created
    pub fn insert(&mut self, term: Term, truth_value: bool) {
        if self.is_tautology { return; }
        match self.terms.entry(term) {
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
    pub fn finish(self) -> Option<Clause> {
        if self.is_tautology { return None; }
        let terms = self.terms
            .into_iter()
            .collect_vec();
        Some(Clause { terms })
    }
}
impl Clause {
    /// apply the resolution rule to two clauses, which are guaranteed to have EXACTLY one conflict
    /// the new clause contains all non_complementary terms
    /// For example, suppose we have
    ///     `{p, q}` (p is true OR q is true)
    ///    `{~q, r}` (q is false OR r is true)
    /// Then, it must be the case that p is true, OR r is true,
    ///       and we don't know anything about q. This gives us:
    ///     `{p, r}` (p is true OR r is true)
    #[allow(dead_code)]
    pub fn resolve(&self, other: &Clause) -> Option<Clause> {
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
    pub fn resolve_under_substitution(&self, other: &Clause, sub: &Substitution) -> Option<Clause> {
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
    /// Apply a substitution and merge all of the identical terms,
    /// possibly returning `None` if a tautology is created
    pub fn factor_under_substitution(&self, sub: &Substitution) -> Option<Clause> {
        let mut builder = ClauseBuilder::new();
        for (term, truth_value) in self.iter() {
            let mapped = term.substitute(sub);
            builder.insert(mapped, *truth_value);
        }
        builder.finish()
    }
    /// Returns true if this is the empty clause, i.e falso
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
    /// Iterates over underlying vector
    pub fn iter(&self) -> impl Iterator<Item = &(Term, bool)> {
        self.terms.iter()
    }
    /// Estimate the benefit to searching for resolution partners of this clause
    pub fn num_terms(&self) -> u32 {
        self.terms.len() as u32
    }
    pub fn contains(&self, term: &Term, truth_value: bool) -> bool {
        for (contained_term, contained_truth_value) in self.terms.iter() {
            if contained_term == term && *contained_truth_value == truth_value {
                return true;
            }
        }
        false
    }
}


impl fmt::Debug for Clause {
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

