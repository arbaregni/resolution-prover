use std::collections::btree_map::Entry;
use std::fmt::Formatter;
use std::fmt;
use std::collections::{BTreeMap};
use itertools::Itertools;
use std::cmp::Ordering;

use crate::ast::{Term, Substitution, compose, SymbolTable};

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
    /// Returns true iff `self` subsumes by `other`
    /// That is, there is a substitution σ such that σ(`self`) is a subset of `other`.
    /// This is _not_ strict subsumption, where every literally in `other` would be matched
    pub fn subsumes(&self, other: &Clause) -> bool {
        fn match_terms(terms: &[(Term, bool)], other: &Clause, sub: Substitution) -> bool {
            let ((term, truth_value), rest) = match terms.split_first() {
                Some(thing) => thing,
                None => {
                    println!("subsuming with σ = {:?}", sub);
                    return true; // made it to the end
                },
            };
            let term = term.substitute(&sub);
            // try to match `term` with every possible term in `other` with the corresponding truth value
            let iter = other.iter()
                .filter(|(_, tv)| tv == truth_value)
                .map(|(t, _)| t);
            for other_term in iter {
                let new = match term.left_unify(other_term) {
                    Some(new) => {
                        compose(sub.clone(), new)
                    },
                    None => continue,
                };
                if match_terms(rest, other, new) {
                    return true; // we have a success!
                }
            }
            false // none of the recursive calls were successful
        }
        match_terms(&self.terms, other, Substitution::new())
    }
    /// Returns true if this is the empty clause, i.e falso
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
    /// Returns true if this clause contains the term with that truth value
    pub fn contains(&self, term: &Term, truth_value: bool) -> bool {
        for (contained_term, contained_truth_value) in self.terms.iter() {
            if contained_term == term && *contained_truth_value == truth_value { return true; }
        }
        false
    }
    /// Iterates over underlying vector
    pub fn iter(&self) -> impl Iterator<Item = &(Term, bool)> {
        self.terms.iter()
    }
    /// Iterates over positive terms
    pub fn iter_pos(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
            .filter(|(_, truth_value)| *truth_value) // keep if truth_value is TRUE
            .map(|(t, _)| t)
    }
    /// Iterates over negative terms
    pub fn iter_neg(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
            .filter(|(_, truth_value)| !*truth_value) // keep if truth_value is FALSE
            .map(|(t, _)| t)
    }
    /// Return a string of the clause with original names restored
    pub fn demangled(&self, symbols: &SymbolTable) -> String {
        let mut s = String::new();
        s.push('{');
        let mut first = true;
        for (term, truth_value) in self.terms.iter() {
            if !first {
                s.push_str(", ");
            }
            first = false;
            if *truth_value {
                // positive term = no tilde
            } else {
                // negated term = tilde
                s.push('~');
            }
            s.push_str(&term.demangled(symbols));
        }
        s.push('}');
        s
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

#[cfg(test)]
mod subsumption_tests {
    use crate::ast::{SymbolTable, Term};
    use crate::prover::ClauseBuilder;

    #[test]
    fn it_works_0() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let q = symbols.make_fun();
        let a = symbols.make_fun();
        let x = symbols.make_var();

        // { P($x), Q($x) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x)]), true)
            .set(Term::predicate(q, vec![Term::variable(x)]), true)
            .finish().unwrap();

        // { P(a), Q(a) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::atom(a)]), true)
            .set(Term::predicate(q, vec![Term::atom(a)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), true); // by σ = {$x: a}
    }
    #[test]
    fn it_works_1() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let a = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();

        // { P($x, a), P($y, $x) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::atom(a)]), true)
            .set(Term::predicate(p, vec![Term::variable(y), Term::variable(x)]), true)
            .finish().unwrap();

        // { P(a, a) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::atom(a), Term::atom(a)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), true); // by σ = {$x: a, $y: a}
    }
    #[test]
    fn different_truth_value() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();

        // { P($x) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x)]), true)
            .finish().unwrap();

        // { ~P($y) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(y)]), false)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), false); // not subsumed
    }
    #[test]
    fn restrictive_variables() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let z = symbols.make_var();

        // { P($x, $x) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::variable(x)]), true)
            .finish().unwrap();

        // { P($y, $z) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(y), Term::variable(z)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), false); // not subsumed
    }
    #[test]
    fn different_functions() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let q = symbols.make_fun();
        let a = symbols.make_fun();
        let b = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();

        // { P($x, a), Q($x, $y) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::atom(a)]), true)
            .set(Term::predicate(q, vec![Term::variable(x), Term::variable(y)]), true)
            .finish().unwrap();

        // { P(b, b), P(b, a) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::atom(b), Term::atom(b)]), true)
            .set(Term::predicate(p, vec![Term::atom(b), Term::atom(a)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), false); // not subsumed
    }
    #[test]
    fn it_works_2() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let a = symbols.make_fun();
        let b = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let z = symbols.make_var();

        // { P($x, $x), P($x, $y), P($y, $z) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::variable(x)]), true)
            .set(Term::predicate(p, vec![Term::variable(x), Term::variable(y)]), true)
            .set(Term::predicate(p, vec![Term::variable(y), Term::variable(z)]), true)
            .finish().unwrap();

        // { P(a, a), P(b, b) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::atom(a), Term::atom(a)]), true)
            .set(Term::predicate(p, vec![Term::atom(b), Term::atom(b)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), true); // subsumed by {$x: a, $y: a, $z: a}  (not strict)
    }
    #[test]
    fn not_unifiable() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let f = symbols.make_fun();
        let g = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let u = symbols.make_var();

        // { P(f($x), $y) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::predicate(f,
                                                                            vec![Term::variable(y)]
            )]), true)
            .finish().unwrap();

        // { P($u, g($u)) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(u), Term::predicate(g,
                                                                            vec![Term::variable(u)]
            )]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), false); // not subsumed
    }
    #[test]
    fn not_subset() {
        let mut symbols = SymbolTable::new();
        let p = symbols.make_fun();
        let a = symbols.make_fun();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let z = symbols.make_var();

        // { P($x, $x), P($y, $x) }
        let first = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(x), Term::variable(x)]), true)
            .set(Term::predicate(p, vec![Term::variable(y), Term::variable(x)]), true)
            .finish().unwrap();

        // { P($z, a) }
        let second = ClauseBuilder::new()
            .set(Term::predicate(p, vec![Term::variable(z), Term::atom(a)]), true)
            .finish().unwrap();

        assert_eq!(first.subsumes(&second), false); // not subsumed
    }

}