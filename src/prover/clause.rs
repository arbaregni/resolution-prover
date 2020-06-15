use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use indexmap::set::IndexSet;
use std::fmt::Formatter;
use std::fmt;

/// A recursive macro that constructs a clause from terms
#[macro_export]
macro_rules! clause {
    // the base case: the empty clause
    () => {
        crate::prover::Clause::empty()
    };
    ($term:ident) => {
        $crate::prover::Clause::empty().set( stringify!($term).to_string() , true)
    };
    ( ~ $term:ident) => {
        crate::prover::Clause::empty().set( stringify!($term).to_string() , false)
    };
    // the recursive, truthy case
    ( $term:ident, $($tail:tt)*) => {
        clause!( $($tail)+ ).set( stringify!($term).to_string() , true)
    };
    // the recursive, falsy case
    ( ~ $term:ident, $($tail:tt)*) => {
        clause!( $($tail)* ).set( stringify!($term).to_string() , false);
    };
}

/// Any number of terms, at least one of which is true
/// (the empty clause, of course, represents paradox)
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    /// maps a variable's name to it's truth value
    /// i.e, the clause `{p, ~q}` is represented by `{"p": true, "q": false}`
    terms: BTreeMap<String, bool>,
}

impl Clause {
    /// Creates the empty clause
    pub fn empty() -> Clause {
        Clause { terms: BTreeMap::new() }
    }
    /// Set a variable name to a specific truth-value, returning `self`
    pub fn set(mut self, var_name: String, truth_value: bool) -> Clause {
        self.insert(var_name, truth_value);
        self
    }
    /// Inserts a specific variable name with its truth-value
    pub fn insert(&mut self, var_name: String, truth_value: bool) {
        self.terms.insert(var_name, truth_value);
    }
    /// apply the resolution rule to two clauses
    /// the new clause contains all non-complementary terms
    /// For example, suppose we have
    ///     `{p, q}` (p is true OR q is true)
    ///    `{~q, r}` (q is false OR r is true)
    /// Then, it must be the case that p is true, OR r is true,
    ///       and we don't know anything about q. This gives us:
    ///     `{p, r}` (p is true OR r is true)
    ///
    /// Returns `None` if there are resolution conflicts.
    /// In this case, resolving two closes only creates tautologies
    /// For example, suppose we have
    ///     `{p, q, r, ...}`
    ///     `{~p, ~q, s, ...}`
    ///     ------------------
    ///      `{q, ~q, r, s, ....}` which is true regardless of `q`'s truth value
    ///      `{p, ~p, r, s, ....}`
    pub fn resolve(&self, other: &Clause) -> Option<Clause> {
        let mut canceled_terms = false; // set to true if we have canceled terms
        let mut resolvant_terms = BTreeMap::new();
        let iter = self.terms.iter()
            .chain(other.terms.iter());
        for (name, &truth_value) in iter {
            let key = name.to_string();
            match resolvant_terms.entry(key) {
                Entry::Vacant(entry) => {
                    entry.insert(truth_value);
                },
                Entry::Occupied(entry) => {
                    if *entry.get() != truth_value {
                        // we have a paradox: neither term is necessarily a possibility,
                        // so we don't include it in the new clause
                        if canceled_terms {
                            // we include both the variable and it's negation
                            // BUT that's a tautology, so we return None
                            return None;
                        }
                        entry.remove();
                        canceled_terms = true;
                    }
                }
            }
        }
        Some(Clause { terms: resolvant_terms })
    }
    /// Intern this object in the interner, returning our clause id
    pub fn intern(self, interner: &mut ClauseInterner) -> ClauseId {
        interner.intern_clause(self)
    }
    /// Returns true if this is the empty clause, i.e falso
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (term, &truth_value) in self.terms.iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            if truth_value {
                write!(f, "{}", term)?;
            } else {
                write!(f, "~{}", term)?;
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ClauseId(usize);

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Clause {}", self.0)
    }
}
#[derive(Debug)]
pub struct ClauseInterner {
    clauses: IndexSet<Clause>,
}

impl ClauseInterner {
    pub fn new() -> ClauseInterner {
        ClauseInterner { clauses: IndexSet::new() }
    }
    pub fn intern_clause(&mut self, clause: Clause) -> ClauseId {
        let (idx, _) = self.clauses.insert_full(clause);
        ClauseId(idx)
    }
    pub fn get(&self, id: ClauseId) -> &Clause {
        self.clauses.get_index(id.0).expect("an invalid ClauseId was created")
    }
    pub fn intern_and_insert(&mut self, clause_set: &mut IndexSet<ClauseId>, clause: Clause) {
        clause_set.insert(self.intern_clause(clause));
    }
}
