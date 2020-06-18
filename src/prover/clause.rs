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
    /// set to true if the clause always becomes a tautology,
    /// i.e. both `p` and `~p` are present
    is_tautology: bool,
}

// TODO streamline clauses
// - bugs if both p and ~p are present in the clause (see king/ace test)
// - the clause is necessarily true, but we shouldn't cancel it immediately

impl Clause {
    /// Creates the empty clause
    pub fn empty() -> Clause {
        Clause { terms: BTreeMap::new(), is_tautology: false }
    }
    /// Set a variable name to a specific truth-value, returning `self`
    #[allow(dead_code)]
    pub fn set(mut self, var_name: String, truth_value: bool) -> Clause {
        self.insert(var_name, truth_value);
        self
    }
    /// Inserts a specific variable name with its truth-value,
    /// returns `true` if a tautology is created
    pub fn insert(&mut self, var_name: String, truth_value: bool) {
        if self.is_tautology { return; }
        match self.terms.entry(var_name) {
            Entry::Vacant(entry) => {
                entry.insert(truth_value);
            },
            Entry::Occupied(entry) => {
                if *entry.get() != truth_value {
                    self.is_tautology = true;
                    return;
                }
            },
        }
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
    #[allow(dead_code)]
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
        Some(Clause { terms: resolvant_terms, is_tautology: false })
    }
    /// Returns true if this is the empty clause, i.e falso
    #[allow(dead_code)]
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
    #[allow(dead_code)]
    pub fn new() -> ClauseInterner {
        ClauseInterner { clauses: IndexSet::new() }
    }
    pub fn intern_clause(&mut self, clause: Clause) -> ClauseId {
        let (idx, _) = self.clauses.insert_full(clause);
        ClauseId(idx)
    }
    #[allow(dead_code)]
    pub fn get(&self, id: ClauseId) -> &Clause {
        self.clauses.get_index(id.0).expect("an invalid ClauseId was created")
    }
    pub fn intern_and_insert(&mut self, clause_set: &mut IndexSet<ClauseId>, clause: Clause) {
        if clause.is_tautology { return; }
        clause_set.insert(self.intern_clause(clause));
    }
}
