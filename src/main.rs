
#[macro_use]
mod clause;
mod prover;

use crate::clause::Clause;
use crate::clause::ClauseInterner;
use crate::prover::is_satisfiable;
use indexmap::set::IndexSet;

fn main() {
    let mut clauses = IndexSet::new();
    let mut interner = ClauseInterner::new();

    // interner.intern_and_insert(&mut clauses, clause!(~p, q)); // p => q
    interner.intern_and_insert(&mut clauses, clause!(p, q));  // p is true
    interner.intern_and_insert(&mut clauses, clause!(~p)); // p is false
    interner.intern_and_insert(&mut clauses, clause!(~q)); // p is false

    assert_eq!(is_satisfiable(clauses, &mut interner), false);
}
