#[macro_use]
mod prover;
mod ast;

#[cfg(test)]
mod tests {
    use indexmap::set::IndexSet;
    use crate::prover::{Clause, ClauseInterner, is_satisfiable};

    #[test]
    fn clause_builder_0() {
        let clause = Clause::empty()
            .set("p", true)
            .set("q", false)
            .set("r", false)
            .set("s", true);
        assert_eq!(clause!(p, ~q, ~r, s), clause);
    }
    #[test]
    fn clause_builder_1() {
        let clause = Clause::empty()
            .set("p", false)
            .set("q", true)
            .set("r", false)
            .set("s", true)
            .set("t", false);
        assert_eq!(clause!(~p, q, ~r, s, ~t), clause);
    }
    #[test]
    fn clause_builder_2() {
        assert_eq!(clause!(), Clause::empty());
    }

    #[test]
    fn resolution_simple_0() {
        let a = clause!(p, q);
        let b = clause!(~q, r);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(p, r)));
    }
    #[test]
    fn resolution_simple_1() {
        let a = clause!(~p, q); // equivalent to p -> q
        let b = clause!(p);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(q)));
    }
    #[test]
    fn resolution_simple_2() {
        let a = clause!(p);
        let b = clause!(~p);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!()));
    }
    #[test]
    fn resolution_simple_3() {
        let a = clause!(~m, p, q);
        let b = clause!(~p, q);
        assert_eq!(Clause::resolve(&a, &b), Some(clause!(~m, q)));
    }
    #[test]
    fn resolution_tautology_0() {
        let a = clause!(p, q);
        let b = clause!(~p, ~q);
        assert_eq!(Clause::resolve(&a, &b), None);
    }
    #[test]
    fn resolution_tautology_1() {
        let a = clause!(s, r, t, p, q);
        let b = clause!(~p, ~q);
        assert_eq!(Clause::resolve(&a, &b), None);
    }
    #[test]
    fn resolution_tautology_2() {
        let a = clause!(~s, ~r, p, q);
        let b = clause!(~p, ~q, s, r);
        assert_eq!(Clause::resolve(&a, &b), None);
    }

    #[test]
    fn clause_intern_0() {
        let mut interner = ClauseInterner::new();

        let a = clause!(p, ~q, r).intern(&mut interner);
        let b = clause!(p, ~q, r).intern(&mut interner);
        assert_eq!(a, b);
    }

    #[test]
    fn satisfy_simple_0() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!()); // contradiction immediately

        assert_eq!(is_satisfiable(clauses, &mut interner), false); // make sure we recognize the falso in the premise
    }
    #[test]
    fn satisfy_simple_1() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p));
        interner.intern_and_insert(&mut clauses, clause!(~p));

        assert_eq!(is_satisfiable(clauses, &mut interner), false); // both p and ~p is a contradiction
    }
    #[test]
    fn satisfy_simple_2() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p, q)); // p or q
        interner.intern_and_insert(&mut clauses, clause!(~p));   // not p, so q is true
        interner.intern_and_insert(&mut clauses, clause!(~q));   // q is not true

        assert_eq!(is_satisfiable(clauses, &mut interner), false); // both q and ~q is a contradiction
    }
    #[test]
    fn satisfy_simple_3() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(~p, q)); // p => q
        interner.intern_and_insert(&mut clauses, clause!(p));     // p is true
        interner.intern_and_insert(&mut clauses, clause!(q));     // q is true

        assert_eq!(is_satisfiable(clauses, &mut interner), true);         // there is no contradiction
    }
    #[test]
    fn satisfy_simple_4() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(~p, q));  // p => q
        interner.intern_and_insert(&mut clauses, clause!(~q, r));  // q => r
        interner.intern_and_insert(&mut clauses, clause!(p));      // p is true
        interner.intern_and_insert(&mut clauses, clause!(~r));     // r is false

        assert_eq!(is_satisfiable(clauses, &mut interner), false);        // there is a contradiction, because we can derive r
    }
    #[test]
    fn satisfy_simple_5() {
        let mut clauses = IndexSet::new();
        let mut interner = ClauseInterner::new();

        interner.intern_and_insert(&mut clauses, clause!(p, q));   // p or q
        interner.intern_and_insert(&mut clauses, clause!(~p, r));  // not p or q
        interner.intern_and_insert(&mut clauses, clause!(~p, ~r)); // not p or not r
        interner.intern_and_insert(&mut clauses, clause!(p, ~q));  // p or not q

        assert_eq!(is_satisfiable(clauses, &mut interner), false);        // there is a contradiction
    }


}