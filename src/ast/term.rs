use crate::ast::{Expr, ExprKind, VarId, FunId};
use TermKind::*;

use std::{fmt, iter, ptr};
use std::collections::HashMap;
use std::rc::Rc;
use std::ops::Deref;
use std::hash::{Hash, Hasher};
use std::cell::RefCell;

/// A literal predicate expression, with no logical connectives
#[derive(PartialOrd, Ord)]
pub struct Term {
    kind: Rc<TermKind>
}
/// The kind of a literal expression (LiteralExpr wraps around this for now)
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TermKind {
    /// Variables are terms that may take on any value. They are produced by universal quantifiers
    Variable(VarId),
    /// Functions are names and arguments. Constants are zero_arity functions
    Function(FunId, Vec<Term>),
}
/// Variable names are mapped to Literal Expressions
pub type Substitution = HashMap<VarId, Term>;

/// The highest level pattern of a term.
///   For instance,
/// `P(f(a, b, ...), g(h(i(...))))` is represented only
/// as a function named `P` with one argument (arity 1).
/// This is to enable unification based lookup
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TermPattern {
    /// Representing any variable
    Variable,
    /// Representing a function with the given name and arity
    Function(FunId),
}

/// Iterates over all expressions and sub_expressions in the given term
#[derive(Debug, Clone)]
pub struct SubTermIterator {
    stack: Vec<Term>,
}
thread_local! {
    static TERM_MAKER: TermMaker = TermMaker::new();
}

impl TermKind {
    fn into_term(self) -> Term {
        TERM_MAKER.with(|term_maker| {
            term_maker.lookup(self)
        })
    }
}

const EMPTY_TERM_SLICE: &'static [Term] = &[];

#[derive(Debug)]
pub struct TermMaker {
    cache: RefCell<HashMap<TermKind, Term>>
}
impl TermMaker {
    pub fn new() -> TermMaker {
        TermMaker {
            cache: RefCell::new(HashMap::new())
        }
    }
    pub fn atom(&self, fun_id: FunId) -> Term {
        self.lookup(Function(fun_id, vec![]))
    }
    pub fn predicate(&self, fun_id: FunId, args: Vec<Term>) -> Term {
        self.lookup(Function(fun_id, args))
    }
    pub fn variable(&self, var_id: VarId) -> Term {
        self.lookup(Variable(var_id))
    }
    fn lookup(&self, term_kind: TermKind) -> Term {
        // lookup term_kind. if it gets mapped to a term (wrapper for a reference counted term kind), great
        if let Some(term) = self.cache.borrow().get(&term_kind) {
            return term.clone()
        }
        let term = Term { kind: Rc::new(term_kind.clone()) };
        self.cache.borrow_mut().insert(term_kind, term.clone());
        term
    }
}

impl Term {
    pub fn atom(fun_id: FunId) -> Term {
        Function(fun_id, vec![]).into_term()
    }
    pub fn predicate(fun_id: FunId, args: Vec<Term>) -> Term {
        Function(fun_id, args).into_term()
    }
    pub fn variable(var_id: VarId) -> Term {
        Variable(var_id).into_term()
    }
    pub fn into<'a>(self) -> Expr<'a> {
        ExprKind::Term(self).into()
    }
    pub fn kind(&self) -> &TermKind {
        &self.kind
    }
    /// Search for the variable name in our structure
    pub fn contains(&self, var: &VarId) -> bool {
        match self.kind.deref() {
            Variable(name) => *name == *var,
            Function(_, args) => args.iter().any(|a| a.contains(var)),
        }
    }
    pub fn pattern(&self) -> TermPattern {
        match self.kind() {
            TermKind::Variable(_) => TermPattern::Variable,
            TermKind::Function(fun_id, _) => TermPattern::Function(*fun_id),
        }
    }
    pub fn children(&self) -> &[Term] {
        match self.kind() {
            TermKind::Variable(_) => EMPTY_TERM_SLICE,
            TermKind::Function(_, args) => args.as_slice(),
        }
    }
    pub fn is_variable(&self) -> bool {
        if let TermKind::Variable(_) = self.kind() {
            true
        } else {
            false
        }
    }
    pub fn is_function(&self) -> bool {
        if let TermKind::Function(_, _) = self.kind() {
            true
        } else {
            false
        }
    }
    /// Perform the given substitution, producing a new literal expression
    pub fn substitute(&self, sub: &Substitution) -> Term {
        match self.kind.deref() {
            Variable(name) => {
                if let Some(lit) = sub.get(name) {
                    lit.clone()
                } else {
                    self.clone()
                }
            }
            Function(f, args) => {
                let mapped = args.iter()
                    .map(|a| a.substitute(sub))
                    .collect::<Vec<_>>();
                Term::predicate(*f, mapped)
            }
        }
    }
    pub fn unify(&self, other: &Term) -> Option<Substitution> {
        match (self.kind.deref(), other.kind.deref()) {
            (Variable(x), Variable(y)) => {
                // substitute one variable for another
                let mut sub = Substitution::new();
                if x != y {
                    sub.insert(*x, Variable(*y).into_term());
                }
                Some(sub)
            }
            (Variable(x), Function(f, args)) | (Function(f, args), Variable(x)) => {
                // check if x occurs in the term
                if args.iter().any(|a| a.contains(x)) {
                    return None; // can not unify due to self reference
                }
                // substitute f(args) for x
                let mut sub = Substitution::new();
                sub.insert(*x, Function(*f, args.clone()).into_term());
                Some(sub)
            }
            (Function(f, args_f), Function(g, args_g)) => {
                if f != g || args_f.len() != args_g.len() {
                    return None; // can not unify if names or arities are different
                }
                let mut sub = Substitution::new();
                for (left, right) in args_f.iter().zip(args_g.iter()) {
                    let left = left.substitute(&sub);
                    let right = right.substitute(&sub);
                    let new = left.unify(&right)?;
                    sub = compose(sub, new);
                }
                Some(sub)
            }
        }
    }
}

impl iter::Iterator for SubTermIterator {
    type Item = Term;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(term) = self.stack.pop() {
            for child in term.children() {
                self.stack.push(child.clone());
            }
            Some(term)
        } else {
            None
        }
    }
    /// We know that there are at least some number of terms waiting to be yielded,
    /// and we don't have an upper bound
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.stack.len(), None)
    }
}

/// if you performed `sub`, and then `new`, the result is `compose(sub, new)`
fn compose(sub: Substitution, new: Substitution) -> Substitution {
    let mut composition = Substitution::new();
    // perform the new substitution in all the existing mappings
    for (k, v) in sub.into_iter() {
        composition.insert(k, v.substitute(&new));
    }
    // then make sure all the new mappings are present
    for (k, v) in new.into_iter() {
        composition.insert(k, v);
    }
    composition
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.deref().fmt(f)
    }
}
impl fmt::Debug for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Variable(name) => write!(f, "{:?}", name)?,
            Function(name, args) => {
                write!(f, "{:?}", name)?;
                if !args.is_empty() {
                    let mut first = true;
                    for arg in args {
                        if first {
                            first = false;
                            write!(f, "(")?;
                        } else {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", arg)?;
                    }
                    write!(f, ")")?;
                }
            }
        }
        Ok(())
    }
}
impl Clone for Term {
    fn clone(&self) -> Self {
        Term { kind: Rc::clone(&self.kind) }
    }
}
// Assumes that all terms have a perfectly shared representation
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.kind, &other.kind)
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr = Rc::as_ptr(&self.kind);
        ptr::hash(ptr, state);
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Substitution, SymbolTable, TermMaker, Term};
    use crate::ast::TermKind::Function;

    #[test]
    fn unify_0() {
        let mut symbols = SymbolTable::new();
        let a = symbols.make_fun();

        let left = Term::atom(a);
        let right = Term::atom(a);
        assert_eq!(left.unify(&right), Some(Substitution::new())); // tautology: a = a by definition
    }
    #[test]
    fn unify_1() {
        let mut symbols = SymbolTable::new();
        let a = symbols.make_fun();
        let b = symbols.make_fun();

        let left = Term::atom(a);
        let right = Term::atom(b);
        assert_eq!(left.unify(&right), None); // a and b do not match
    }
    #[test]
    fn unify_2() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();

        let left = Term::variable(x);
        let right = Term::variable(x);
        assert_eq!(left.unify(&right), Some(Substitution::new())); // tautology: X = X by definition
    }
    #[test]
    fn unify_3() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let a = symbols.make_fun();

        let left = Term::atom(a);
        let right = Term::variable(x);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::atom(a)); // X := a
        assert_eq!(mgu, Some(sub));  // X is assigned constant a
    }
    #[test]
    fn unify_4() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();

        let left = Term::variable(x);
        let right = Term::variable(y);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::variable(y));

        assert_eq!(mgu, Some(sub)); // X and Y alias
    }
    #[test]
    fn unify_5() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let f = symbols.make_fun();
        let a = symbols.make_fun();
        let b = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::atom(a),
            Term::variable(x),
        ]);
        let right = Term::predicate(f, vec![
            Term::atom(a),
            Term::atom(b),
        ]);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::atom(b));
        assert_eq!(mgu, Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_6() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let f = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::variable(x),
        ]);
        let right = Term::predicate(f, vec![
            Term::variable(y),
        ]);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::variable(y));
        assert_eq!(mgu, Some(sub));  // functions and constants match, X and Y alias
    }
    #[test]
    fn unify_7() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let f = symbols.make_fun();
        let g = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::variable(x),
        ]);
        let right = Term::predicate(g, vec![
            Term::variable(y),
        ]);
        let mgu = left.unify(&right);

        assert_eq!(mgu, None);  // functions do not match
    }
    #[test]
    fn unify_8() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let z = symbols.make_var();
        let f1 = symbols.make_fun();
        let f2 = symbols.make_fun();

        let left = Term::predicate(f1, vec![
            Term::variable(x),
        ]);
        let right = Term::predicate(f2, vec![
            Term::variable(y),
            Term::variable(z),
        ]);
        let mgu = left.unify(&right);

        assert_eq!(mgu, None);  // Term::predicates have different arities
    }
    #[test]
    fn unify_9() {
        let mut symbols = SymbolTable::new();
        let x= symbols.make_var();
        let f = symbols.make_fun();
        let a = symbols.make_fun();
        let b = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::atom(a),
            Term::variable(x),
        ]);
        let right = Term::predicate(f, vec![
            Term::atom(a),
            Term::atom(b),
        ]);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::atom(b));
        assert_eq!(mgu, Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_10() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let f = symbols.make_fun();
        let g = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::predicate(g, vec![
                Term::variable(x),
            ]),
        ]);
        let right = Term::predicate(f, vec![
            Term::variable(y),
        ]);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(y, Term::predicate(g, vec![
            Term::variable(x)
        ]));
        assert_eq!(mgu, Some(sub));  // y gets unified with the term g(x)
    }
    #[test]
    fn unify_11() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let y = symbols.make_var();
        let f = symbols.make_fun();
        let g = symbols.make_fun();
        let a = symbols.make_fun();

        let left = Term::predicate(f, vec![
            Term::predicate(g, vec![
                Term::variable(x),
            ]),
            Term::variable(x),
        ]);
        let right = Term::predicate(f, vec![
            Term::variable(y),
            Term::atom(a)
        ]);
        let mgu = left.unify(&right);

        let mut sub = Substitution::new();
        sub.insert(x, Term::atom(a));
        sub.insert(y, Term::predicate(g, vec![
            Term::atom(a)
        ]));

        assert_eq!(mgu, Some(sub));  // x assigned to constant a, y assigned to term g(a)
    }
    #[test]
    fn unify_12() {
        let mut symbols = SymbolTable::new();
        let x = symbols.make_var();
        let f = symbols.make_fun();

        let left = Term::variable(x);
        let right = Term::predicate(f, vec![
            Term::variable(x),
        ]);
        let mgu = left.unify(&right);

        assert_eq!(mgu, None);  // can not unify without infinite descent
    }
}
