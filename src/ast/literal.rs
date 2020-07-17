use std::{fmt, iter};
use crate::ast::{Expr, ExprKind};
use std::collections::HashMap;
use TermKind::*;
use std::rc::Rc;
use std::ops::Deref;

/// A literal predicate expression, with no logical connectives
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Term<'a> {
    kind: Rc<TermKind<'a>>
}
/// The kind of a literal expression (LiteralExpr wraps around this for now)
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TermKind<'a> {
    /// Variables are terms that may take on any value. They are produced by universal quantifiers
    Variable(VarId<'a>),
    /// Functions are names and arguments. Constants are zero-arity functions
    Function(&'a str, Vec<Term<'a>>),
}
/// Variable names are mapped to Literal Expressions
pub type Substitution<'a> = HashMap<VarId<'a>, Term<'a>>;

/// For our purposes, we want all variables to be equal in the hash map
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct VarId<'a>(pub &'a str);

/// The highest level pattern of a term.
///   For instance,
/// `P(f(a, b, ...), g(h(i(...))))` is represented only
/// as a function named `P` with one argument (arity 1).
/// This is to enable unification based lookup
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TermPattern<'a> {
    /// Representing any
    Variable,
    /// Representing a function with the given name and arity
    Function(&'a str, usize),
}

/// Iterates over all expressions and sub-expressions in the given term
#[derive(Debug, Clone)]
pub struct SubTermIterator<'a> {
    stack: Vec<Term<'a>>,
}

impl <'a> TermKind<'a> {
    fn into_expr(self) -> Term<'a> {
        Term { kind: Rc::new(self) }
    }
}

const EMPTY_TERM_SLICE: &'static [Term] = &[];

impl <'a> Term<'a> {
    pub fn atom(name: &'a str) -> Term<'a> {
        Function(name, Vec::new()).into_expr()
    }
    pub fn predicate(name: &'a str, args: Vec<Term<'a>>) -> Term<'a> {
        Function(name, args).into_expr()
    }
    pub fn variable(name: &'a str) -> Term<'a> {
        TermKind::Variable(VarId(name)).into_expr()
    }
    pub fn into(self) -> Expr<'a> {
        ExprKind::Literal(self).into()
    }
    pub fn kind(&self) -> &TermKind<'a> {
        &self.kind
    }
    /// Search for the variable name in our structure
    pub fn contains(&self, var: &VarId) -> bool {
        match self.kind.deref() {
            Variable(name) => *name == *var,
            Function(_, args) => args.iter().any(|a| a.contains(var)),
        }
    }
    pub fn pattern(&self) -> TermPattern<'a> {
        match self.kind() {
            TermKind::Variable(_) => TermPattern::Variable,
            TermKind::Function(name, args) => TermPattern::Function(name, args.len()),
        }
    }
    pub fn children(&self) -> &[Term<'a>] {
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
    pub fn arity(&self) -> usize {
        match self.kind() {
            TermKind::Variable(_) => 0,
            TermKind::Function(_, args) => args.len(),
        }
    }
    pub fn iter(&self) -> SubTermIterator<'a> {
        SubTermIterator {
            stack: vec![self.clone()]
        }
    }
    /// Perform the given substitution, producing a new literal expression
    pub fn substitute(&self, sub: &Substitution<'a>) -> Term<'a> {
        match self.kind.deref() {
            Variable(name) => {
                if let Some(lit) = sub.get(name) {
                    lit.clone()
                } else {
                    Variable(*name).into_expr()
                }
            }
            Function(f, args) => {
                let mapped = args.iter()
                    .map(|a| a.substitute(sub))
                    .collect::<Vec<_>>();
                Function(*f, mapped).into_expr()
            }
        }
    }
    pub fn unify(&self, other: &Term<'a>) -> Option<Substitution<'a>> {
        match (self.kind.deref(), other.kind.deref()) {
            (Variable(x), Variable(y)) => {
                // substitute one variable for another
                let mut sub = Substitution::new();
                if x != y {
                    sub.insert(*x, Variable(*y).into_expr());
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
                sub.insert(*x, Function(f, args.clone()).into_expr());
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

impl <'a> iter::Iterator for SubTermIterator<'a> {
    type Item = Term<'a>;

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
fn compose<'a>(sub: Substitution<'a>, new: Substitution<'a>) -> Substitution<'a> {
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

impl fmt::Debug for VarId<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl fmt::Debug for Term<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind.deref() {
            Variable(name) => write!(f, "${}", name.0)?,
            Function(name, args) => {
                write!(f, "{}", name)?;
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


#[cfg(test)]
mod tests {
    use crate::ast::TermKind::{Function, Variable};
    use crate::ast::{Substitution, Term, VarId};

    #[test]
    fn unify_0() {
        let left = Function("a", vec![]).into_expr();
        let right = Function("a", vec![]).into_expr();
        assert_eq!(left.unify(&right), Some(Substitution::new())); // tautology: a = a by definition
    }
    #[test]
    fn unify_1() {
        let left = Function("a", vec![]).into_expr();
        let right = Function("b", vec![]).into_expr();
        assert_eq!(left.unify(&right), None); // a and b do not match
    }
    #[test]
    fn unify_2() {
        let left = Term::variable("X");
        let right = Term::variable("X");
        assert_eq!(left.unify(&right), Some(Substitution::new())); // tautology: X = X by definition
    }
    #[test]
    fn unify_3() {
        let left = Function("a", vec![]).into_expr();
        let right = Term::variable("X");
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Term::atom("a"));
        assert_eq!(left.unify(&right), Some(sub));  // X is assigned constant a
    }
    #[test]
    fn unify_4() {
        let left = Term::variable("X");
        let right = Term::variable("Y");
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Term::variable("Y"));
        assert_eq!(left.unify(&right), Some(sub)); // X and Y alias
    }
    #[test]
    fn unify_5() {
        let left = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Term::variable("X"),
        ]).into_expr();
        let right = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Function("b", vec![]).into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Function("b", vec![]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_6() {
        let left = Function("f", vec![
            Term::variable("X"),
        ]).into_expr();
        let right = Function("f", vec![
            Term::variable("Y"),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Term::variable("Y"));
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X and Y alias
    }
    #[test]
    fn unify_7() {
        let left = Function("f", vec![
            Term::variable("X"),
        ]).into_expr();
        let right = Function("g", vec![
            Term::variable("Y"),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // functions do not match
    }
    #[test]
    fn unify_8() {
        let left = Function("f", vec![
            Term::variable("X"),
        ]).into_expr();
        let right = Function("f", vec![
            Term::variable("Y"),
            Term::variable("Z"),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // functions have different arities
    }
    #[test]
    fn unify_9() {
        let left = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Term::variable("X"),
        ]).into_expr();
        let right = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Function("b", vec![]).into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Function("b", vec![]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_10() {
        let left = Function("f", vec![
            Function("g", vec![
                Term::variable("X"),
            ]).into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Term::variable("Y"),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert(VarId("Y"), Function("g", vec![
            Term::variable("X")
        ]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // y gets unified with the term g(x)
    }
    #[test]
    fn unify_11() {
        let left = Function("f", vec![
            Function("g", vec![
                Term::variable("X"),
            ]).into_expr(),
            Term::variable("X"),
        ]).into_expr();
        let right = Function("f", vec![
            Term::variable("Y"),
            Function("a", vec![]).into_expr()
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert(VarId("X"), Function("a", vec![]).into_expr());
        sub.insert(VarId("Y"), Function("g", vec![
            Function("a", vec![]).into_expr()
        ]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // x assigned to constant a, y assigned to term g(a)
    }
    #[test]
    fn unify_12() {
        let left = Term::variable("X");
        let right = Function("f", vec![
            Term::variable("X"),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // can not unify without infinite descent
    }
}
