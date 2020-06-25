use std::{fmt};
use crate::ast::{Expr, ExprKind};
use std::collections::HashMap;
use LiteralKind::*;

/// A literal predicate expression, with no logical connectives
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LiteralExpr<'a> {
    kind: LiteralKind<'a>
}
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LiteralKind<'a> {
    /// Variables are terms that may take on any value. They are produced by universal quantifiers
    Variable(&'a str),
    /// Functions are names and arguments. Constants are zero-arity functions
    Function(&'a str, Vec<LiteralExpr<'a>>),
}
/// Variable names are mapped to Literal Expressions
pub type Substitution<'a> = HashMap<&'a str, LiteralExpr<'a>>;

impl <'a> LiteralKind<'a> {
    fn into_expr(self) -> LiteralExpr<'a> {
        LiteralExpr { kind: self }
    }
}
impl <'a> LiteralExpr<'a> {
    pub fn atom(name: &'a str) -> LiteralExpr<'a> {
        LiteralKind::Function(name, Vec::new()).into_expr()
    }
    pub fn predicate(name: &'a str, args: Vec<LiteralExpr<'a>>) -> LiteralExpr<'a> {
        LiteralKind::Function(name, args).into_expr()
    }
    pub fn into(self) -> Expr<'a> {
        ExprKind::Literal(self).into()
    }
    /// Search for the variable name in our structure
    pub fn contains(&self, var_name: &str) -> bool {
        match &self.kind {
            LiteralKind::Variable(name) => *name == var_name,
            LiteralKind::Function(_, args) => args.iter().any(|a| a.contains(var_name)),
        }
    }
    /// Perform the given substitution, producing a new literal expression
    pub fn substitute(&self, sub: &Substitution<'a>) -> LiteralExpr<'a> {
        match &self.kind {
            Variable(name) => {
                if let Some(lit) = sub.get(name) {
                    lit.clone()
                } else {
                    Variable(name).into_expr()
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
    pub fn unify(&self, other: &LiteralExpr<'a>) -> Option<Substitution<'a>> {
        match (&self.kind, &other.kind) {
            (Variable(x), Variable(y)) => {
                // substitute one variable for another
                let mut sub = Substitution::new();
                if x != y {
                    sub.insert(x, Variable(y).into_expr());
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
                sub.insert(x, Function(f, args.clone()).into_expr());
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

impl fmt::Debug for LiteralExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            Variable(name) => write!(f, "${}", name)?,
            Function(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)?;
                } else {
                    let mut dt = f.debug_tuple(name);
                    for arg in args {
                        dt.field(arg);
                    }
                    dt.finish()?;
                }
            }
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use crate::ast::LiteralKind::{Function, Variable};
    use crate::ast::Substitution;

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
        let left = Variable("X").into_expr();
        let right = Variable("X").into_expr();
        assert_eq!(left.unify(&right), Some(Substitution::new())); // tautology: X = X by definition
    }
    #[test]
    fn unify_3() {
        let left = Function("a", vec![]).into_expr();
        let right = Variable("X").into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Function("a", vec![]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // X is assigned constant a
    }
    #[test]
    fn unify_4() {
        let left = Variable("X").into_expr();
        let right = Variable("Y").into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Variable("Y").into_expr());
        assert_eq!(left.unify(&right), Some(sub)); // X and Y alias
    }
    #[test]
    fn unify_5() {
        let left = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Function("b", vec![]).into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Function("b", vec![]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_6() {
        let left = Function("f", vec![
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Variable("Y").into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Variable("Y").into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X and Y alias
    }
    #[test]
    fn unify_7() {
        let left = Function("f", vec![
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("g", vec![
            Variable("Y").into_expr(),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // functions do not match
    }
    #[test]
    fn unify_8() {
        let left = Function("f", vec![
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Variable("Y").into_expr(),
            Variable("Z").into_expr(),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // functions have different arities
    }
    #[test]
    fn unify_9() {
        let left = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Function("a", vec![]).into_expr(),
            Function("b", vec![]).into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Function("b", vec![]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // functions and constants match, X is assigned constant b
    }
    #[test]
    fn unify_10() {
        let left = Function("f", vec![
            Function("g", vec![
                Variable("X").into_expr(),
            ]).into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Variable("Y").into_expr(),
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert("Y", Function("g", vec![
            Variable("X").into_expr()
        ]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // y gets unified with the term g(x)
    }
    #[test]
    fn unify_11() {
        let left = Function("f", vec![
            Function("g", vec![
                Variable("X").into_expr(),
            ]).into_expr(),
            Variable("X").into_expr(),
        ]).into_expr();
        let right = Function("f", vec![
            Variable("Y").into_expr(),
            Function("a", vec![]).into_expr()
        ]).into_expr();
        let mut sub = Substitution::new();
        sub.insert("X", Function("a", vec![]).into_expr());
        sub.insert("Y", Function("g", vec![
            Function("a", vec![]).into_expr()
        ]).into_expr());
        assert_eq!(left.unify(&right), Some(sub));  // x assigned to constant a, y assigned to term g(a)
    }
    #[test]
    fn unify_12() {
        let left = Variable("X").into_expr();
        let right = Function("f", vec![
            Variable("X").into_expr(),
        ]).into_expr();
        assert_eq!(left.unify(&right), None);  // can not unify without infinite descent
    }


}
