use map_in_place::MapVecInPlace;
use itertools::Itertools;
use crate::prover::{ClosedClauseSet, ClauseBuilder};
use std::fmt::Formatter;
use std::{fmt, iter};

use crate::error::*;

/// A high level expression
#[derive(PartialEq, Eq, Clone)]
pub struct Expr<'a> {
    kind: Box<ExprKind<'a>>
}
/// Represents what type of expression it is, and any associated data
#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(dead_code)]
pub enum ExprKind<'a> {
    Literal(&'a str),
    Not(Expr<'a>),
    If(Expr<'a>, Expr<'a>),
    Iff(Expr<'a>, Expr<'a>),
    Xor(Expr<'a>, Expr<'a>),
    Or(Vec<Expr<'a>>),
    And(Vec<Expr<'a>>),
}

impl <'a> ExprKind<'a> {
    #[allow(dead_code)]
    pub fn into(self) -> Expr<'a> {
        Expr { kind: Box::new(self) }
    }
}

impl <'a> Expr<'a> {
    /// Return the negation of this expression
    #[allow(dead_code)]
    pub fn negate(self) -> Expr<'a> {
        ExprKind::Not(self).into()
    }

    /// Replace implies with its definition,
    /// flattens all nested `And`s and `Or`s
    /// and move all `Not`s to immediately before atoms
    /// by applying the de morgan's and double negation elim.
    #[allow(dead_code)]
    pub fn normalize_negations(self) -> Expr<'a> {
        use ExprKind::*;
        match *self.kind {
            // convert `not not P` to `P`
            Not(negated) => {
                match *negated.kind {
                    // double negation elimination
                    // `not not P` becomes `P`
                    Not(inner) => {
                        inner.normalize_negations()
                    }
                    // de morgan's law
                    // `not (P and Q)` becomes `not P or not Q`
                    And(subexprs) => {
                        Or(subexprs.map_in_place(|e| e.negate().normalize_negations())).into()
                    }
                    // de morgan's law
                    // `not (P or Q)` becomes `not P and not Q`
                    Or(subexprs) => {
                        And(subexprs.map_in_place(|e| e.negate().normalize_negations())).into()
                    }
                    // negation of an implication
                    // `not (P implies Q)` becomes `P and not Q`
                    If(condition, consequence) => {
                        And(vec![
                            condition.normalize_negations(),
                            consequence.negate().normalize_negations(),
                        ]).into()
                    }
                    // negation of a biconditional is an exclusive or
                    // `not (p iff q)` becomes `(p or q) and (~p or ~q)`
                    Iff(p, q) => {
                        let not_p = Not(p.clone()).into().normalize_negations();
                        let p = p.normalize_negations();
                        let not_q = Not(q.clone()).into().normalize_negations();
                        let q = q.normalize_negations();
                        And(vec![
                            Or(vec![p, q]).into(),
                            Or(vec![not_p, not_q]).into(),
                        ]).into()
                    }
                    // negation of exclusive or is a biconditional
                    // `not (p xor q)` becomes `(~p or q) and (~p or q)`
                    Xor(p, q) => {
                        let not_p = Not(p.clone()).into().normalize_negations();
                        let p = p.normalize_negations();
                        let not_q = Not(q.clone()).into().normalize_negations();
                        let q = q.normalize_negations();
                        And(vec![
                            Or(vec![not_p, q]).into(),
                            Or(vec![p, not_q]).into(),
                        ]).into()
                    },
                    Literal(_) => Not(negated).into(),
                }
            }
            // convert `P implies Q` to `not P or Q`
            If(condition, consequence) => {
                let negated = Not(condition).into().normalize_negations();
                let other = consequence.normalize_negations();
                Or(vec![negated, other]).into()
            }
            // convert `P iff Q` to `(~P or Q) and (P or ~Q)``
            Iff(p, q) => {
                let not_p = Not(p.clone()).into().normalize_negations();
                let p = p.clone().normalize_negations();
                let not_q = Not(q.clone()).into().normalize_negations();
                let q = q.normalize_negations();
                And(vec![
                    Or(vec![not_p, q]).into(),
                    Or(vec![p, not_q]).into(),
                ]).into()
            }
            // convert `P xor Q` to (P or Q) and (~P or ~Q)
            Xor(p, q) => {
                let not_p = Not(p.clone()).into().normalize_negations();
                let p = p.clone().normalize_negations();
                let not_q = Not(q.clone()).into().normalize_negations();
                let q = q.normalize_negations();
                And(vec![
                    Or(vec![p, q]).into(),
                    Or(vec![not_p, not_q]).into(),
                ]).into()
            },
            Or(subexprs) => {
                // normalize all our subexpressions
                // assume, inductively, that `Or`s have been flattened
                // now, we just flatten any that we find
                let subexprs = subexprs
                    .map_in_place(Expr::normalize_negations)
                    .into_iter()
                    .flat_map(|expr| {
                        if let ExprKind::Or(nested_terms) = *expr.kind {
                            Box::new(nested_terms.into_iter()) as Box<dyn Iterator<Item = Expr>>
                        } else {
                            Box::new(iter::once(expr)) as Box<dyn Iterator<Item = Expr>>
                        }
                    })
                    .collect();
                Or(subexprs).into()
            }
            And(subexprs) => {
                // normalize all our subexpressions
                // assume, inductively, that `And`s have been flattened
                // now, we just flatten any that we find
                let subexprs = subexprs
                    .map_in_place(Expr::normalize_negations)
                    .into_iter()
                    .flat_map(|expr| {
                        if let ExprKind::And(nested_terms) = *expr.kind {
                            Box::new(nested_terms.into_iter()) as Box<dyn Iterator<Item = Expr>>
                        } else {
                            Box::new(iter::once(expr)) as Box<dyn Iterator<Item = Expr>>
                        }
                    })
                    .collect();
                And(subexprs).into()
            }
            Literal(_) => self
        }
    }

    /// Distribute all of the ors inward as much as possible,
    /// i.e. `p + q + rs` becomes `(p + q + r)(p + q + s)`
    /// removes redundant `Or`s and `And`s
    #[allow(dead_code)]
    pub fn distribute_ors_inward(self) -> Expr<'a> {
        // println!("distributing ors inward on {:#?}", self);
        use ExprKind::*;
        match *self.kind {
            Or(mut or_terms) => {
                // search for an `And` we can distribute over
                let search_result = or_terms.iter()
                    .find_position(|expr| {
                        if let And(_) = *expr.kind {
                            true
                        } else {
                            false
                        }
                    });
                if let Some((index, _)) = search_result {
                    // here we have found the `rs` expression (see doc example)
                    // take the And expression out
                    let and_terms = match *or_terms.swap_remove(index).kind {
                        And(and_terms) => and_terms,
                        _ => unreachable!(),
                    };
                    // distribute the remaining Or terms over the And
                    // this is where we generate `(p + q + r)` and `(p + q + s)`
                    let new_terms = and_terms
                        .into_iter()
                        .map(|term| {
                            // get the terms that we're or'ing inward, i.e. `p + q`
                            let mut new_terms = or_terms.clone();
                            // add the terms from the conjunction, i.e. `r` or `s`
                            new_terms.push(term);
                            // now recursively distribute
                            Or(new_terms).into().distribute_ors_inward()
                        })
                        .collect::<Vec<_>>();
                    And(new_terms).into()
                } else {
                    // here we haven't found any ands to distribute into => all done!
                    Or(or_terms).into()
                }
            },
            // simply recurse on all of our children
            And(exprs) => And(exprs.map_in_place(Expr::distribute_ors_inward)).into(),
            If(cond, cons) => If(cond.distribute_ors_inward(), cons.distribute_ors_inward()).into(),
            Iff(p, q) => Iff(p.distribute_ors_inward(), q.distribute_ors_inward()).into(),
            Xor(p, q) => Xor(p.distribute_ors_inward(), q.distribute_ors_inward()).into(),
            Not(inner) => Not(inner.distribute_ors_inward()).into(),
            Literal(_) => self,
        }
    }

    /// Converts an expression in conjunctive normal form into clauses,
    /// interning them in `interner` and then adding them to `clause_set`
    /// Panics if this is not the case:
    ///  - if any expr kind other than `Or`, `And`, `Not`, and `Literal` are present
    ///  - if `Not` surround anything but a `Literal`
    ///  - if `Or`s surround any `And`s
    #[allow(dead_code)]
    pub fn make_clause_set(self, clause_set: &mut ClosedClauseSet<'a>) -> Result<(), BoxedErrorTrait>{
        // println!("making into a clause set: {:#?}", self);
        use ExprKind::*;
        match *self.kind {
            // there is only one clause
            Literal(_) | Not(_) | Or(_) => {
                let mut builder = ClauseBuilder::new();
                self.make_clause(&mut builder)?;
                if let Some(clause) = builder.finish() {
                    clause_set.integrate_clause(clause);
                }
            }
            And(exprs) => {
                // ands must be on the highest level
                // we go through each of the sub-exprs and
                // add whatever clauses they produce
                for expr in exprs {
                    expr.make_clause_set(clause_set)?;
                }
            }
            _ => {
                error!("calling make_clause helper on non-normalized expr {:?}", self);
                return internal_error!();
            }
        }
        Ok( () )
    }
    /// adds the current expression to the clause
    /// panicking if it can not be done (i.e. it was an `And` or `If`)
    #[allow(dead_code)]
    fn make_clause(self, builder: &mut ClauseBuilder<'a>) -> Result<(), BoxedErrorTrait> {
        use ExprKind::*;
        match *self.kind {
            Literal(name) => {
                builder.insert(name, true);
            },
            Not(inner) => {
                if let Literal(name) = *inner.kind {
                    builder.insert(name, false);
                } else {
                    error!("calling make_clause helper on non-normalized expr Not({:?})", inner);
                    return internal_error!();
                }
            }
            Or(exprs) => {
                for expr in exprs {
                    expr.make_clause(builder)?;
                }
            }
            _ => {
                error!("calling make_clause helper on non-normalized expr {:?}", self);
                return internal_error!();
            }
        };
        Ok( () )
    }

    /// Convert an expression to clausal normal form,
    /// inserting all new clauses into the clause set
    #[allow(dead_code)]
    pub fn into_clauses(self, clause_set: &mut ClosedClauseSet<'a>) -> Result<(), BoxedErrorTrait> {
        // println!("converting: {:?}", self);
        self
            .normalize_negations()
            .distribute_ors_inward()
            .make_clause_set(clause_set)?;
        Ok( ()  )
    }
}

impl fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &*self.kind {
            ExprKind::Literal(name) => write!(f, "{:?}", name)?,
            ExprKind::Not(inner) => write!(f, "Not({:?})", inner)?,
            ExprKind::If(cond, cons) => write!(f, "Implies({:?} => {:?})", cond, cons)?,
            ExprKind::Iff(p, q) => {
                write!(f, "Iff(")?;
                f.debug_list().entry(p).entry(q).finish()?;
                write!(f, ")")?;
            },
            ExprKind::Xor(p, q) => {
                write!(f, "Xor(")?;
                f.debug_list().entry(p).entry(q).finish()?;
                write!(f, ")")?;
            },
            ExprKind::Or(exprs) => {
                write!(f, "Or(")?;
                f.debug_list().entries(exprs.clone()).finish()?;
                write!(f, ")")?;
            },
            ExprKind::And(exprs) => {
                write!(f, "And(")?;
                f.debug_list().entries(exprs.clone()).finish()?;
                write!(f, ")")?;
            },
        };
        Ok( () )
    }
}
