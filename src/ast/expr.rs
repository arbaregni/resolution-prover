use map_in_place::MapVecInPlace;

/// A high level expression
#[derive(Debug, PartialEq, Eq)]
pub struct Expr<'a> {
    kind: Box<ExprKind<'a>>
}
/// Represents what type of expression it is, and any associated data
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ExprKind<'a> {
    Literal(&'a str),
    Not(Expr<'a>),
    If(Expr<'a>, Expr<'a>),
    Or(Vec<Expr<'a>>),
    And(Vec<Expr<'a>>),
}

impl <'a> ExprKind<'a> {
    pub fn into(self) -> Expr<'a> {
        Expr { kind: Box::new(self) }
    }
}

impl <'a> Expr<'a> {
    pub fn negate(self) -> Expr<'a> {
        ExprKind::Not(self).into()
    }
    /// Eliminate implications and double implications,
    /// and move all NOTs to immediately before atoms
    pub fn normalize_negations(mut self) -> Expr<'a> {
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
                    _ => {
                        Not(negated).into()
                    }
                }
            }
            // convert `P implies Q` to `not P or Q`
            If(condition, consequence) => {
                let negated = Not(condition).into().normalize_negations();
                let other = consequence.normalize_negations();
                Or(vec![negated, other]).into()
            }
            Or(mut subexprs) => {
                Or(subexprs.map_in_place(Expr::normalize_negations)).into()
            }
            And(mut subexprs) => {
                And(subexprs.map_in_place(Expr::normalize_negations)).into()
            }
            Literal(_) => self
        }
    }
}
