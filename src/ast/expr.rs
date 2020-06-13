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
