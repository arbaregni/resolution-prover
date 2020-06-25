use std::{fmt};
use crate::ast::{Expr, ExprKind};

/// A literal predicate expression, with no logical connectives
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LiteralExpr<'a> {
    name: &'a str,
    args: Vec<LiteralExpr<'a>>,
}

impl <'a> LiteralExpr<'a> {
    pub fn atom(name: &'a str) -> LiteralExpr<'a> {
        LiteralExpr { name, args: Vec::new(), }
    }
    pub fn predicate(name: &'a str, args: Vec<LiteralExpr<'a>>) -> LiteralExpr<'a> {
        LiteralExpr { name, args }
    }
    pub fn into(self) -> Expr<'a> {
        ExprKind::Literal(self).into()
    }
}

impl fmt::Debug for LiteralExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.name)?;
        } else {
            let mut dt = f.debug_tuple(self.name);
            for arg in &self.args {
                dt.field(arg);
            }
            dt.finish()?;
        }
        Ok(())
    }
}
