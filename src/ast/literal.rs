use std::fmt;
use serde::export::Formatter;

/// A literal predicate expression, with no logical connectives
#[derive(Clone, PartialEq, Eq)]
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
}

impl fmt::Debug for LiteralExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.name)?;
        } else {
            write!(f, "{}(", self.name)?;
            f.debug_list().entries(self.args.clone()).finish()?;
            write!(f, ")")?;
        }
        Ok(())
    }
}

