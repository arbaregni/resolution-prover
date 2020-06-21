use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::error::{Error, ErrorVariant, InputLocation};

use pest_derive::*;
use crate::ast::{Expr, ExprKind};

#[derive(Parser)]
#[grammar = "../grammar.pest"]
struct Grammar;

pub fn parse(source: &str) -> Result<Expr<'_>, Error<Rule>> {
    // pest (essentially) tokenizes it for us,
    // all we have to do is deal with operator precedence
    // and converting into Expr structs
    let pairs = Grammar::parse(Rule::source, source).map_err(|e| explain_reserved(source, e))?;
    parse_expr(pairs)
}

fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr<'_>, Error<Rule>> {
    let mut operator = None; // we don't have an operator yet
    let mut terms = vec![];
    for pair in pairs {
        match pair.as_rule() {
            Rule::EOI => { break; }
            Rule::operator => {
                let new_operator = pair.into_inner()
                    .next()
                    .expect("operator missing inner rule (all operators should be `and`, `or`, or `implies`");
                match operator {
                    // if this is the first operator we've seen, update the operator
                    None => operator = Some(new_operator),
                    // we can not chain implications, and we can not chain different operators together
                    Some(old_operator)
                        if old_operator.as_rule() == Rule::implies
                        || old_operator.as_rule() != new_operator.as_rule() => {
                        let variant = ErrorVariant::CustomError {
                            message: format!("unexpected {:?} after {:?}; try adding parenthesis to disambiguate",
                                              new_operator.as_rule(), old_operator.as_rule()
                            )
                        };
                        let error = Error::new_from_span(variant, new_operator.as_span());
                        return Err(error);
                    }
                    Some(_) => {}
                }
            }
            _ => {
                // not an operator, it is a term
                terms.push(parse_term(pair)?);
            }
        }
    }
    let expr = match operator.map(|p| (p.as_rule(), p)) {
        None => {
            // the parsing rules should prevent two adjacent terms
            assert_eq!(1, terms.len());
            terms.pop().unwrap()
        }
        Some((Rule::implies, _)) => {
            // the parsing rules should prevent chaining implications w/o parens
            assert_eq!(2, terms.len());
            let last = terms.pop().unwrap();
            let first = terms.pop().unwrap();
            ExprKind::If(first, last).into()
        }
        Some((Rule::bicond, p)) => {
            if terms.len() != 2 {
                let variant = ErrorVariant::CustomError {
                    message: "biconditional chains are not supported yet".to_string()
                };
                return Err(Error::new_from_span(variant, p.as_span()));
            }
            let last = terms.pop().unwrap();
            let first = terms.pop().unwrap();
            ExprKind::Iff(first, last).into()
        }
        Some((Rule::xor, p)) => {
            if terms.len() != 2 {
                let variant = ErrorVariant::CustomError {
                    message: "exclusive or chains are not supported yet".to_string()
                };
                return Err(Error::new_from_span(variant, p.as_span()));
            }
            let last = terms.pop().unwrap();
            let first = terms.pop().unwrap();
            ExprKind::Xor(first, last).into()
        }
        Some((Rule::and, _)) => {
            ExprKind::And(terms).into()
        }
        Some((Rule::or, _)) => {
            ExprKind::Or(terms).into()
        }
        Some((rule, _)) => {
            panic!("`{:?}` is not a valid operator", rule)
        }
    };
    Ok(expr)
}

fn parse_term(pair: Pair<Rule>) -> Result<Expr<'_>, Error<Rule>> {
    let expr = match pair.as_rule() {
        Rule::literal => {
            ExprKind::Literal(pair.as_str()).into()
        }
        Rule::negation => {
            let inner = parse_expr(pair.into_inner())?;
            ExprKind::Not(inner).into()
        }
        Rule::parenthetical => {
            parse_expr(pair.into_inner())?
        }
        // we're not expecting operators or EOI here
        Rule::operator | Rule::or | Rule::and | Rule::implies | Rule::xor | Rule::bicond | Rule::EOI => {
            panic!("unexpected operator or EOI {} in parse_term", pair.as_str())
        }
        // silent rules produce nothing
          Rule::WHITESPACE | Rule::reserved
        | Rule::expr | Rule::source | Rule::term | Rule::not => panic!("rule {:?} should produce nothing", pair.as_rule())
    };
    Ok(expr)
}

/// updates the error so that reserved words are mentioned in the error message
fn explain_reserved(source: &str, mut error: Error<Rule>) -> Error<Rule> {
    let start_idx = match error.location {
        InputLocation::Pos(idx) => idx,
        InputLocation::Span((idx, _)) => idx,
    };
    // check if reserved word would parse starting here
    let pair = match Grammar::parse(Rule::reserved, &source[start_idx..]) {
        Err(_) => {
            // not a reserved word, it did not fail because of that
            return error;
        }
        Ok(pair) => pair
    };
    error.variant = ErrorVariant::CustomError {
        message: format!("unexpected reserved word `{}`; expected literal, negation, or parenthetical",
                           pair.as_str().trim()
        )
    };
    error
}
