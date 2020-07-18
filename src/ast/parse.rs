use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::error::{Error, ErrorVariant, InputLocation};
use pest_derive::*;

use crate::ast::{Expr, ExprKind, Term};
use crate::error::BoxedErrorTrait;
use itertools::{Itertools, Position};
use crate::ast::symbols::SymbolTable;


#[derive(Parser)]
#[grammar = "../grammar.pest"]
struct Grammar;

pub fn parse(source: &str) -> Result<(SymbolTable, Expr), BoxedErrorTrait> {
    let mut symbols = SymbolTable::new();
    let expr = parse_with_symbols(source, &mut symbols)?;
    Ok( (symbols, expr) )
}

pub fn parse_with_symbols<'a>(source: &'a str, symbols: &mut SymbolTable<'a>) -> Result<Expr<'a>, BoxedErrorTrait> {
    // pest (essentially) tokenizes it for us,
    // all we have to do is deal with operator precedence
    // and converting into Expr structs
    let pairs = Grammar::parse(Rule::source, source).map_err(|e| explain_reserved(source, e))?;
    let expr = parse_expr(pairs, symbols)?;
    Ok(expr)
}

fn parse_expr<'a>(pairs: Pairs<'a, Rule>, symbols: &mut SymbolTable<'a>) -> Result<Expr<'a>, BoxedErrorTrait> {
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
                        let variant = ErrorVariant::<Rule>::CustomError {
                            message: format!("unexpected {:?} after {:?}; try adding parenthesis to disambiguate",
                                              new_operator.as_rule(), old_operator.as_rule()
                            )
                        };
                        let error = Error::new_from_span(variant, new_operator.as_span());
                        return Err(Box::new(error));
                    }
                    Some(_) => {}
                }
            }
            _ => {
                // not an operator, it is a term
                terms.push(parse_term(pair, symbols)?);
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
                let variant = ErrorVariant::<Rule>::CustomError {
                    message: "biconditional chains are not supported yet".to_string()
                };
                let error = Error::new_from_span(variant, p.as_span());
                return Err(Box::new(error));
            }
            let last = terms.pop().unwrap();
            let first = terms.pop().unwrap();
            ExprKind::Iff(first, last).into()
        }
        Some((Rule::xor, p)) => {
            if terms.len() != 2 {
                let variant = ErrorVariant::<Rule>::CustomError {
                    message: "exclusive or chains are not supported yet".to_string()
                };
                let error = Error::new_from_span(variant, p.as_span());
                return Err(Box::new(error));
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
            return internal_error!("`{:?}` is not a valid operator", rule);
        }
    };
    Ok(expr)
}

fn parse_term<'a>(pair: Pair<'a, Rule>, symbols: &mut SymbolTable<'a>) -> Result<Expr<'a>, BoxedErrorTrait> {
    let expr = match pair.as_rule() {
        Rule::literal => {
            let name = pair.as_str();
            if let Some(var_id) = symbols.var_id(name) {
                Term::variable(var_id).into()
            } else {
                Term::atom(name).into()
            }
        }
        Rule::negation => {
            let inner = parse_expr(pair.into_inner(), symbols)?;
            ExprKind::Not(inner).into()
        }
        Rule::parenthetical => {
            parse_expr(pair.into_inner(), symbols)?
        }
        Rule::pred => parse_literal(pair.into_inner(), symbols)?.into(),
        Rule::quantified => {
            let mut iter = pair.into_inner();
            let quantifier = if let Some(quantifier) = iter.next() {
                quantifier.as_rule()
            } else {
                return internal_error!("quantified missing its quantifier")
            };
            let name = if let Some(name_pair) = iter.next() {
                name_pair.as_str()
            } else {
                return internal_error!("quantified missing its variable")
            };
            // bind the name to a variable, but only in our subscope
            let (var, shadow_info) = symbols.shadow_var(name);
            let expr = parse_expr(iter, symbols)?;
            symbols.restore_binding(shadow_info);

            match quantifier {
                Rule::univ => {
                    ExprKind::Universal(name, var, expr).into()
                },
                Rule::exis => {
                    ExprKind::Existential(name, var, expr).into()
                },
                _ => return internal_error!("unexpected quantifier {:?}", quantifier)
            }
        }
        // we're not expecting operators or arguments or EOI here
         Rule::arg | Rule::univ | Rule::exis | Rule::operator
        | Rule::or | Rule::and | Rule::implies | Rule::xor | Rule::bicond | Rule::EOI => {
             return internal_error!("unexpected operator or EOI `{}` in parse_term", pair.as_str());
        }
        // silent rules produce nothing
          Rule::WHITESPACE | Rule::reserved
        | Rule::expr | Rule::source | Rule::term | Rule::not => {
             return internal_error!("rule {:?} should produce nothing", pair.as_rule());
          }
    };
    Ok(expr)
}

/// parses a predicate expression
fn parse_literal<'a>(mut pairs: Pairs<'a, Rule>, symbols: &mut SymbolTable<'a>) -> Result<Term<'a>, BoxedErrorTrait> {
    // the name should be the first thing
    let p = if let Some(p) = pairs.next() {
        p
    } else {
        return internal_error!("predicate missing name")
    };
    let name = p.as_str();
    let term = if let Some(var_id) = symbols.var_id(name) {
        if pairs.next().is_some() {
            // this is an error at the level of first order logic:
            // predicates can not be variable
            let variant: ErrorVariant<Rule> = ErrorVariant::CustomError {
                message: format!("can not use `{}` as a predicate name because it is also bound as a variable (see second order logic)", name)
            };
            let err = Error::new_from_span(variant, p.as_span());
            return Err(Box::new(err) as BoxedErrorTrait);
        }
        Term::variable(var_id)
    } else {
        // for a function, the remaining pairs are our arguments
        let args = pairs
            .map(|p| {
                parse_literal(p.into_inner(), symbols)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Term::predicate(name, args)
    };
    Ok(term)
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
    let mut msg = format!("unexpected reserved word `{}`; expected ",
                           pair.as_str().trim());
    match &error.variant {
        ErrorVariant::CustomError { message, .. } => {
            msg.push_str(message);
        },
        ErrorVariant::ParsingError { positives, .. } => {
            for elem in positives.iter().with_position() {
                match elem {
                    Position::First(r) | Position::Middle(r) => {
                        msg.push_str(&format!("{:?}, ", r));
                    }
                    Position::Only(r) => {
                        msg.push_str(&format!("{:?}", r));
                    }
                    Position::Last(r) => {
                        msg.push_str(&format!("or {:?}", r));
                    }
                }
            }
        }
    };
    error.variant = ErrorVariant::CustomError { message: msg };
    error
}
