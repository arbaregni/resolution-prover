#[macro_use]
mod error;
#[macro_use]
mod prover;
mod ast;

extern crate pretty_env_logger;
#[macro_use] extern crate log;

use error::BoxedErrorTrait;
use ast::SymbolTable;
use prover::ClosedClauseSet;

/// Parse and the givens and the goal,
/// search for a proof, returning `Ok(true)` on if one was found, `Ok(false)` otherwise
#[inline]
pub fn find_proof(givens: &[&str], goal: &str) -> Result<bool, BoxedErrorTrait> {
    let mut symbols = SymbolTable::new();

    // parse the givens and the goal
    let givens = givens
        .iter()
        .map(|&source| ast::parse_withsymbols(source, &mut symbols))
        .collect::<Result<Vec<_>, _>>()?;
    let goal = ast::parse_withsymbols(goal, &mut symbols)?;

    let success = prover::find_proof(&mut symbols, givens, goal)?;

    Ok( success )
}

/// Parse and normalize the query expression,
/// returning `Ok(clause_set)`, which is the query in clausal normal form
#[inline]
pub fn find_clause_set(query: &str) -> Result<ClosedClauseSet, BoxedErrorTrait> {
    let (mut symbols, query) = ast::parse(query)?;
    let mut clause_set = ClosedClauseSet::new();
    query.into_clauses(&mut symbols, &mut clause_set)?;
    Ok(clause_set)
}
