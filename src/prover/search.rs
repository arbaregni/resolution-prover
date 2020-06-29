use crate::ast::Expr;
use crate::prover::{ClosedClauseSet, Clause};
use crate::error::BoxedErrorTrait;

/// search for a proof of `query` from `givens`
pub fn find_proof(givens: Vec<Expr<'_>>, goal: Expr<'_>) -> Result<bool, BoxedErrorTrait> {
    let mut clause_set = ClosedClauseSet::new();
    // enter all the givens
    for expr in givens {
        expr.into_clauses(&mut clause_set)?;
    }
    // we do proof by contradiction
    // negate the goal, and if we find a contradiction, that's a proof
    goal
        .negate()
        .into_clauses(&mut clause_set)?;
    println!("clause_set: {:#?}", clause_set);
    // search for the contradiction
    let success = clause_set.has_contradiction();

    println!("after: {:#?}", clause_set);
    Ok( success )
}

impl ClosedClauseSet<'_> {
    pub fn has_contradiction(&mut self) -> bool {
        // every clause strictly before the cutoff has been completely resolved
        let mut cutoff = 0;
        loop {
            if let Some(clause) = self.clauses.get_index(cutoff) {
                if clause.is_empty() {
                    return true; // found a contradiction!
                }
                let to_resolve = self.possible_resolution_partners(clause);
                let products = to_resolve
                    .into_iter()        // iterate over everything to resolve, and resolve them with the original clause
                    .filter_map(|(id, sub)| {
                        let other = self.get(id);
                        clause.resolve_under_substitution(other, &sub)
                    })
                    .chain(self.factors(clause)) // add every reduction of the clause to the vector
                    .collect::<Vec<Clause>>();

                println!("============================================================");
                println!("resolving {:?} produced: {:?}", clause, products);

                for product in products.into_iter() {
                    if product.is_empty() {
                        return true; // found a contradiction
                    }
                    self.integrate_clause(product);
                }

                // println!("current set: {:#?}", self);

                // advance the cutoff
                cutoff += 1;

            } else {
                // the cut off has reached the end, and we haven't found an empty clause
                // because everything all the clauses before the cutoff is closed,
                // we know there is no way to get the empty clause
                return false;
            }
        }
    }
}

