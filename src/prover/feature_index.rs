use crate::prover::Clause;
use indexmap::set::IndexSet;
use crate::ast::{SymbolTable, Symbol};
use std::collections::HashMap;
use std::rc::Rc;

fn count_pos(clause: &Clause) -> u32 {
    clause.iter_pos().count() as u32
}

#[derive(Copy, Clone, Debug)]
enum Feature {
    CountPos,
    CountNeg,
    SymbolOccurPos(Symbol),
    SymbolOccurNeg(Symbol),
}
impl Feature {
    fn apply(&self, clause: &Clause) -> u32 {
        let count = match self {
            Feature::CountPos => clause.iter_pos().count(),
            Feature::CountNeg => clause.iter_neg().count(),
            Feature::SymbolOccurPos(s) => {
                clause.iter_pos()
                    .map(|t| t.count_symbol(*s))
                    .count()
            },
            Feature::SymbolOccurNeg(s) => {
                clause.iter_neg()
                    .map(|t| t.count_symbol(*s))
                    .count()
            },
        };
        count as u32
    }
    fn distribution(&self, clause_set: &IndexSet<Clause>) -> Vec<u32> {
        clause_set.iter()
            .map(|clause| {
                self.apply(clause)
            })
            .collect()
    }
}

pub struct FeatureVectorFunction {
    features: Vec<Feature>,
}

impl FeatureVectorFunction {
    pub fn new() -> FeatureVectorFunction {
        FeatureVectorFunction { features: Vec::new() }
    }
    pub fn from(clause_set: &IndexSet<Clause>, symbols: &SymbolTable) -> FeatureVectorFunction {
        // all the features to select from
        let mut features = Vec::with_capacity(2 + 2 * symbols.count());
        features.push(Feature::CountPos);
        features.push(Feature::CountNeg);
        for s in symbols.symbols(){
            features.push(Feature::SymbolOccurPos(s));
            features.push(Feature::SymbolOccurNeg(s));
        }

        // rate the features by informativity
        let mut stats = features.iter()
            .map(|feature| {
                let distr = feature.distribution(clause_set);
                todo!("some statistics")
            })
            .collect::<Vec<_>>();

        //todo: sort & filter them by the informativity


        FeatureVectorFunction { features }
    }
    pub fn apply(&self, clause: &Clause) -> Vec<u32> {
        self.features.iter()
            .map(|feature| feature.apply(clause))
            .collect()
    }
}

type NodeId = usize;

enum Node {
    Inner(HashMap<u32, NodeId>),
    Leaf(Vec<Rc<Clause>>),
}
pub struct SubsumptionTree {
    feat_vec_fun: FeatureVectorFunction,
    store: Vec<Rc<Clause>>,
}
impl SubsumptionTree {
    pub fn new() -> SubsumptionTree {
        SubsumptionTree {
            feat_vec_fun: FeatureVectorFunction::new(),
            store: vec![],
        }
    }
    /// Insert `clause` into the collection if it is not subsumed by anything else
    /// Return `true` if insertion took place (i.e. it represented a new fact)
    pub fn insert(&mut self, clause: Rc<Clause>) -> bool {
        for c in self.store.iter() {
            if c.subsumes(&clause) {
                return false; // did not insert
            }
        }
        self.store.push(clause);
        true
    }
}