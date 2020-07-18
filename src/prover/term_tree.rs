use crate::ast::{Term, TermPattern};
use std::fmt;
use std::collections::{HashMap};
use map_in_place::MapVecInPlace;

/// Supports unification based lookup, using a discrimination tree
#[derive(Debug, PartialEq, Eq)]
pub struct TermTree {
    /// All nodes in the discrimination trie
    nodes: Vec<Node>,
    skip_to_next: Vec<Vec<NodeId>>,
}

/// `NodeId` are indices into `nodes` field of `TermMap`
type NodeId = usize;

#[derive(Debug, PartialEq, Eq)]
enum Node {
    Internal(HashMap<TermPattern, NodeId>),
    Leaf(Vec<Term>),
}

impl TermTree {
    /// create an empty term map
    pub fn new() -> TermTree {
        TermTree {
            nodes: vec![Node::new()],
            skip_to_next: vec![Vec::new()],
        }
    }
    /// Updates the `TermMap` to include a new usage of `term`, creating an entry if it doesn't exist
    /// Expects to be called with increasing `clause_id`s
    pub fn update(&mut self, term: Term) {
        // update the discrimination tree
        let mut arity_totals: Vec<(NodeId, usize)> = Vec::new(); // running total of the arity (used for determining subterm boundaries)
        let mut node_id = 0 as NodeId; // start at the root noot
        for subterm in term.iter() {

            // treat the subterm's pattern as a prefix and look up the next trie node
            let num_nodes = self.nodes.len();
            node_id = self.nodes[node_id].get_or_insert(num_nodes, subterm.pattern());
            // if we had to insert a child, then node_id == num_nodes
            if node_id == num_nodes {
                self.nodes.push(Node::new());
                self.skip_to_next.push(Vec::new());
            }

            // deal with everything that has zero arity
            // (we are the node that is skipped to)
            arity_totals = arity_totals.filter_map_in_place(
                |(prev_id, arity_sum)| {
                    if arity_sum == 0 {
                        self.skip_to_next[prev_id].push(node_id);
                        None
                    } else {
                        Some( (prev_id, arity_sum) )
                    }
                }
            );
            // this is an argument to everything that came before it, so we take 1 from the arity sum
            // BUT, we are also part of everythings expression tree, so we add our own arity
            for (_, arity_sum) in arity_totals.iter_mut() {
                *arity_sum = *arity_sum + subterm.arity() - 1;
            }
            arity_totals.push( (node_id, subterm.arity()) );
        }
        // make the final term in our path a leaf
        self.nodes[node_id].leafify(term.clone());
    }

    /// Returns at least all terms which are generalizations of `query_term`,
    /// A term `t` generalizes a query term `s` iff there exists a substitution σ such that σ(t) = s
    /// Further filtering is required
    fn generalizations_of<'t>(&'t self, node_id: NodeId, to_check: &mut Vec<Term>, found: &mut Vec<Term>) {
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                assert!(to_check.is_empty()); // due to fixed_arity functions, we expect the path sizes to be equal
                println!("finding: {:?}", terms);
                found.extend_from_slice(terms.as_slice());
            },
            Node::Internal(map) => {
                let term = to_check.pop().expect("query path ended early");
                // we can def. match our own pattern
                if let Some(child) = map.get(&term.pattern()) {
                    // we must check the subterms
                    for subterm in term.children() {
                        to_check.push(subterm.clone());
                    }
                    self.generalizations_of(*child, to_check, found);
                }
                // we can match any variable, but it consumes the current subterm and all its children
                if let Some(child) = map.get(&TermPattern::Variable) {
                    // we don't check the subterms
                    self.generalizations_of(*child, to_check, found);
                }
            },
        }
    }
    /// Returns at least all terms which are an instance of `query_term`
    /// A term `t` is an instance of a query term `s` iff there exists a substitution σ such that t = σ(s)
    /// Further filtering is required
    fn instances_of(&self, node_id: NodeId, to_check: &mut Vec<Term>, found: &mut Vec<Term>) {
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                assert!(to_check.is_empty()); // due to fixed_arity functions, we expect the path sizes to be equal
                found.extend_from_slice(terms.as_slice());
            }
            Node::Internal(map) => {
                let term = to_check.pop().expect("query path ended early");
                // we can def. match our own pattern
                if let Some(child) = map.get(&term.pattern()) {
                    // must check our subterms
                    for subterm in term.children() {
                        to_check.push(subterm.clone());
                    }
                    self.instances_of(*child, to_check, found);
                }
                // if we are a variable, we can match anything, but it consumes that subterm
                if term.is_variable() {
                    for (_, child) in map.iter() {
                        // the term IN THE TREE is consumed, so we skip to the node of the next terms (if any)
                        for next_node in &self.skip_to_next[*child] {
                            // must check query subterms
                            for subterm in term.children() {
                                to_check.push(subterm.clone());
                            }
                            self.instances_of(*next_node, to_check, found);
                        }
                    }
                }
            }
        }
    }
    /// Return an iterator with all references to clauses containing terms that unify with `term`
    pub fn unification_candidates(&self, query_term: Term) -> Vec<Term> {
        // collect candidates here
        let mut found = Vec::new();

        // find generalizations, i.e. we can map terms in the tree --> the query via a substitution
        let mut to_check = vec![query_term.clone()];
        self.generalizations_of(0 as NodeId, &mut to_check, &mut found);

        // find instances, i.e. we can map the query --> terms in the tree via a substitution
        let mut to_check = vec![query_term.clone()];
        self.instances_of(0 as NodeId, &mut to_check, &mut found);

        found.push(query_term); // the term itself, of course, should be included
        found
    }

}

impl fmt::Debug for TermPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermPattern::Variable => write!(f, "*")?,
            TermPattern::Function(fun_id) => write!(f, "{:?}", fun_id)?,
        }
        Ok(())
    }
}

impl Node {
    fn new() -> Node {
        Node::Internal( HashMap::new() )
    }
    fn get_or_insert(&mut self, num_nodes: NodeId, pattern: TermPattern) -> NodeId {
        if let Node::Internal(ref mut map) = self {
            let node_id = map
                .entry(pattern)
                .or_insert(num_nodes);
            *node_id
        } else {
            // since all functions are fixed arity, this *should* never happen
            unreachable!()
        }
    }
    fn leafify(&mut self, term: Term) {
        if let Node::Leaf(ref mut terms) = self {
            terms.push(term);
            return;
        }
        // must change to a leaf
        *self = Node::Leaf(vec![term]);
    }
}


/* TODO tests and benchmarks for TermTree

#[cfg(test)]
mod tests {
    use crate::prover::{TermTree, ClauseId};
    use super::{Node, TermPattern};
    use crate::ast::Term;
    use std::collections::HashMap;

    trait MapBuilder<K, V> {
        fn build(self, key: K, value: V) -> Self;
    }
    impl <K, V> MapBuilder<K, V> for HashMap<K, V>
        where K: std::cmp::Eq + std::hash::Hash
    {
        fn build(mut self, key: K, value: V) -> Self {
            self.insert(key, value);
            self
        }
    }
}

*/