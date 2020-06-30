use crate::ast::{LiteralExpr, Substitution, LiteralKind};
use crate::prover::ClauseId;
use std::fmt;
use std::collections::{HashMap, VecDeque};

/// Maps literal expressions to clauses who use them.
/// Supports unification based lookup, using a trie
#[derive(Debug, PartialEq, Eq)]
pub struct TermMap<'a> {
    nodes: Vec<Node<'a>>,
}

/// Type def for indices into `nodes` field of `TermMap`
type NodeId = usize;

/// Nodes in the lookup trie are always associated with a TermPattern
/// Ex: `g($z, f($x, a))` is represented as the path:
///  g2 (the function g with 2 arguments)
///    [$z, g2] => [Leaf
#[derive(Debug, PartialEq, Eq)]
enum Node<'a> {
    /// Associated pattern is a non-constant function (arity > 0).
    /// Maps a number of patterns to corresponding nodes.
    Internal(HashMap<PatternSequence<'a>, NodeId>),
    /// Associated pattern is a constant function or variable.
    /// Stores all occurrences of the given path through the trie.
    Leaf(Vec<ClauseId>),
}

type PatternSequence<'a> = Vec<TermPattern<'a>>;

/// The highest level pattern of a term.
///   For instance,
/// `P(f(a, b, ...), g(h(i(...))))` is represented only
/// as a function named `P` with one argument (arity 1).
/// This is to enable unification based lookup
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum TermPattern<'a> {
    /// Representing a variable with the given name
    Variable(&'a str),
    /// Representing a function with the given name and arity
    Function(&'a str, usize),
}
impl <'a> TermPattern<'a> {
    /// gets the arity of a function, or zero for a variable
    fn arity(&self) -> usize {
        match self {
            TermPattern::Variable(_) => 0,
            TermPattern::Function(_, arity) => *arity,
        }
    }
}
impl <'a> LiteralExpr<'a> {
    fn pattern(&self) -> TermPattern<'a> {
       match self.kind() {
           LiteralKind::Variable(name) => TermPattern::Variable(name),
           LiteralKind::Function(name, args) => TermPattern::Function(name, args.len()),
       }
    }
    /// Gets the sequence of patterns for the entire expression, in a breadth-first manner
    fn pattern_sequence(&self) -> PatternSequence<'a> {
        let mut seq = Vec::new();
        let mut todo = VecDeque::new();
        todo.push_back(self);
        while let Some(term) = todo.pop_front() {
            seq.push(term.pattern());
            if let LiteralKind::Function(_, args) = term.kind() {
                for a in args {
                    todo.push_back(a);
                }
            }
        }
        println!("built seq: {:?} for {:#?}", seq, self);
        seq
    }
}
impl <'a> TermMap<'a> {
    /// create an empty term map
    pub fn new() -> TermMap<'a> {
        let root = Node::Internal(HashMap::new());
        TermMap {
            nodes: vec![root]
        }
    }
    /// Updates the `TermMap` to include a new usage of `term`, creating an entry if it doesn't exist
    /// Expects to be called with increasing `clause_id`s
    pub fn update(&mut self, term: &LiteralExpr<'a>, clause_id: ClauseId) {
        // first off, get all the patterns that we will need to lookup/insert
        let seq = term.pattern_sequence();
        // iterate over slices of the pattern sequence as far as we can into the trie
        // at the end of the loop, we will have to insert `clause_id` into `node`
        let mut idx = 0; // start at the beginning of the pattern sequence
        let mut expand_by = 1;
        let mut node_id = 0; // start at the root node
        while let Node::Internal(map) = &mut self.nodes[node_id] {
            // internal => we must lookup the next slice of patterns
            let slice = &seq[idx..idx+expand_by];
            if let Some(next_node) = map.get(slice) {
                // next iteration, inspect the new node
                node_id = *next_node;
                // the slice of patterns shifts forward
                idx += expand_by;
                /*
                    next iteration, we want to inspect all arguments of functions invoked in the last slice
                    as such, we want to expand by their total arity
                    for instance:
                    g^2 h^1 h^1 a^0 $x
                    ^-----^ current slice
                    1 + 1 = 2, so the next slice should be:
                    g^2 h^1 h^1 a^0 $x
                    ^----^ next slice
                */
                expand_by = slice.iter().map(TermPattern::arity).sum();
            } else {
                break; // not found: we traversed as far as we could
            }
        };
        // time to insert into `node`
        println!("inserting into [{}]: {:#?}", node_id, &self.nodes[node_id]);
        loop {
            let slice = &seq[idx..idx+expand_by];
            let remaining = &seq[idx+expand_by..];

            let child_id = self.nodes.len(); // will be the id of the child when we push it into the vector;
            let child = match &mut self.nodes[node_id] {
                // if we've found a leaf, we should be at the end of the path, and we can insert into the occurrences vector
                Node::Leaf(occurrences) => {
                    assert!(remaining.is_empty());
                    occurrences.push(clause_id); // clause_id should be greater than or equal to every previous ClauseId
                    occurrences.dedup(); // since it's sorted, this should remove duplicates
                    return;
                },
                // otherwise, we have to insert the relevant segment and keep looping
                Node::Internal(map) => {
                    map.insert(slice.to_vec(), child_id);
                    if remaining.is_empty() {
                        // nothing more in the path: next node is the last one
                        Node::Leaf(Vec::with_capacity(1))
                    } else {
                        // more in the path
                        Node::Internal(HashMap::with_capacity(1))
                    }
                },
            };
            self.nodes.push(child);
            // update our loop variables
            node_id = child_id;
            idx += expand_by;
            expand_by = slice.iter().map(TermPattern::arity).sum();
        }
    }
    /// Return an iterator with all references to clauses containing terms that unify with `term`
    pub fn unifies_with<'s>(&'s self, term: &'s LiteralExpr<'a>) -> Vec<(&'s Vec<ClauseId>, Substitution<'a>)> {
        unimplemented!()
        /* self.buckets
            .iter()
            .filter_map(move |(elem, value)| {
                if let Some(sub) = term.unify(elem) {
                    Some((value, sub))
                } else {
                    None
                }
            })

         */
    }
}


impl fmt::Debug for TermPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermPattern::Variable(name) => write!(f, "${}", name)?,
            TermPattern::Function(name, arity) => write!(f, "{}^{}", name, arity)?,
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::prover::{TermMap, ClauseId};
    use super::{Node, TermPattern};
    use crate::ast::LiteralExpr;
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

    #[test]
    fn term_map_insert_0() {
        let mut term_map = TermMap::new();
        // insert g(a, f($x, $y)) = g^2 a^0 f^2 $x $y
        // slices: [g^2] [a^0 f^2] [$x $y]
        term_map.update(&LiteralExpr::predicate("g", vec![
            LiteralExpr::atom("a"),
            LiteralExpr::predicate("f", vec![
                LiteralExpr::variable("x"),
                LiteralExpr::variable("y"),
            ])
        ]), ClauseId(0));
        println!("{:#?}", term_map);
        assert_eq!(term_map, TermMap {
            nodes: vec![
                Node::Internal(HashMap::new()
                    .build(vec![TermPattern::Function("g", 2)], 1)
                ),
                Node::Internal(HashMap::new()
                    .build(vec![TermPattern::Function("a", 0), TermPattern::Function("f", 2)], 2)
                ),
                Node::Internal(HashMap::new()
                    .build(vec![TermPattern::Variable("x"), TermPattern::Variable("y")], 3)
                ),
                Node::Leaf(vec![ClauseId(0)]),
            ]
        });

        // insert g(a, f(f($x), $z)) = `g^2 a^0 f^2 f^1 $z $x`
        // slices: [g^2] [a^0 f^2] [f^1 $z] [$x]
        term_map.update(&LiteralExpr::predicate("g", vec![
            LiteralExpr::atom("a"),
            LiteralExpr::predicate("f", vec![
                LiteralExpr::predicate("f", vec![
                    LiteralExpr::variable("x")
                ]),
                LiteralExpr::variable("z")
            ])
        ]), ClauseId(1));
        println!("==============================\n{:#?}", term_map);
        assert_eq!(term_map, TermMap {
            nodes: vec![
                Node::Internal(HashMap::new()  // 0
                    .build(vec![TermPattern::Function("g", 2)], 1)
                ),
                Node::Internal(HashMap::new()  // 1
                    .build(vec![TermPattern::Function("a", 0), TermPattern::Function("f", 2)], 2)
                ),
                Node::Internal(HashMap::new() // 2
                    .build(vec![TermPattern::Variable("x"), TermPattern::Variable("y")], 3)
                    .build(vec![TermPattern::Function("f", 1), TermPattern::Variable("z")], 4)
                ),
                Node::Leaf(vec![ClauseId(0)]), // 3
                Node::Internal(HashMap::new()  // 4
                    .build(vec![TermPattern::Variable("x")], 5)
                ),
                Node::Leaf(vec![ClauseId(1)]), // 5
            ]
        });

        // insert another copy of g(a, f($x, $y)) to make sure the leaf is updated
        // slices: [g^2] [a^0 f^2] [$x $y]
        term_map.update(&LiteralExpr::predicate("g", vec![
            LiteralExpr::atom("a"),
            LiteralExpr::predicate("f", vec![
                LiteralExpr::variable("x"),
                LiteralExpr::variable("y"),
            ])
        ]), ClauseId(2));
        println!("==============================\n{:#?}", term_map);
        assert_eq!(term_map, TermMap {
            nodes: vec![
                Node::Internal(HashMap::new()  // 0
                    .build(vec![TermPattern::Function("g", 2)], 1)
                ),
                Node::Internal(HashMap::new()  // 1
                    .build(vec![TermPattern::Function("a", 0), TermPattern::Function("f", 2)], 2)
                ),
                Node::Internal(HashMap::new() // 2
                    .build(vec![TermPattern::Variable("x"), TermPattern::Variable("y")], 3)
                    .build(vec![TermPattern::Function("f", 1), TermPattern::Variable("z")], 4)
                ),
                Node::Leaf(vec![ClauseId(0), ClauseId(2)]), // 3
                Node::Internal(HashMap::new()  // 4
                    .build(vec![TermPattern::Variable("x")], 5)
                ),
                Node::Leaf(vec![ClauseId(1)]), // 5
            ]
        });

        // insert yet another copy of g(a, f($x, $y)) to make sure the leaf ignores the duplicate
        // slices: [g^2] [a^0 f^2] [$x $y]
        term_map.update(&LiteralExpr::predicate("g", vec![
            LiteralExpr::atom("a"),
            LiteralExpr::predicate("f", vec![
                LiteralExpr::variable("x"),
                LiteralExpr::variable("y"),
            ])
        ]), ClauseId(2));
        println!("==============================\n{:#?}", term_map);
        assert_eq!(term_map, TermMap {
            nodes: vec![
                Node::Internal(HashMap::new()  // 0
                    .build(vec![TermPattern::Function("g", 2)], 1)
                ),
                Node::Internal(HashMap::new()  // 1
                    .build(vec![TermPattern::Function("a", 0), TermPattern::Function("f", 2)], 2)
                ),
                Node::Internal(HashMap::new() // 2
                    .build(vec![TermPattern::Variable("x"), TermPattern::Variable("y")], 3)
                    .build(vec![TermPattern::Function("f", 1), TermPattern::Variable("z")], 4)
                ),
                Node::Leaf(vec![ClauseId(0), ClauseId(2)]), // 3
                Node::Internal(HashMap::new()  // 4
                    .build(vec![TermPattern::Variable("x")], 5)
                ),
                Node::Leaf(vec![ClauseId(1)]), // 5
            ]
        });
    }
}
