use crate::ast::{Term, TermPattern};
use std::{fmt, iter, io};
use std::collections::{HashMap};
use indexmap::set::IndexSet;
use crate::error::BoxedErrorTrait;

/// Supports unification based lookup, using a discrimination tree
/// Example structure of a tree storing `P(f(a),$x)` and `P(f(c),b)`
/// ```       Node 0
///             +
///             | P
///             v
///           Node 1
///             +
///             | f
///             v
///           Node 2
///             +
///      +------+-----+
///    a |            | c
///      v            v
///    Node 3       Node 5
///      +            +
///    * |            | b
///      v            v
///    Node 4       Node 6
/// P(f(a),$x)     P(f(c),b)
/// ```
/// In this example, skips would be:
///  0 -> 4,6
///  1 -> 3,5
///  2 -> 3,5
///  3 -> 4
///  4 ->
///  5 -> 6
///  6 ->
#[derive(Debug, PartialEq, Eq)]
pub struct TermTree {
    /// All nodes in the discrimination trie, indexed into by `NodeId`s
    nodes: Vec<Node>,
    /// When an internal node is matched on, we want to skip to all of its "leaves"
    skips: Vec<IndexSet<NodeId>>,
}

/// `NodeId` are indices into `nodes` field of `TermMap`
type NodeId = usize;

#[derive(Debug, PartialEq, Eq)]
enum Node {
    /// Internal nodes have branches for different `TermPattern`s
    Internal(HashMap<TermPattern, NodeId>),
    /// Leaf nodes collect all the terms that inhabit this path
    Leaf(IndexSet<Term>),
}

/// A representation of terms as a string of `TermPattern`s
#[derive(Debug)]
pub struct PatternSequence {
    /// The sequence of term patterns representing a string
    /// For `P(f(a), $x)`, this will be `[P, f, a, $x]`
    seq: Vec<TermPattern>,
    /// The index after the current subterm ends
    /// For `P(f(a), $x)`, this will be `[4, 3, 3, 4]`
    /// Because `f(a)` (at index 2) ends just before index 3
    skips: Vec<usize>,
}

impl PatternSequence {
    pub fn from(term: &Term) -> PatternSequence {
        let mut seq = Vec::new();
        let mut skips = Vec::new();

        fn create(term: &Term, seq: &mut Vec<TermPattern>, skips: &mut Vec<usize>) {
            // construct the sequence:
            let our_idx = seq.len();
            seq.push(term.pattern());
            skips.push(0); // place holder
            for subterm in term.children() {
                create(subterm, seq, skips);
            }
            skips[our_idx] = seq.len();
        }
        create(term, &mut seq, &mut skips);
        PatternSequence { seq, skips }
    }
    pub fn get(&self, idx: usize) -> Option<&TermPattern> {
        self.seq.get(idx)
    }
    pub fn skip_over(&self, idx: usize) -> usize {
        self.skips[idx]
    }
}

impl TermTree {
    /// create an empty term map
    pub fn new() -> TermTree {
        TermTree {
            nodes: vec![Node::new()],
            skips: vec![IndexSet::new()],
        }
    }

    /// Inserts the sequence of patterns for `term` at `node_id`, returning the NodeId one after the last node in the pattern
    fn create_path_at(&mut self, node_id: NodeId, term: &Term) -> NodeId {
        // pass the current number of nodes in case we need to insert
        let num_nodes = self.nodes.len();
        let mut next_id = self.nodes[node_id].get_or_insert(num_nodes, term.pattern());
        if next_id == num_nodes {
            // inserting child
            self.nodes.push(Node::new());
            self.skips.push(IndexSet::new());
        }
        for subterm in term.children() {
            next_id = self.create_path_at(next_id, subterm);
        }
        self.skips[node_id].insert(next_id);
        next_id
    }

    /// Updates the `TermMap` to include a new usage of `term`, creating an entry if it doesn't exist
    pub fn update(&mut self, term: Term) {
        // start the path at the root (node 0)
        let leaf_id = self.create_path_at(0 as NodeId, &term);
        // the last node in the path should point to a leaf containing the actual term
        self.nodes[leaf_id].leafify(term);
    }

    /// Returns at least all terms which are generalizations of `query_term`,
    /// A term `t` generalizes a query term `s` iff there exists a substitution σ such that σ(t) = s
    fn generalizations_of(&self, node_id: NodeId, query_string: &PatternSequence, idx: usize, found: &mut IndexSet<Term>) -> Result<(), BoxedErrorTrait> {
        // println!("generalizations of. looking at node_id {} ({:?}), idx =  {}", node_id, &self.nodes[node_id], idx);
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                if query_string.get(idx).is_some() {
                    return internal_error!("query path continues past reaching leaf");
                }
                // everything in the leaf is a generalization of the query string
                // println!("  collecting in leaf {}", node_id);
                for t in terms {
                    found.insert(t.clone());
                }
            },
            Node::Internal(map) => {
                let term_pat = match query_string.get(idx) {
                    Some(term_pat) => term_pat,
                    None => {
                        // self.pretty_print(&mut io::stdout()).unwrap();
                        return internal_error!("query path ended early while generalizing with ^^^");
                    },
                };
                // we can match our own pattern
                if let Some(next_node) = map.get(term_pat) {
                    // println!("  matching `{:?}`, sending us to `{:?}`", term_pat, next_node);
                    self.generalizations_of(*next_node, query_string, idx + 1, found)?;
                }
                // we can match a variable (if we already are a variable, then we just did this)
                if term_pat.is_function() {
                    if let Some(next_node) = map.get(&TermPattern::Variable) {
                        // skip over the matched term in the query
                        let skipped = query_string.skip_over(idx);
                        // println!("  matching `{:?}`, sending us to `{:?}`, skipping over {:?} to {:?}", term_pat, next_node, idx, skipped);
                        self.generalizations_of(*next_node, query_string, skipped, found)?;
                    }
                }
            },
        }
        Ok(())
    }
    /// Returns instances of the term represented by `query_string`, starting at `idx`
    /// Returns `Ok(final_idx)` where `final_idx` is one index after where we stopped reading in query_string
    /// (A term `t` is an instance of a query term `s` iff there exists a substitution σ such that t = σ(s))
    fn instances_of(&self, node_id: NodeId, query_string: &PatternSequence, idx: usize, found: &mut IndexSet<Term>) -> Result<(), BoxedErrorTrait>{
        // println!("in instances of. looking at node id {} ({:?}), idx = {}", idx, &self.nodes[node_id], idx);
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                if query_string.get(idx).is_some() {
                    return internal_error!("query path continues past reaching a leaf")
                }
                // every thing contained in the leaf is an instance of the entire `query_string`
                // println!("  collecting in leaf {}", node_id);
                for t in terms {
                    found.insert(t.clone());
                }
            }
            Node::Internal(map) => {
                let term_pat = match query_string.get(idx) {
                    Some(t) => t,
                    None => {
                        return internal_error!("query path ended early on {:#?}", self)
                    },
                };
                if term_pat.is_variable() {
                    // a variable term can match anything
                    // println!("  variable matching everything...");
                    for next_node in self.skips[node_id].iter() {
                        self.instances_of(*next_node, query_string, idx + 1, found)?;
                    }
                } else {
                    // a constant term can only match itself
                    // println!("  matching {:?}", term_pat);
                    if let Some(next_node) = map.get(term_pat) {
                        self.instances_of(*next_node, query_string, idx + 1, found)?;
                    }
                }
            }
        }
        // println!("done. at node {}", node_id);
        Ok(())
    }
    /// Return an iterator with all references to clauses containing terms that unify with `term`
    pub fn unification_candidates(&self, query_term: Term) -> Result<IndexSet<Term>, BoxedErrorTrait> {
        // collect candidates here
        let mut found = IndexSet::new();
        // the string of term and subterm patterns in the query (i.e. the path to follow down the tree)
        let query_string = PatternSequence::from(&query_term);

        // find generalizations, i.e. we can map terms in the tree --> the query via a substitution
        self.generalizations_of(0 as NodeId, &query_string, 0, &mut found)?;

        // find instances, i.e. we can map the query --> terms in the tree via a substitution
        self.instances_of(0 as NodeId, &query_string, 0, &mut found)?;

        found.insert(query_term); // the term itself, of course, should be included
        Ok(found)
    }

    /// Walk the tree, pretty-printing all the nodes (helpful when debugging)
    #[allow(dead_code)]
    pub fn pretty_print<Writer>(&self, w: &mut Writer) -> io::Result<()>
        where Writer: io::Write
    {
        self.pretty_print_node(w, 0, 0 as NodeId)?;
        Ok(())
    }
    #[allow(dead_code)]
    fn pretty_print_node<Writer>(&self, w: &mut Writer, indent_depth: usize, node_id: NodeId) -> io::Result<()>
        where Writer: io::Write
    {
        let indent = iter::repeat(' ').take(indent_depth).collect::<String>();
        w.write_fmt(format_args!("Node {} {{\n", node_id))?;
        match &self.nodes[node_id] {
            Node::Internal(map) => {
                for (pat, child_id) in map.iter() {
                    w.write_fmt(format_args!("{}    {:?} => ", indent, pat))?;
                    self.pretty_print_node(w, indent_depth + 4, *child_id)?;
                }
            },
            Node::Leaf(bucket) => {
                for term in bucket.iter() {
                    w.write_fmt(format_args!("{}    {:?}\n", indent, term))?;
                }
            },
        }
        w.write_fmt(format_args!("{}}}\n", indent))?;
        Ok(())
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
            terms.insert(term);
            return;
        }
        // must change to a leaf
        let mut terms = IndexSet::new();
        terms.insert(term);
        *self = Node::Leaf(terms);
    }
}



#[cfg(test)]
mod tests {
    use crate::ast::Term;

    macro_rules! symbols {
        ($name:ident,
         VARIABLES: $( $var:ident ),*
         FUNCTIONS: $( $fun:ident ),*
        ) => {
                let mut $name = crate::ast::SymbolTable::new();
                // declare variables
                $(
                    let $var = $name.make_var();
                )*
                // declare functions
                $(
                    let $fun = $name.make_fun();
                )*
        }
    }

    macro_rules! term_tree {
        ($($term:expr),* $(,)*) => {
            {
                let mut term_tree = crate::prover::TermTree::new();
                $(
                    term_tree.update($term.clone());
                )*
                term_tree
            }
        }
    }

    macro_rules! set {
        ($($item:expr),* $(,)*) => {
            {
                let mut set = indexmap::set::IndexSet::new();
                $(
                    set.insert($item);
                )*
                set
            }
        }
    }

    #[test]
    fn unif_lookup_0() {
        symbols!(_symbols,
            VARIABLES: u, v, x, y
            FUNCTIONS: p, a, b, c, d
        );
        let left_general = Term::predicate(p, vec![Term::variable(u), Term::variable(v)]);
        let right_general = Term::predicate(p, vec![Term::variable(y), Term::variable(x)]);
        let left_witness = Term::predicate(p, vec![Term::atom(a), Term::atom(b)]);
        let right_witness = Term::predicate(p, vec![Term::atom(d), Term::atom(c)]);

        let term_tree = term_tree!(left_general, right_general, left_witness, right_witness);

        // term_tree.pretty_print(&mut io::stdout()).unwrap();

        let mut found = term_tree.unification_candidates(left_general.clone()).expect("should not error");
        found.sort();

        let mut expected = set![left_general, right_general, left_witness, right_witness];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_1() {
        symbols!(_symbols,
            VARIABLES: u, v, x, y
            FUNCTIONS: p, a, b, c, d
        );
        let left_general = Term::predicate(p, vec![Term::variable(u), Term::variable(v)]);
        let right_general = Term::predicate(p, vec![Term::variable(y), Term::variable(x)]);
        let left_witness = Term::predicate(p, vec![Term::atom(a), Term::atom(b)]);
        let right_witness = Term::predicate(p, vec![Term::atom(d), Term::atom(c)]);

        let term_tree = term_tree!(left_general, right_general, left_witness, right_witness);

        // term_tree.pretty_print(&mut io::stdout()).unwrap();

        let mut found = term_tree.unification_candidates(right_general.clone()).expect("should not error");
        found.sort();

        let mut expected = set![left_general, right_general, left_witness, right_witness];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_2() {
        symbols!(_symbols,
            VARIABLES: u, v, x, y
            FUNCTIONS: p, a, b, c, d
        );
        let left_general = Term::predicate(p, vec![Term::variable(u), Term::variable(v)]);
        let right_general = Term::predicate(p, vec![Term::variable(y), Term::variable(x)]);
        let left_witness = Term::predicate(p, vec![Term::atom(a), Term::atom(b)]);
        let right_witness = Term::predicate(p, vec![Term::atom(d), Term::atom(c)]);

        let term_tree = term_tree!(left_general, right_general, left_witness, right_witness);

        // term_tree.pretty_print(&mut io::stdout()).unwrap();

        let mut found = term_tree.unification_candidates(left_witness.clone()).expect("should not error");
        found.sort();

        let mut expected = set![left_general, right_general, left_witness];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_3() {
        symbols!(_symbols,
            VARIABLES: u, v, x, y
            FUNCTIONS: p, a, b, c, d
        );
        let left_general = Term::predicate(p, vec![Term::variable(u), Term::variable(v)]);
        let right_general = Term::predicate(p, vec![Term::variable(y), Term::variable(x)]);
        let left_witness = Term::predicate(p, vec![Term::atom(a), Term::atom(b)]);
        let right_witness = Term::predicate(p, vec![Term::atom(d), Term::atom(c)]);

        let term_tree = term_tree!(left_general, right_general, left_witness, right_witness);

        // term_tree.pretty_print(&mut io::stdout()).unwrap();

        let mut found = term_tree.unification_candidates(right_witness.clone()).expect("should not error");
        found.sort();

        let mut expected = set![left_general, right_general, right_witness];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_4() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: path, a, b
        );
        let forward = Term::predicate(path, vec![Term::variable(x), Term::variable(y)]);  // Path($x, $y)
        let reversed = Term::predicate(path, vec![Term::variable(y), Term::variable(x)]); // Path($y, $x)
        let concrete = Term::predicate(path, vec![Term::atom(a), Term::atom(b)]);        // Path(a, b)
        let concrete_rev = Term::predicate(path, vec![Term::atom(b), Term::atom(a)]);    // Path(b, a)

        let term_tree = term_tree!(forward, reversed, concrete, concrete_rev);

        let mut found = term_tree.unification_candidates(concrete.clone()).expect("should not error");
        found.sort();

        let mut expected = set![forward, reversed, concrete];
        expected.sort();

        // `Path(a, b)` can unify with `Path($x, $y)`, `Path($y, $x)` and `Path(a, b)`
        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_5() {
        symbols!(_symbols,
            VARIABLES: x
            FUNCTIONS: p, q, a
        );
        let p_x = Term::predicate(p, vec![Term::variable(x)]);
        let p_a = Term::predicate(p, vec![Term::atom(a)]);
        let q_x = Term::predicate(q, vec![Term::variable(x)]);
        let q_a = Term::predicate(q, vec![Term::atom(a)]);

        let term_tree = term_tree!(q_a, p_a, p_x, q_x);

        let mut found = term_tree.unification_candidates(p_x.clone()).expect("should not error");
        found.sort();

        let mut expected = set![p_x, p_a];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_6() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: p, q, f, a, b, c
        );
        // P(f(a), b)
        let p_f_a_b = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(a)]), Term::atom(b)]);
        // P(f(a), c)
        let p_f_c_a = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(c)]), Term::atom(b)]);
        // P($x, $y)
        let p_x_y = Term::predicate(p, vec![Term::variable(x), Term::variable(y)]);
        // Q($x)
        let q_x = Term::predicate(q, vec![Term::variable(x)]);
        // Q(a)
        let q_a = Term::predicate(q, vec![Term::atom(a)]);

        let term_tree = term_tree!(p_f_a_b, p_f_c_a, p_x_y, q_x, q_a);

        let mut found = term_tree.unification_candidates(p_x_y.clone()).expect("should not error");
        found.sort();

        let mut expected = set![p_x_y, p_f_a_b, p_f_c_a];
        expected.sort();

        // P($x, $y) unifies with P($x, $y), P(f(a), b), and P(f(c), b)
        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_7() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: p, q, f, a, b, c
        );
        // P(f(a), b)
        let p_f_a_b = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(a)]), Term::atom(b)]);
        // P(f(a), c)
        let p_f_c_a = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(c)]), Term::atom(b)]);
        // P($x, $y)
        let p_x_y = Term::predicate(p, vec![Term::variable(x), Term::variable(y)]);
        // Q($x)
        let q_x = Term::predicate(q, vec![Term::variable(x)]);
        // Q(a)
        let q_a = Term::predicate(q, vec![Term::atom(a)]);

        let term_tree = term_tree!(p_f_a_b, p_f_c_a, p_x_y, q_x, q_a);

        let mut found = term_tree.unification_candidates(p_f_c_a.clone()).expect("should not error");
        found.sort();

        let mut expected = set![p_x_y, p_f_c_a];
        expected.sort();

        // P($x, $y) unifies with P($x, $y), and P(f(c), b)
        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_8() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: p, q, f, a, b, c
        );
        // P(f(a), b)
        let p_f_a_b = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(a)]), Term::atom(b)]);
        // P(f(a), c)
        let p_f_c_a = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(c)]), Term::atom(b)]);
        // P($x, $y)
        let p_x_y = Term::predicate(p, vec![Term::variable(x), Term::variable(y)]);
        // Q($x)
        let q_x = Term::predicate(q, vec![Term::variable(x)]);
        // Q(a)
        let q_a = Term::predicate(q, vec![Term::atom(a)]);

        let term_tree = term_tree!(p_f_a_b, p_f_c_a, p_x_y, q_x, q_a);

        let mut found = term_tree.unification_candidates(q_x.clone()).expect("should not error");
        found.sort();

        let mut expected = set![q_x, q_a];
        expected.sort();

        // Q($x) unifies with Q($x) and Q(a)
        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_9() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: p, q, f, a, b, c
        );
        // P(f(a), b)
        let p_f_a_b = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(a)]), Term::atom(b)]);
        // P(f(a), c)
        let p_f_c_a = Term::predicate(p, vec![Term::predicate(f, vec![Term::atom(c)]), Term::atom(b)]);
        // P($x, $y)
        let p_x_y = Term::predicate(p, vec![Term::variable(x), Term::variable(y)]);
        // Q($x)
        let q_x = Term::predicate(q, vec![Term::variable(x)]);
        // Q(a)
        let q_a = Term::predicate(q, vec![Term::atom(a)]);

        let term_tree = term_tree!(p_f_a_b, p_f_c_a, p_x_y, q_x, q_a);

        let mut found = term_tree.unification_candidates(q_a.clone()).expect("should not error");
        found.sort();

        let mut expected = set![q_x, q_a];
        expected.sort();

        // Q(a) unifies with Q($x) and Q(a)
        assert_eq!(found, expected);
    }

}