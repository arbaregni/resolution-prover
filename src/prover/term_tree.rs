use crate::ast::{Term, TermPattern};
use std::{fmt, iter, io};
use std::collections::{HashMap};
use indexmap::set::IndexSet;
use crate::error::BoxedErrorTrait;

/// Supports unification based lookup, using a discrimination tree
#[derive(Debug, PartialEq, Eq)]
pub struct TermTree {
    /// All nodes in the discrimination trie
    nodes: Vec<Node>,
    /// Maps ClauseId's to the nodes which begin the next term
    skip_to_next: Vec<IndexSet<NodeId>>,
}

/// `NodeId` are indices into `nodes` field of `TermMap`
type NodeId = usize;

#[derive(Debug, PartialEq, Eq)]
enum Node {
    Internal(HashMap<TermPattern, NodeId>),
    Leaf(IndexSet<Term>),
}

impl TermTree {
    /// create an empty term map
    pub fn new() -> TermTree {
        TermTree {
            nodes: vec![Node::new()],
            skip_to_next: vec![IndexSet::new()],
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
            self.skip_to_next.push(IndexSet::new());
        }
        for subterm in term.children() {
            next_id = self.create_path_at(next_id, subterm);
        }
        self.skip_to_next[node_id].insert(next_id);
        next_id
    }
    /// Converts the given node to a leaf variant, or updates it if already a leaf
    fn leafify(&mut self, leaf_id: NodeId, term: Term) {
        if let Node::Leaf(ref mut terms) = self.nodes[leaf_id] {
            terms.insert(term);
            return;
        }
        // must change to a leaf
        let mut terms = IndexSet::new();
        terms.insert(term);
        self.nodes[leaf_id] = Node::Leaf(terms);
        // the last node in our term's pattern sequence is the only node
        // self.skip_to_next[leaf_id].insert(leaf_id);
    }

    /// Updates the `TermMap` to include a new usage of `term`, creating an entry if it doesn't exist
    pub fn update(&mut self, term: Term) {
        // start the path at the root (node 0)
        let leaf_id = self.create_path_at(0 as NodeId, &term);
        // the last node in the path should point to a leaf containing the actual term
        self.leafify(leaf_id, term);
    }

    /// Returns at least all terms which are generalizations of `query_term`,
    /// A term `t` generalizes a query term `s` iff there exists a substitution σ such that σ(t) = s
    /// Further filtering is required
    fn generalizations_of(&self, node_id: NodeId, to_check: &mut Vec<Term>, found: &mut IndexSet<Term>) -> Result<(), BoxedErrorTrait> {
        // println!("generalizations of. looking at node_id {} ({:?}), to_check: {:?}", node_id, &self.nodes[node_id], to_check);
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                assert!(to_check.is_empty()); // due to fixed arity functions, we expect the path sizes to be equal
                // println!("finding: {:?}", terms);
                for t in terms {
                    found.insert(t.clone());
                }
            },
            Node::Internal(map) => {
                let term = match to_check.pop() {
                    Some(term) => term,
                    None => {
                        self.pretty_print(&mut io::stdout()).unwrap();
                        return internal_error!("query path ended early while generalizing with ^^^");
                    },
                };
                // we can def. match our own pattern if we are a function
                if term.is_function() {
                    if let Some(child) = map.get(&term.pattern()) {
                        // we must check the subterms
                        let mut to_check_with_children = to_check.clone();
                        // println!("checking constant branch ({:?}) of node {}", term.pattern(), node_id);
                        for subterm in term.children().iter().rev() {
                            to_check_with_children.push(subterm.clone());
                        }
                        self.generalizations_of(*child, &mut to_check_with_children, found)?;
                    }
                }
                // we can match any variable, but it consumes the current subterm and all its children
                if let Some(child) = map.get(&TermPattern::Variable) {
                    // we don't check the subterms
                    // println!("checking variable branch of node {}", node_id);
                    self.generalizations_of(*child, to_check, found)?;
                }
            },
        }
        Ok(())
    }
    /// Returns at least all terms which are an instance of `query_term`
    /// A term `t` is an instance of a query term `s` iff there exists a substitution σ such that t = σ(s)
    /// Further filtering is required
    fn instances_of(&self, node_id: NodeId, to_check: &mut Vec<Term>, found: &mut IndexSet<Term>) -> Result<(), BoxedErrorTrait>{
        match &self.nodes[node_id] {
            Node::Leaf(terms) => {
                assert!(to_check.is_empty()); // due to fixed_arity functions, we expect the path sizes to be equal
                for t in terms {
                    found.insert(t.clone());
                }
            }
            Node::Internal(map) => {
                let term = match to_check.pop() {
                    Some(term) => term,
                    None => {
                        return internal_error!("query path ended early on {:#?}", self)
                    },
                };
                // we can def. match our own pattern
                if let Some(child) = map.get(&term.pattern()) {
                    // must check our subterms
                    for subterm in term.children() {
                        to_check.push(subterm.clone());
                    }
                    self.instances_of(*child, to_check, found)?;
                }
                // if we are a variable, we can match anything, but it consumes that subterm
                if term.is_variable() {
                    for (_, child) in map.iter() {
                        // the term IN THE TREE is consumed, so we skip to the node of the next terms (if any)
                        if self.skip_to_next[*child].is_empty() {
                            self.instances_of(*child, to_check, found)?;
                        }
                        for next_node in &self.skip_to_next[*child] {
                            // must check query subterms
                            for subterm in term.children() {
                                to_check.push(subterm.clone());
                            }
                            self.instances_of(*next_node, to_check, found)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// Return an iterator with all references to clauses containing terms that unify with `term`
    pub fn unification_candidates(&self, query_term: Term) -> Result<IndexSet<Term>, BoxedErrorTrait> {
        // collect candidates here
        let mut found = IndexSet::new();

        // find generalizations, i.e. we can map terms in the tree --> the query via a substitution
        let mut to_check = vec![query_term.clone()];
        self.generalizations_of(0 as NodeId, &mut to_check, &mut found)?;

        // find instances, i.e. we can map the query --> terms in the tree via a substitution
        let mut to_check = vec![query_term.clone()];
        self.instances_of(0 as NodeId, &mut to_check, &mut found)?;

        found.insert(query_term); // the term itself, of course, should be included
        Ok(found)
    }

    /// Walk the tree, pretty-printing all the nodes (helpful when debugging)
    #[allow(dead_code)]
    pub fn pretty_print<Writer>(&self, w: &mut Writer) -> io::Result<()>
        where Writer: io::Write
    {
        self.pretty_print_node(w, 0, 0 as NodeId)?;
        writeln!(w, "skips: {:#?}", self.skip_to_next)?;
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

        // term_tree.pretty_print(&mut std::io::stdout()).unwrap();

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
        let forward = Term::predicate(path, vec![Term::variable(x), Term::variable(y)]);
        let reversed = Term::predicate(path, vec![Term::variable(y), Term::variable(x)]);
        let concrete = Term::predicate(path, vec![Term::atom(a), Term::atom(b)]);
        let concrete_rev = Term::predicate(path, vec![Term::atom(b), Term::atom(a)]);

        let term_tree = term_tree!(forward, reversed, concrete, concrete_rev);


        // term_tree.pretty_print(&mut std::io::stdout()).unwrap();

        let mut found = term_tree.unification_candidates(concrete.clone()).expect("should not error");
        found.sort();

        let mut expected = set![forward, reversed, concrete, concrete_rev];
        expected.sort();

        assert_eq!(found, expected);
    }

    #[test]
    fn unif_lookup_5() {
        symbols!(_symbols,
            VARIABLES: x, y
            FUNCTIONS: f, a
        );
        let f_x = Term::predicate(f, vec![Term::variable(x)]);
        let f_y = Term::predicate(f, vec![Term::variable(y)]);
        let f_a = Term::predicate(f, vec![Term::atom(a)]);

        let term_tree = term_tree!(f_x, f_y, f_a);

        let mut found = term_tree.unification_candidates(f_x.clone()).expect("should not error");
        found.sort();

        let mut expected = set![f_x, f_y, f_a];
        expected.sort();

        assert_eq!(found, expected);
    }

}