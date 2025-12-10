//! Handles stratification of Datalog programs

use petgraph::{algo, graphmap::DiGraphMap};
use std::collections::{HashMap, HashSet};
use std::slice::Iter;
use syn::Ident;

pub struct Strata {
    list: Vec<Vec<Ident>>,
    index: HashMap<Ident, usize>,
}

impl Strata {
    pub fn new(relations: HashSet<Ident>, dependencies: HashSet<(&Ident, &Ident)>) -> Self {
        let mut graph = DiGraphMap::new();
        for ident in relations.iter() {
            graph.add_node(ident);
        }
        for edge in dependencies {
            graph.add_edge(edge.0, edge.1, ());
        }

        // Strongly connected components, as a vector of vectors of `&Ident`s.
        //
        // These are given in reverse topological order, which is our intended
        // order of evaluation (dependencies before dependents).
        let scc = algo::kosaraju_scc(&graph);

        let mut list = Vec::new();
        let mut index = HashMap::new();
        for (i, stratum) in scc.into_iter().enumerate() {
            let mut current = Vec::new();
            for ident in stratum {
                index.insert(ident.clone(), i);
                current.push(ident.clone());
            }
            list.push(current);
        }

        Self { list, index }
    }

    pub fn iter(&self) -> Iter<'_, Vec<Ident>> {
        self.list.iter()
    }

    pub fn find_relation(&self, rel: &Ident) -> usize {
        *self.index.get(rel).expect("key not found in stratum index")
    }
}
