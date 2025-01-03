/// Specifies whether our graph is Directed or Undirected
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GraphType {
    Directed,
    Undirected,
}
/// A graph structure using an adjacency list.
/// Supports both Directed and Undirected graphs.
pub struct Graph {
    /// `adjacency_list[u]` holds all vertices adjacent to vertex `u`.
    adjacency_list: Vec<Vec<usize>>,
    graph_type: GraphType,
}

impl Graph {
    /// Creates a new graph with `n` vertices (0 to n-1) and no edges.
    /// You must specify whether the graph is directed or undirected.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    ///
    /// // Create a directed graph with 5 vertices
    /// let g_directed = Graph::new(5, GraphType::Directed);
    /// assert_eq!(g_directed.len(), 5);
    ///
    /// // Create an undirected graph with 5 vertices
    /// let g_undirected = Graph::new(5, GraphType::Undirected);
    /// assert_eq!(g_undirected.len(), 5);
    /// ```
    pub fn new(n: usize, graph_type: GraphType) -> Self {
        Graph {
            adjacency_list: vec![Vec::new(); n],
            graph_type,
        }
    }

    /// Returns the number of vertices in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// let g = Graph::new(5, GraphType::Undirected);
    /// assert_eq!(g.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.adjacency_list.len()
    }

    /// Adds an edge between vertices `u` and `v`.
    ///
    /// - If the graph is directed, the edge will go from `u` to `v`.
    /// - If the graph is undirected, the edge will be bidirectional.
    ///
    /// # Panics
    ///
    /// Panics if `u` or `v` is out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// let mut g_directed = Graph::new(3, GraphType::Directed);
    /// g_directed.add_edge(0, 1); // Edge: 0 -> 1
    /// let mut g_undirected = Graph::new(3, GraphType::Undirected);
    /// g_undirected.add_edge(0, 1);
    /// g_undirected.add_edge(1, 2);
    /// // Now 0 -- 1 -- 2
    /// ```
    pub fn add_edge(&mut self, u: usize, v: usize) {
        // Validate indices (optional, depending on how you handle errors)
        assert!(
            u < self.len() && v < self.len(),
            "Vertex index out of range"
        );

        // Always add v to u's adjacency list
        self.adjacency_list[u].push(v);

        // If undirected, also add u to v's adjacency list
        if self.graph_type == GraphType::Undirected {
            self.adjacency_list[v].push(u);
        }
    }

    /// Returns a slice of all neighbors of vertex `u`.
    ///
    /// # Panics
    ///
    /// Panics if `u` is out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// let mut g_directed = Graph::new(3, GraphType::Directed);
    /// g_directed.add_edge(0, 1);
    /// g_directed.add_edge(1, 2);
    /// g_directed.add_edge(0, 2);
    /// assert_eq!(g_directed.neighbors(0), &[1, 2]) ;
    /// assert_eq!(g_directed.neighbors(1), &[2, ]) ;
    /// assert_eq!(g_directed.neighbors(2), &[]) ;
    /// ```
    pub fn neighbors(&self, u: usize) -> &[usize] {
        assert!(u < self.len(), "Vertex index out of range");
        &self.adjacency_list[u]
    }

    /// Returns true if there is an edge from `u` to `v`.
    /// In an undirected graph, this also implies `v to `u`.
    ///
    /// # Panics
    ///
    /// Panics if `u` or `v` are out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// let mut g = Graph::new(3, GraphType::Directed);
    /// g.add_edge(0, 1);
    /// g.add_edge(1, 2);
    /// // 0 -> 1 -> 2
    /// assert!(g.has_edge(0, 1));
    /// assert!(!g.has_edge(1, 0));
    /// assert!(g.has_edge(1, 2));
    /// ```
    pub fn has_edge(&self, u: usize, v: usize) -> bool {
        assert!(
            u < self.len() && v < self.len(),
            "Vertex index out of range"
        );
        self.adjacency_list[u].contains(&v)
    }

    /// Removes the edge from `u` to `v`.
    /// If the graph is undirected, it also removes the edge from `v` to `u`.
    ///
    /// # Panics
    ///
    /// Panics if `u` or `v` are out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    ///
    /// // Create a directed graph
    /// let mut g_directed = Graph::new(3, GraphType::Directed);
    /// g_directed.add_edge(0, 1);
    /// g_directed.add_edge(1, 2);
    /// // 0 -> 1 -> 2
    /// g_directed.remove_edge(0, 1);
    /// // 0    1 -> 2
    /// assert_eq!(g_directed.neighbors(0), &[]);
    /// assert_eq!(g_directed.neighbors(1), &[2]);
    /// assert_eq!(g_directed.neighbors(2), &[]);
    ///
    /// // Create an undirected graph
    /// let mut g_undirected = Graph::new(3, GraphType::Undirected);
    /// g_undirected.add_edge(0, 1);
    /// g_undirected.add_edge(1, 2);
    /// // 0 -- 1 -- 2
    /// g_undirected.remove_edge(0, 1);
    /// // 0    1 -- 2
    /// assert_eq!(g_undirected.neighbors(0), &[]);
    /// assert_eq!(g_undirected.neighbors(1), &[2, ]);
    /// assert_eq!(g_undirected.neighbors(2), &[1, ]);
    pub fn remove_edge(&mut self, u: usize, v: usize) {
        assert!(
            u < self.len() && v < self.len(),
            "Vertex index out of range"
        );

        // Remove v from u's adjacency list
        if let Some(idx) = self.adjacency_list[u].iter().position(|&x| x == v) {
            self.adjacency_list[u].swap_remove(idx);
        }

        // If undirected, remove also u from v's adjacency list
        if self.graph_type == GraphType::Undirected {
            if let Some(idx) = self.adjacency_list[v].iter().position(|&x| x == u) {
                self.adjacency_list[v].swap_remove(idx);
            }
        }
    }

    /// Returns the degree of vertex `u` in an undirected graph.
    /// For a directed graph, returns the `out_degree`.
    ///
    /// # Panics
    ///
    /// Panics if `u` is out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// // Create an undirected graph
    /// let mut g_undirected = Graph::new(4, GraphType::Undirected);
    /// g_undirected.add_edge(0, 1);
    /// g_undirected.add_edge(1, 2);
    /// // 0 -- 1 -- 2   3
    /// assert_eq!(g_undirected.degree(0), 1);
    /// assert_eq!(g_undirected.degree(1), 2);
    /// assert_eq!(g_undirected.degree(3), 0);
    /// ```
    ///
    /// ```
    /// use graph_vec::{Graph, GraphType};
    /// // Create a directed graph
    /// let mut g_directed = Graph::new(3, GraphType::Directed);
    /// g_directed.add_edge(0, 1);
    /// g_directed.add_edge(2, 1);
    /// // 0 -> 1 <- 2
    /// assert_eq!(g_directed.degree(0), 1);
    /// assert_eq!(g_directed.degree(1), 0);
    /// assert_eq!(g_directed.degree(2), 1);
    /// ```
    pub fn degree(&self, u: usize) -> usize {
        assert!(u < self.len(), "Vertex index out of range");
        self.adjacency_list[u].len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_directed_graph() {
        let mut g = Graph::new(3, GraphType::Directed);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        // 0-> 1 -> 2

        // Check neighbors
        assert_eq!(g.neighbors(0), &[1]);
        assert_eq!(g.neighbors(1), &[2]);
        assert_eq!(g.neighbors(2), &[]);
    }

    #[test]
    fn test_undirected_graph() {
        let mut g = Graph::new(3, GraphType::Undirected);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        // 0 -- 1 -- 2

        // Check neighbors
        assert_eq!(g.neighbors(0), &[1]);
        assert_eq!(g.neighbors(1), &[0, 2]);
        assert_eq!(g.neighbors(2), &[1]);
    }
}
