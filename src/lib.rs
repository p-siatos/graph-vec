/// A simple undirected graph structure using an adjacency list.
pub struct Graph {
    /// `adjacency_list[u]` holds all vertices adjacent to vertex `u`.
    adjacency_list: Vec<Vec<usize>>,
}

impl Graph {
    /// Creates a new graph with `n` vertices (0 to n-1) and no edges.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::Graph;
    /// let g = Graph::new(5);
    /// assert_eq!(g.len(), 5);
    /// ```
    pub fn new(n: usize) -> Self {
        Graph {
            adjacency_list: vec![Vec::new(); n],
        }
    }

    /// Returns the number of vertices in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::Graph;
    /// let g = Graph::new(5);
    /// assert_eq!(g.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.adjacency_list.len()
    }

    /// Adds an undirected edge between vertices `u` and `v`
    ///
    /// If the graph already has an edge between `u` and `v`, it will be duplicated.
    ///
    /// # Panics
    ///
    /// Panics if `u` or `v` is out of bounds (>= the number of vertices).
    ///
    /// # Examples
    ///
    /// ```
    /// use graph_vec::Graph;
    /// let mut g = Graph::new(3);
    /// g.add_edge(0, 1);
    /// g.add_edge(1, 2);
    /// // Now 0 -- 1 -- 2
    /// ```
    pub fn add_edge(&mut self, u: usize, v: usize) {
        // Validate indices (optional, depending on how you handle errors)
        assert!(u < self.len() && v < self.len(), "Vertex index out of range");

        // Undirected graph: add `v` to `u`'s adjacency list, and `u` to `v`s adjacency list
        self.adjacency_list[u].push(v);
        self.adjacency_list[v].push(u);
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
    /// use graph_vec::Graph;
    /// let mut g = Graph::new(3);
    /// g.add_edge(0, 1);
    /// g.add_edge(0, 2);
    /// assert_eq!(g.neighbors(0), &[1, 2]) ;
    /// ```
    pub fn neighbors(&self, u: usize) -> &[usize] {
        assert!(u < self.len(), "Vertex index out of range");
        &self.adjacency_list[u]
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_graph_creation() {
        let g = Graph::new(5);
        assert_eq!(g.len(), 5);
        for i in 0..5 {
            assert!(g.neighbors(i).is_empty());
        }
    }

    #[test]
    fn test_add_edge() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);

        // Check neighbors
        assert_eq!(g.neighbors(0), &[1]);
        assert_eq!(g.neighbors(1), &[0, 2]);
        assert_eq!(g.neighbors(2), &[1]);
    }

}
