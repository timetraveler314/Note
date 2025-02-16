#import "@local/MetaNote:0.0.1" : *

= Graph Theory

== Hamilton Paths and Cycles

#theorem("Dirac's Theorem")[
  If a graph $G$ has $n$ vertices $(n >= 3)$ and the degree of each vertex is at least $n/2$, then $G$ has a Hamilton cycle.
]

#corollary[
  $
  forall (u,v) in.not E, deg(u) + deg(v) >= n => G "has a Hamilton cycle" => forall V_i subset V, p(G - V_i) <= |V_i|.
  $
]

#proof[
  (i) Assume for any non-adjacent vertices $u$ and $v$, $deg(u) + deg(v) >= n$. 

  We first show that $G$ is connected. Consider $u$ and $v$'s neighborhoods $N(u)$ and $N(v)$. If $N(u) and N(v)$ are disjoint, then $deg(u) + deg(v) >= n$ implies $|N(u)| + |N(v)| >= n$, a contradiction. Thus, $N(u) and N(v)$ must have a common vertex $w$. So either $(u,v)$ or $(u,w,v)$ is a path.

  Now we show that $G$ indeed has a Hamilton cycle. Consider the longest path $P$ in $G$. If $P$ is a cycle, we are done. Otherwise, let $u$ and $v$ be the endpoints of $P$. By the assumption, $deg(u) + deg(v) >= n$, so there must be a vertex $w$ adjacent to $u$ but not in $P$. Then $P + (u,w)$ is a longer path, a contradiction.
]

== Connectivity

#definition("Connectivity")[
  Vertex connectivity $kappa$: The minimum number of vertices that must be removed to disconnect a graph. The set of vertices whose removal disconnects the graph is called a vertex cut.

  Edge connectivity $lambda$: The minimum number of edges that must be removed to disconnect a graph.
]

#theorem("Whitney")[
  // Copilot says "A graph $G$ is $k$-connected if and only if for any two vertices $u$ and $v$, there are $k$ vertex-disjoint paths between them."
  Denote the minimum degree of $G$ as $delta$.
  $
  kappa <= lambda <= delta.
  $
]

#proofsk[
  (i) $kappa <= lambda$: Removing a vertex $v$ disconnects $u$ and $v$, so removing an edge incident to $v$ also disconnects $u$ and $v$.
  
  // By Menger's Theorem, the maximum number of vertex-disjoint paths between $u$ and $v$ is equal to the minimum number of vertices that must be removed to disconnect $u$ and $v$.

  (ii) $lambda <= delta$: // By Menger's Theorem, the maximum number of edge-disjoint paths between $u$ and $v$ is equal to the minimum number of edges that must be removed to disconnect $u$ and $v$.
]

== Directed Graphs

#definition("Strongly Connected")[
  A directed graph $G$ is strongly connected if for any two vertices $u$ and $v$, there is a directed path from $u$ to $v$ and a directed path from $v$ to $u$.
]

#theorem("Strong Connectivity")[
  A directed graph $G$ is strongly connected if and only if there exists a directed cycle containing all the vertices.
]

#definition("One-Way Connectivity")[
  A directed graph $G$ is one-way connected if for any two vertices $u$ and $v$, there is a directed path from $u$ to $v$ or a directed path from $v$ to $u$.
]

#theorem("One-Way Connectivity")[
  A directed graph $G$ is one-way connected if and only if there exists a directed path connecting all the vertices.
]

== Trees

=== Matrix Tree Theorem

#definition("Laplacian Matrix")[
  The Laplacian matrix $L$ of a graph $G$ is defined as $L = D - A$, where $D$ is the degree matrix and $A$ is the adjacency matrix.
]

#theorem("Matrix Tree Theorem")[
  The number of spanning trees of a graph $G$ is equal to any cofactor of the Laplacian matrix $L$.
]

Matrix tree theorem is a generalization of Cayley's formula, which states that the number of spanning trees of a complete graph $K_n$ is $n^(n-2)$.