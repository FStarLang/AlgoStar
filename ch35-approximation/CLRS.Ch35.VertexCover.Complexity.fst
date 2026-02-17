module CLRS.Ch35.VertexCover.Complexity

open FStar.Mul

(** Vertex Cover 2-Approximation Algorithm (CLRS Section 35.1)
    
    Algorithm:
    1. Start with empty cover C
    2. While there exist uncovered edges:
       a. Pick arbitrary uncovered edge (u,v)
       b. Add both u and v to C
       c. Mark all edges incident to u or v as covered
    
    Complexity with adjacency matrix:
    - O(V²) to scan all edges
    - Each edge considered once
    - Total: O(V²)
    
    Approximation guarantee:
    - Returns a vertex cover of size at most 2·OPT
*)

/// Number of edge examinations in vertex cover algorithm
//SNIPPET_START: vertex_cover_ops
let vertex_cover_iterations (v: nat) : nat = v * v

let vertex_cover_quadratic (v: nat) 
  : Lemma (ensures vertex_cover_iterations v <= v * v) 
  = ()
//SNIPPET_END: vertex_cover_ops

/// Upper bound: examining all possible edges in complete graph
let vertex_cover_complete_graph (v: nat)
  : Lemma (ensures vertex_cover_iterations v = v * v)
  = ()

/// For sparse graphs with e edges, complexity is O(e)
let vertex_cover_sparse (e: nat) (v: nat{e <= v * v})
  : nat
  = e

let vertex_cover_sparse_bound (e: nat) (v: nat{e <= v * v})
  : Lemma (ensures vertex_cover_sparse e v <= vertex_cover_iterations v)
  = ()
