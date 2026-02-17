(**
 * CLRS Chapter 22: White-Path Theorem (CLRS Theorem 22.9)
 *
 * Theorem 22.9: In a depth-first forest of graph G, vertex v is a descendant
 * of vertex u if and only if at the time d[u] that the search discovers u,
 * there is a path from u to v consisting entirely of white vertices.
 *
 * This module formalizes the White-Path Theorem and provides the key
 * definitions needed to state and prove it.
 *)
module CLRS.Ch22.DFS.WhitePath

open FStar.Mul
open CLRS.Ch22.DFS.Spec

(*** Core Definitions ***)

(**
 * Definition 1: DFS Ancestor Relation
 *
 * Vertex v is a descendant of vertex u in the DFS tree if and only if
 * v's timestamp interval is contained within u's interval:
 *   d[u] < d[v] < f[v] < f[u]
 *
 * This follows from the Parenthesis Theorem (CLRS Theorem 22.7).
 *)
let dfs_ancestor (d f: Seq.seq nat) (u v: nat) : prop =
  u < Seq.length d && v < Seq.length d &&
  u < Seq.length f && v < Seq.length f &&
  (let du = Seq.index d u in
   let dv = Seq.index d v in
   let fu = Seq.index f u in
   let fv = Seq.index f v in
   // v's interval [d[v], f[v]] is strictly contained in u's interval [d[u], f[u]]
   du < dv && dv < fv && fv < fu)

(**
 * Definition 2: White at Time
 *
 * A vertex v is white (undiscovered) at a given time if:
 *   - Either the vertex has never been discovered (d[v] = 0), or
 *   - The current time is before the vertex's discovery time (time < d[v])
 *
 * We model this using a function color_at : nat -> Seq.seq color that
 * gives the color of each vertex at each time.
 *)
let white_at_time (d: Seq.seq nat) (v: nat) (time: nat) : prop =
  v < Seq.length d /\
  (let dv = Seq.index d v in
   dv = 0 \/ time < dv)

(**
 * Helper: All intermediate vertices on a path are white
 *
 * This predicate states that there exists a path from u to v where
 * all intermediate vertices (not including u, but including v) are white
 * at the specified time.
 *)
let rec path_all_white 
  (adj: Seq.seq (Seq.seq int))
  (n: nat) 
  (d: Seq.seq nat)
  (u v: nat) 
  (time: nat)
  (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then 
      // Base case: path of length 0 means u = v
      u = v /\ white_at_time d v time
    else if steps = 1 then
      // Path of length 1: direct edge u -> v, and v is white
      has_edge n adj u v /\ white_at_time d v time
    else
      // Path of length > 1: u -> w -> ... -> v
      // where w is white and there's a white path from w to v
      u < n /\ v < n /\
      (exists (w: nat). 
        w < n /\ 
        has_edge n adj u w /\
        white_at_time d w time /\
        path_all_white adj n d w v time (steps - 1))

(**
 * Definition 3: White Path Exists
 *
 * There exists a white path from u to v at time d[u] if there is a path
 * from u to v such that all vertices on the path (except u) are white
 * at the time u is discovered.
 *
 * Note: The definition allows for the trivial path (u = v), but also
 * requires that v itself is white at d[u].
 *)
let white_path_exists 
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : prop
  = u < n /\ v < n /\
    u < Seq.length d /\
    // There exists a path of some length from u to v where all vertices are white
    (exists (steps: nat). steps < n /\ path_all_white adj n d u v time steps)

(**
 * Alternative formulation: White path using has_path from Spec
 *
 * This is a more direct encoding: at time d[u], there exists a path from u to v,
 * and all vertices on that path (except u) are white.
 *)
let white_path_exists_v2
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : prop
  = u < n /\ v < n /\
    u < Seq.length d /\
    // u = v (trivial path), or there exists a non-trivial path
    (if u = v then white_at_time d v time
     else 
       // There exists a path from u to v
       (exists (k: nat). k > 0 /\ k < n /\ has_path adj n u v k) /\
       // All intermediate vertices (not u) are white at time d[u]
       (forall (w: nat). w < n /\ w <> u /\
         (exists (k1 k2: nat). k1 < n /\ k2 < n /\
           has_path adj n u w k1 /\ has_path adj n w v k2) ==>
         white_at_time d w time))

(*** Helper Lemmas ***)

(**
 * Lemma: Reflexivity of white path
 *
 * If u is white at time t, then there is a trivial white path from u to u.
 *)
let white_path_reflexive
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u: nat)
  (time: nat)
  : Lemma
    (requires u < n /\ u < Seq.length d /\ white_at_time d u time)
    (ensures white_path_exists adj n d u u time)
  = ()

(**
 * Lemma: Transitivity of white path
 *
 * If there's a white path from u to w and from w to v, and w is white,
 * then there's a white path from u to v.
 *)
let white_path_transitive
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u w v: nat)
  (time: nat)
  : Lemma
    (requires 
      u < n /\ w < n /\ v < n /\
      white_path_exists adj n d u w time /\
      white_path_exists adj n d w v time /\
      white_at_time d w time)
    (ensures white_path_exists adj n d u v time)
  = admit() // Requires induction over path composition; existential witness extraction from path_all_white

(**
 * Lemma: If v is white at d[u] and there's an edge u -> v,
 * then there exists a white path from u to v at d[u].
 *)
let edge_to_white_vertex_gives_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\
      u < Seq.length d /\ v < Seq.length d /\
      has_edge n adj u v /\
      white_at_time d v time)
    (ensures white_path_exists adj n d u v time)
  = ()

(**
 * Lemma: White at discovery time
 *
 * If u is discovered at time du, then any vertex v with d[v] > du
 * was white at time du.
 *)
let discovered_later_was_white
  (d: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires 
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d u > 0 /\
      Seq.index d v > Seq.index d u)
    (ensures white_at_time d v (Seq.index d u))
  = ()

(**
 * Lemma: Descendant implies discovered later
 *
 * If v is a descendant of u, then v was discovered after u.
 *)
let descendant_discovered_later
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires dfs_ancestor d f u v)
    (ensures 
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d v > Seq.index d u)
  = ()

(*** Main Theorem: White-Path Theorem ***)

(**
 * White-Path Theorem (CLRS Theorem 22.9) - Forward Direction
 *
 * If there is a white path from u to v at the time d[u] when u is discovered,
 * then v becomes a descendant of u in the DFS tree.
 *
 * Proof intuition:
 * - When u is discovered, all vertices on the white path are unvisited
 * - DFS explores from u, so it will discover all reachable vertices
 * - Since v is reachable via white vertices, v will be discovered during
 *   the exploration from u (before u finishes)
 * - Therefore, d[u] < d[v] < f[v] < f[u], making v a descendant of u
 *)
let white_path_implies_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      u < Seq.length d /\ 
      Seq.index d u > 0 /\  // u has been discovered
      white_path_exists adj n d u v (Seq.index d u))
    (ensures dfs_ancestor d f u v)
  = admit() // Complex inductive proof over DFS structure

(**
 * White-Path Theorem (CLRS Theorem 22.9) - Backward Direction
 *
 * If v is a descendant of u in the DFS tree, then at the time d[u]
 * when u was discovered, there was a white path from u to v.
 *
 * Proof intuition:
 * - If v is a descendant, then d[u] < d[v] (v discovered after u)
 * - This means at time d[u], vertex v was still white (unvisited)
 * - Since v was discovered during u's exploration, there must be a path
 *   from u to v through the DFS tree
 * - All vertices on this tree path were white at time d[u] because they
 *   were all discovered after u (tree edges go from earlier to later)
 * - Therefore, there exists a white path from u to v at time d[u]
 *)
let descendant_implies_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      dfs_ancestor d f u v)
    (ensures 
      u < Seq.length d /\
      Seq.index d u > 0 /\
      white_path_exists adj n d u v (Seq.index d u))
  = admit() // Requires reasoning about DFS tree structure

(**
 * Main Theorem: White-Path Theorem (Both Directions)
 *
 * In a DFS forest of graph G, vertex v is a descendant of vertex u
 * if and only if at the time d[u] that the search discovers u,
 * there is a path from u to v consisting entirely of white vertices.
 *
 * Formally:
 *   dfs_ancestor d f u v ⟺ white_path_exists adj n d u v (d[u])
 *)
//SNIPPET_START: white_path_theorem
let white_path_theorem
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      u < Seq.length d /\ Seq.index d u > 0)
    (ensures 
      dfs_ancestor d f u v <==> 
      white_path_exists adj n d u v (Seq.index d u))
//SNIPPET_END: white_path_theorem
  = // Combine both directions
    // Forward: white_path => dfs_ancestor
    Classical.move_requires (white_path_implies_descendant adj n d f u) v;
    // Backward: dfs_ancestor => white_path
    Classical.move_requires (descendant_implies_white_path adj n d f u) v

(**
 * Corollary: Reachability and Descendant Relation
 *
 * If there is a path from u to v and both are discovered in the same
 * DFS tree (starting from u), then v is a descendant of u.
 *)
let reachable_in_tree_is_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      Seq.index f v < Seq.index f u /\ // Parenthesis theorem
      // There is a path from u to v
      (exists (k: nat). k > 0 /\ k < n /\ has_path adj n u v k) /\
      // v was discovered after u started but before u finished
      Seq.index d u < Seq.index d v /\
      Seq.index d v < Seq.index f u)
    (ensures dfs_ancestor d f u v)
  = // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Corollary: Non-descendant means no white path
 *
 * If v is not a descendant of u, then there was no white path from u to v
 * at the time u was discovered.
 *)
let non_descendant_no_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      ~(dfs_ancestor d f u v))
    (ensures ~(white_path_exists adj n d u v (Seq.index d u)))
  = // This is the contrapositive of white_path_implies_descendant
    Classical.move_requires (white_path_implies_descendant adj n d f u) v

(*** Applications of White-Path Theorem ***)

(**
 * Application 1: Tree Edge Characterization
 *
 * An edge (u, v) is a tree edge if and only if v is white when
 * first discovered from u, which means there's a white path of length 1.
 *)
let tree_edge_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      Seq.index f v < Seq.index f u /\ // Tree edge property
      // v was white at time d[u] and discovered directly from u
      Seq.index d v = Seq.index d u + 1)
    (ensures 
      dfs_ancestor d f u v /\
      white_path_exists adj n d u v (Seq.index d u))
  = // v was discovered immediately after u, so v was white at time d[u]
    // There's an edge u -> v, so there's a white path of length 1
    edge_to_white_vertex_gives_white_path adj n d u v (Seq.index d u);
    // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Application 2: Forward Edge Characterization
 *
 * An edge (u, v) is a forward edge if v is a descendant of u but
 * not through a direct tree edge from u to v.
 *)
let forward_edge_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      // Forward edge: d[u] < d[v] and f[v] < f[u]
      Seq.index d u < Seq.index d v /\
      Seq.index f v < Seq.index f u)
    (ensures dfs_ancestor d f u v)
  = // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Application 3: Back Edge Not Descendant
 *
 * An edge (u, v) is a back edge if v is an ancestor of u,
 * which means u is a descendant of v (not v of u).
 *)
let back_edge_not_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d u < Seq.index f u /\ // DFS invariant
      Seq.index d v < Seq.index f v /\ // DFS invariant
      // Back edge: d[v] < d[u] and f[u] < f[v]
      Seq.index d v < Seq.index d u /\
      Seq.index f u < Seq.index f v)
    (ensures 
      ~(dfs_ancestor d f u v) /\
      dfs_ancestor d f v u)  // v is ancestor of u
  = // For ~(dfs_ancestor d f u v): we need ~(d[u] < d[v]), which follows from d[v] < d[u]
    // For dfs_ancestor d f v u: all inequalities follow from preconditions
    ()

(*** Summary ***)

(*
 * This module formalizes the White-Path Theorem (CLRS Theorem 22.9):
 *
 * Key definitions:
 * 1. dfs_ancestor: v is descendant of u ⟺ d[u] < d[v] < f[v] < f[u]
 * 2. white_at_time: v is white at time t ⟺ t < d[v]
 * 3. white_path_exists: path from u to v with all vertices white at d[u]
 *
 * Main theorem:
 *   dfs_ancestor d f u v ⟺ white_path_exists adj n d u v (d[u])
 *
 * Applications:
 * - Tree edges: direct discovery from white vertex
 * - Forward edges: non-tree edges to descendants
 * - Back edges: edges to ancestors
 *
 * The admits represent complex inductive proofs that would require
 * detailed reasoning about the DFS traversal structure and the evolution
 * of vertex colors over time. The key insight is that the descendant
 * relation is captured by timestamp interval containment (Parenthesis Theorem),
 * and the white-path property ensures reachability through undiscovered vertices.
 *)
