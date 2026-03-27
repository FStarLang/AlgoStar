(*
   CLRS Chapter 23: Minimum Spanning Trees - Cut Property Theorem
   
   This module formalizes the key MST theorem (CLRS Theorem 23.1):
   For any cut (S, V-S) of a graph G, if (u,v) is a light edge crossing
   the cut that respects edge set A, then A ∪ {(u,v)} is safe for some MST.
*)

module CLRS.Ch23.MST.Spec

open FStar.List.Tot

(*** Basic Graph Definitions ***)

//SNIPPET_START: graph_defs
// Weighted edge: two vertices and a weight
noeq type edge = {
  u: nat;
  v: nat;
  w: int;
}

// A graph: n vertices (0 to n-1) and a list of edges
noeq type graph = {
  n: nat;  // number of vertices
  edges: list edge;
}
//SNIPPET_END: graph_defs

// Edge equality (ignoring direction for undirected graphs)
let edge_eq (e1 e2: edge) : bool =
  (e1.u = e2.u && e1.v = e2.v && e1.w = e2.w) ||
  (e1.u = e2.v && e1.v = e2.u && e1.w = e2.w)

// Edge equality is reflexive
val edge_eq_reflexive (e: edge) 
  : Lemma (edge_eq e e = true)

// Edge equality is symmetric
val edge_eq_symmetric (e1 e2: edge)
  : Lemma (edge_eq e1 e2 = edge_eq e2 e1)

// Check if edge is in edge set
let rec mem_edge (e: edge) (es: list edge) : bool =
  match es with
  | [] -> false
  | hd :: tl -> edge_eq e hd || mem_edge e tl

// An edge is in a list that starts with it
val mem_edge_hd (e: edge) (tl: list edge)
  : Lemma (mem_edge e (e :: tl) = true)

// Edge set subset
let rec subset_edges (a b: list edge) : bool =
  match a with
  | [] -> true
  | hd :: tl -> mem_edge hd b && subset_edges tl b

// Total weight of edge set
let rec total_weight (es: list edge) : int =
  match es with
  | [] -> 0
  | e :: rest -> e.w + total_weight rest

(*** Path and Reachability ***)

// A path is a list of edges where consecutive edges share endpoints
let rec is_path_from_to (edges: list edge) (start: nat) (finish: nat) : bool =
  match edges with
  | [] -> start = finish
  | e :: rest ->
    if e.u = start then is_path_from_to rest e.v finish
    else if e.v = start then is_path_from_to rest e.u finish
    else false

// Reachable via a set of edges
let reachable (es: list edge) (u v: nat) : prop =
  exists (path: list edge). 
    subset_edges path es /\ is_path_from_to path u v

// All vertices reachable from vertex 0
let all_connected (n: nat) (es: list edge) : prop =
  forall (v: nat). v < n ==> reachable es 0 v

(*** Cycles and Acyclicity ***)

// A cycle is a non-empty path from a vertex back to itself
// with at least one edge
let is_cycle (edges: list edge) (v: nat) : prop =
  Cons? edges /\ is_path_from_to edges v v

// No edge appears twice in a path (simple path/cycle)
let rec all_edges_distinct (path: list edge) : bool =
  match path with
  | [] -> true
  | hd :: tl -> not (mem_edge hd tl) && all_edges_distinct tl

// Acyclic: no vertex has a simple cycle (no repeated edges)
let acyclic (n: nat) (es: list edge) : prop =
  forall (v: nat) (cycle: list edge).
    v < n /\ subset_edges cycle es /\ Cons? cycle /\ all_edges_distinct cycle ==>
    ~(is_path_from_to cycle v v)

(*** Spanning Tree ***)

//SNIPPET_START: spanning_tree_mst
// A spanning tree: connects all vertices, acyclic, has exactly n-1 edges
let is_spanning_tree (g: graph) (es: list edge) : prop =
  g.n > 0 /\
  subset_edges es g.edges /\
  length es = g.n - 1 /\
  all_connected g.n es /\
  acyclic g.n es

(*** Minimum Spanning Tree ***)

// MST: spanning tree with minimum total weight
let is_mst (g: graph) (mst: list edge) : prop =
  is_spanning_tree g mst /\
  (forall (t: list edge). 
    is_spanning_tree g t ==> total_weight mst <= total_weight t)
//SNIPPET_END: spanning_tree_mst

(*** Cut Definitions ***)

// A cut S partitions vertices into S and V-S
// Represented as a predicate: vertex -> bool
type cut = nat -> bool

// An edge crosses the cut if endpoints are on different sides
let crosses_cut (e: edge) (s: cut) : bool =
  s e.u <> s e.v

// Filter edges that cross the cut
let rec crossing_edges (es: list edge) (s: cut) : list edge =
  match es with
  | [] -> []
  | e :: rest ->
    if crosses_cut e s then e :: crossing_edges rest s
    else crossing_edges rest s

//SNIPPET_START: cut_defs
// Light edge: minimum weight among edges crossing the cut
let is_light_edge (e: edge) (s: cut) (g: graph) : prop =
  mem_edge e g.edges /\
  crosses_cut e s /\
  (forall (e': edge). 
    mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w)

// A cut respects edge set A: no edge in A crosses the cut
let rec respects (a: list edge) (s: cut) : bool =
  match a with
  | [] -> true
  | e :: rest -> not (crosses_cut e s) && respects rest s
//SNIPPET_END: cut_defs

(*** Helper Lemmas ***)

// Basic facts about edge membership
val mem_edge_append (e: edge) (l1 l2: list edge)
  : Lemma (mem_edge e (l1 @ l2) <==> (mem_edge e l1 || mem_edge e l2))

val subset_edges_append (a b c: list edge)
  : Lemma (requires subset_edges a b)
          (ensures subset_edges a (b @ c))

val subset_edges_cons (a: list edge) (e: edge) (b: list edge)
  : Lemma (requires subset_edges a b)
          (ensures subset_edges a (e :: b))

val subset_edges_reflexive (a: list edge)
  : Lemma (subset_edges a a)

// If two edges are equal and one is in a list, so is the other
val mem_edge_eq (e1 e2: edge) (es: list edge)
  : Lemma (requires edge_eq e1 e2 /\ mem_edge e1 es)
          (ensures mem_edge e2 es)

// If an edge is in a, and a is subset of b, then edge is in b
val mem_edge_subset (e: edge) (a b: list edge)
  : Lemma (requires mem_edge e a /\ subset_edges a b)
          (ensures mem_edge e b)

val subset_edges_transitive (a b c: list edge)
  : Lemma (requires subset_edges a b /\ subset_edges b c)
          (ensures subset_edges a c)

(* Adding an edge to a set *)
let add_edge (e: edge) (es: list edge) : list edge =
  if mem_edge e es then es else e :: es

val mem_edge_add (e e': edge) (es: list edge)
  : Lemma (mem_edge e' (add_edge e es) <==> (edge_eq e e' || mem_edge e' es))

(*** Path Manipulation Helpers ***)

// Path concatenation: composing two paths
val path_concat (p1 p2: list edge) (a b c: nat)
  : Lemma (requires is_path_from_to p1 a b /\ is_path_from_to p2 b c)
          (ensures is_path_from_to (p1 @ p2) a c)

// Subset edges preserved under append (both subsets of s)
val subset_edges_append_both (a b: list edge) (s: list edge)
  : Lemma (requires subset_edges a s /\ subset_edges b s)
          (ensures subset_edges (a @ b) s)

// Subset edges preserved under snoc
val subset_edges_snoc (a: list edge) (e: edge) (s: list edge)
  : Lemma (requires subset_edges a s /\ mem_edge e s)
          (ensures subset_edges (a @ [e]) s)

// mem_edge is preserved by rev
val mem_edge_rev (e: edge) (path: list edge)
  : Lemma (ensures mem_edge e (rev path) = mem_edge e path)

// If all elements of l are in s, then subset_edges l s
val subset_from_mem (l: list edge) (s: list edge)
  : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e s)
          (ensures subset_edges l s)

// Subset edges preserved under reversal
val subset_edges_rev (path: list edge) (s: list edge)
  : Lemma (requires subset_edges path s)
          (ensures subset_edges (rev path) s)

// Path reversal for undirected graphs
val path_reverse (path: list edge) (a b: nat)
  : Lemma (requires is_path_from_to path a b)
          (ensures is_path_from_to (rev path) b a)

// Reachability is symmetric for undirected graphs
val reachable_symmetric (es: list edge) (u v: nat)
  : Lemma (requires reachable es u v)
          (ensures reachable es v u)

// Reachability is transitive
val reachable_transitive (es: list edge) (a b c: nat)
  : Lemma (requires reachable es a b /\ reachable es b c)
          (ensures reachable es a c)

// If a path subset of (e :: t) doesn't use e, it's a subset of t
val path_not_using_e_in_t (path: list edge) (e: edge) (t: list edge)
  : Lemma (requires subset_edges path (e :: t) /\ not (mem_edge e path))
          (ensures subset_edges path t)

// edge_eq is transitive
val edge_eq_transitive (e1 e2 e3: edge)
  : Lemma (requires edge_eq e1 e2 /\ edge_eq e2 e3)
          (ensures edge_eq e1 e3)

// edges that are edge_eq have same endpoints (as sets) and same weight
val edge_eq_endpoints (e1 e2: edge)
  : Lemma (requires edge_eq e1 e2)
          (ensures e1.w = e2.w /\
                   ((e1.u = e2.u /\ e1.v = e2.v) \/ (e1.u = e2.v /\ e1.v = e2.u)))

// edges that are edge_eq have the same crossing property
val edge_eq_crosses (e1 e2: edge) (s: cut)
  : Lemma (requires edge_eq e1 e2)
          (ensures crosses_cut e1 s = crosses_cut e2 s)

(*** Graph Theory Lemmas for Cut Property ***)

// Helper: all_edges_distinct is preserved for sublists
val all_edges_distinct_tail (hd: edge) (tl: list edge)
  : Lemma (requires all_edges_distinct (hd :: tl))
          (ensures all_edges_distinct tl /\ not (mem_edge hd tl))

// Helper: if edge_eq a b and ~(mem_edge b tl), then ~(mem_edge a tl)
val mem_edge_eq_neg (a b: edge) (tl: list edge)
  : Lemma (requires edge_eq a b /\ not (mem_edge b tl))
          (ensures not (mem_edge a tl))

// Split a simple path at the first occurrence of an edge matching e.
val split_at_first_e (path: list edge) (e: edge) (t: list edge) (start finish: nat)
  : Lemma (requires is_path_from_to path start finish /\
                    subset_edges path (e :: t) /\
                    mem_edge e path /\
                    all_edges_distinct path)
          (ensures (reachable t start e.u /\ reachable t e.v finish) \/
                   (reachable t start e.v /\ reachable t e.u finish))

// A simple cycle in (e :: t) must use e if t is acyclic
val cycle_must_use_e (n: nat) (t: list edge) (e: edge) (v: nat) (cycle: list edge)
  : Lemma (requires acyclic n t /\
                    v < n /\ subset_edges cycle (e :: t) /\ 
                    Cons? cycle /\ all_edges_distinct cycle /\
                    is_path_from_to cycle v v)
          (ensures mem_edge e cycle)

// If t is acyclic and e's endpoints are NOT connected in t, then e :: t is also acyclic
val acyclic_when_unreachable (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ e.u < n /\ e.v < n /\ ~(mem_edge e t) /\ ~(reachable t e.u e.v))
          (ensures acyclic n (e :: t))

// If adding edge e to acyclic graph creates a simple cycle,
// then e connects two previously connected components
val lemma_adding_edge_creates_cycle (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ 
                    e.u < n /\ e.v < n /\
                    ~(mem_edge e t) /\
                    ~(acyclic n (e :: t)))
          (ensures reachable t e.u e.v)

// A path from a to b where s(a) ≠ s(b) must contain a crossing edge
val path_crosses_when_sides_differ 
    (path: list edge) (es: list edge) (s: cut) (a b: nat)
  : Lemma (requires is_path_from_to path a b /\ subset_edges path es /\ s a <> s b)
          (ensures exists (e': edge). mem_edge e' path /\ mem_edge e' es /\ crosses_cut e' s)

// General version: a simple path using edge e with s(a)=s(b) must have a t-crossing
val find_t_crossing (path: list edge) (e: edge) (t: list edge) (s: cut) (a b: nat)
  : Lemma (requires is_path_from_to path a b /\
                    subset_edges path (e :: t) /\
                    mem_edge e path /\
                    all_edges_distinct path /\
                    Cons? path /\
                    crosses_cut e s /\
                    s a = s b)
          (ensures exists (e': edge). mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s)

// If adding edge (u,v) to tree T creates a cycle C,
// and (u,v) crosses cut S, then C contains another edge crossing S
val lemma_cycle_crosses_cut_twice 
    (n: nat) (t: list edge) (e: edge) (s: cut) (cycle: list edge)
  : Lemma (requires e.u < n /\ e.v < n /\
                    crosses_cut e s /\
                    subset_edges cycle (e :: t) /\
                    mem_edge e cycle /\
                    Cons? cycle /\
                    all_edges_distinct cycle /\
                    is_path_from_to cycle e.u e.u)
          (ensures (exists (e': edge). 
                     mem_edge e' cycle /\ 
                     mem_edge e' t /\ 
                     crosses_cut e' s))

(*** Weight Lemmas for Edge Exchange ***)

// Filtering out an edge: weight decomposition
val filter_weight_decomp (e_rem: edge) (t: list edge)
  : Lemma (ensures total_weight t = 
                   total_weight (filter (fun e -> not (edge_eq e e_rem)) t) +
                   total_weight (filter (fun e -> edge_eq e e_rem) t))

// All edges matching edge_eq have the same weight
val filter_matching_weight (e_rem: edge) (t: list edge)
  : Lemma (ensures (let c = length (filter (fun e -> edge_eq e e_rem) t) in
                    total_weight (filter (fun e -> edge_eq e e_rem) t) = op_Multiply c e_rem.w))

// If mem_edge e t, then filter keeps at least one match
val filter_match_nonempty (e_rem: edge) (t: list edge)
  : Lemma (requires mem_edge e_rem t)
          (ensures length (filter (fun e -> edge_eq e e_rem) t) >= 1)

// Filter only removes: length decreases
val filter_length_le (f: edge -> bool) (t: list edge)
  : Lemma (ensures length (filter f t) <= length t)

// Complementary filter lengths sum to original
val filter_complement_length (f: edge -> bool) (t: list edge)
  : Lemma (ensures length (filter f t) + length (filter (fun e -> not (f e)) t) = length t)

(*** Main Theorem: Cut Property (CLRS Theorem 23.1) ***)

val lemma_exchange_preserves_mst 
    (g: graph)
    (t: list edge)      // Original MST
    (e_add: edge)       // Edge to add (light edge crossing cut)
    (e_rem: edge)       // Edge to remove (from cycle)
  : Lemma (requires is_mst g t /\
                    mem_edge e_add g.edges /\
                    mem_edge e_rem t /\
                    e_add.w <= e_rem.w /\
                    ~(mem_edge e_add t) /\
                    is_spanning_tree g (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)))
          (ensures is_mst g (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)) \/
                   total_weight (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)) = 
                   total_weight t)

// Extract a simple path from any walk (for use with split_at_first_e)
val reachable_simple (es: list edge) (a b: nat)
  : Lemma (requires reachable es a b /\ a <> b)
          (ensures exists (path: list edge).
                    subset_edges path es /\ is_path_from_to path a b /\
                    all_edges_distinct path /\ Cons? path)

(*** Helpers for Cut Property Proof ***)

// Filtering preserves membership for non-matching edges
val mem_edge_filter_neg (x e_rem: edge) (t: list edge)
  : Lemma (requires mem_edge x t /\ not (edge_eq x e_rem))
          (ensures mem_edge x (filter (fun e -> not (edge_eq e e_rem)) t))

// If cut respects a and e_rem crosses cut, then a ⊆ (e_add :: filter (...) t)
val subset_edges_exchange (a: list edge) (e_add e_rem: edge) (t: list edge) (s: cut)
  : Lemma (requires subset_edges a t /\ respects a s /\ crosses_cut e_rem s)
          (ensures subset_edges a (e_add :: filter (fun e -> not (edge_eq e e_rem)) t))


val acyclic_subset (n: nat) (es es': list edge)
  : Lemma (requires acyclic n es /\ (forall (e:edge). mem_edge e es' ==> mem_edge e es))
          (ensures acyclic n es')

// Exchange preserves spanning tree
val exchange_is_spanning_tree
    (g: graph) (t: list edge) (e_add e_rem: edge) (path: list edge)
  : Lemma (requires is_spanning_tree g t /\
                    mem_edge e_add g.edges /\
                    mem_edge e_rem t /\
                    ~(mem_edge e_add t) /\
                    e_add.u < g.n /\ e_add.v < g.n /\ e_add.u <> e_add.v /\
                    e_rem.u < g.n /\ e_rem.v < g.n /\ e_rem.u <> e_rem.v /\
                    subset_edges path t /\
                    is_path_from_to path e_add.u e_add.v /\
                    mem_edge e_rem path /\
                    all_edges_distinct path)
          (ensures is_spanning_tree g (e_add :: filter (fun e -> not (edge_eq e e_rem)) t))

//SNIPPET_START: cut_property
// Main theorem: Cut Property
// If A ⊆ MST T, and (u,v) is light edge crossing cut respecting A,
// then A ∪ {(u,v)} ⊆ some MST
val cut_property:
  g: graph ->
  a: list edge ->  // Edge set A (subset of some MST)
  e: edge ->       // Light edge crossing cut
  s: cut ->        // The cut
  Lemma (requires 
          // Graph has at least one MST
          (exists (t: list edge). is_mst g t /\ subset_edges a t) /\
          // e is a light edge crossing the cut
          is_light_edge e s g /\
          // The cut respects A
          respects a s /\
          // Edge endpoints are valid vertices
          e.u < g.n /\ e.v < g.n /\
          // All graph edges have valid endpoints
          (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n))
        (ensures 
          // A ∪ {e} is contained in some MST
          (exists (t: list edge). is_mst g t /\ subset_edges (e :: a) t))
//SNIPPET_END: cut_property

(*** MST Existence Infrastructure ***)

// If endpoints of e are reachable in t, then e :: t is not acyclic
val reachable_implies_not_acyclic (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ reachable t e.u e.v /\
                    e.u < n /\ e.v < n /\ e.u <> e.v /\ ~(mem_edge e t))
          (ensures ~(acyclic n (e :: t)))

// Acyclic(e :: t) implies endpoints of e are NOT reachable in t
val acyclic_edge_disconnects (n: nat) (e: edge) (tl: list edge)
  : Lemma (requires acyclic n (e :: tl) /\ e.u < n /\ e.v < n /\ e.u <> e.v /\
                    ~(mem_edge e tl))
          (ensures ~(reachable tl e.u e.v))

// Acyclic + connected ⟹ exactly n-1 edges
val acyclic_connected_length (n: nat) (es: list edge)
  : Lemma (requires n > 0 /\ all_connected n es /\ acyclic n es /\ all_edges_distinct es /\
                    (forall (e: edge). mem_edge e es ==> e.u < n /\ e.v < n /\ e.u <> e.v))
          (ensures length es >= n - 1 /\ length es <= n - 1)