module CLRS.Ch35.VertexCover.Spec

(**
 * Pure F* specification for APPROX-VERTEX-COVER (CLRS Chapter 35).
 *
 * Contains type definitions, graph predicates, counting functions,
 * and the minimum vertex cover specification. Lemmas and proofs
 * are in CLRS.Ch35.VertexCover.Lemmas.
 *)

open FStar.Mul
open FStar.List.Tot
open FStar.Seq

(*** Type definitions ***)

//SNIPPET_START: type_defs
type edge = nat & nat
type cover_fn = nat -> bool

let edge_uses_vertex (e: edge) (v: nat) : bool =
  let (u1, v1) = e in u1 = v || v1 = v

let edges_share_vertex (e1 e2: edge) : bool =
  let (u1, v1) = e1 in
  let (u2, v2) = e2 in
  u1 = u2 || u1 = v2 || v1 = u2 || v1 = v2

let rec pairwise_disjoint (m: list edge) : Type0 =
  match m with
  | [] -> True
  | e :: rest ->
      (forall (e': edge). memP e' rest ==> ~(edges_share_vertex e e')) /\
      pairwise_disjoint rest

let is_valid_cover_for_edges (c: cover_fn) (edges: list edge) : Type0 =
  forall (e: edge). memP e edges ==> (let (u, v) = e in c u \/ c v)

let rec count_cover (c: cover_fn) (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else (if c (n - 1) then 1 else 0) + count_cover c (n - 1)
//SNIPPET_END: type_defs

(*** Minimum vertex cover specification ***)

// Extract edges from adjacency matrix representation
// adj is a sequence of length n*n where adj[i*n+j] != 0 means edge (i,j) exists
// We only consider edges (u,v) where u < v to avoid counting each edge twice
let rec extract_edges (adj: seq int) (n: nat) (u v: nat) 
  : Tot (list edge) (decreases ((if u >= n then 0 else n - u) * (n + 1) + (if v > n then 0 else n + 1 - v))) =
  if u >= n then []
  else if v >= n then extract_edges adj n (u + 1) (u + 2)
  else if v > u && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0
       then (u, v) :: extract_edges adj n u (v + 1)
       else extract_edges adj n u (v + 1)

// A cover is valid for a graph if it covers all edges
let is_valid_graph_cover (adj: seq int) (n: nat) (c: cover_fn) : Type0 =
  let edges = extract_edges adj n 0 1 in
  is_valid_cover_for_edges c edges

//SNIPPET_START: min_vertex_cover
let is_minimum_vertex_cover (adj: seq int) (n: nat) (c_min: cover_fn) : Type0 =
  is_valid_graph_cover adj n c_min /\
  (forall (c': cover_fn). is_valid_graph_cover adj n c' ==>
    count_cover c_min n <= count_cover c' n)

let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn). 
    is_minimum_vertex_cover adj n c_min /\ 
    count_cover c_min n = opt
//SNIPPET_END: min_vertex_cover

(*** Auxiliary definitions used by lemmas ***)

let edge_contribution (c: cover_fn) (e: edge) : nat =
  let (u, v) = e in
  (if c u then 1 else 0) + (if c v then 1 else 0)

let rec sum_contributions (c: cover_fn) (m: list edge) : Tot nat (decreases m) =
  match m with
  | [] -> 0
  | e :: rest -> edge_contribution c e + sum_contributions c rest

(*** Connection definitions ***)

// Symmetry predicate: adjacency matrix represents an undirected graph
let is_symmetric_adj (s_adj: seq int) (n: nat) : prop =
  Seq.length s_adj == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    Seq.index s_adj (u * n + v) == Seq.index s_adj (v * n + u))

// The is_cover predicate used by the Pulse implementation.
// Tracks which edges have been processed so far via (bound_u, bound_v).
let is_cover (s_adj s_cover: seq int) (n: nat) (bound_u bound_v: nat) : prop =
  Seq.length s_adj == n * n /\
  Seq.length s_cover == n /\
  (forall (u v: nat). (u < bound_u \/ (u == bound_u /\ v < bound_v)) ==>
    u < n ==> v < n ==> u < v ==>
    Seq.index s_adj (u * n + v) <> 0 ==>
    (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0))

// Convert sequence to cover function (with bounds check)
let seq_to_cover_fn (s_cover: seq int) (n: nat{Seq.length s_cover = n}) : cover_fn =
  fun (i: nat) -> i < n && Seq.index s_cover i <> 0
