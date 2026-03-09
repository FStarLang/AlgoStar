(*
   Union-Find Correctness for Kruskal's Algorithm — Interface

   Exposes the pure union-find model and its key invariant (uf_inv),
   along with lemma signatures for:
   - Initialization: identity parent ⟹ uf_inv [] n 0
   - Union: adding an edge while updating parent preserves uf_inv
   - Soundness: find(u) ≠ find(v) ⟹ ¬(reachable edges u v)
   - Equivalence: uf_inv preserved under parent-value-equal arrays
*)
module CLRS.Ch23.Kruskal.UF

open FStar.List.Tot
open FStar.Seq
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.MST.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

(*** Core Definitions ***)

/// Parent array validity: length = n and all values < n
let valid_parents (sparent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) < n)

/// Pure find: chase parent pointers for at most `steps` hops
let rec find_pure (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Tot nat (decreases steps)
  = if steps = 0 || v >= n || Seq.length sparent <> n then v
    else find_pure sparent (SZ.v (Seq.index sparent v)) (steps - 1) n

/// UF invariant: relates parent array to edge-list connectivity
let uf_inv (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat) : prop =
  valid_parents sparent n /\ ec < n /\
  (forall (v: nat). v < n ==> find_pure sparent v n n < n) /\
  (forall (v: nat). v < n ==>
    SZ.v (Seq.index sparent (find_pure sparent v n n)) = find_pure sparent v n n) /\
  (forall (v: nat). v < n ==> find_pure sparent v ec n = find_pure sparent v n n) /\
  (forall (u v: nat). u < n /\ v < n /\ reachable edges u v ==>
    find_pure sparent u n n = find_pure sparent v n n)

/// Identity parent: parent[i] = i for all i < n
let identity_parent (n: nat) (sparent: Seq.seq SZ.t) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) = i)

/// All edges have endpoints within [0, n)
let all_edges_valid (edges: list edge) (n: nat) : prop =
  forall (e: edge). mem_edge e edges ==> e.u < n /\ e.v < n

(*** Lemmas ***)

/// find_pure always returns a value < n
val find_pure_bounded (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n)
          (ensures find_pure sparent v steps n < n)

/// find_pure at a fixed point returns the vertex itself
val find_pure_fixed (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n /\ SZ.v (Seq.index sparent v) = v)
          (ensures find_pure sparent v steps n = v)

/// find_pure splits: find(v, k1+k2) = find(find(v, k1), k2)
val find_pure_split (sparent: Seq.seq SZ.t) (v: nat) (k1 k2: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n)
          (ensures find_pure sparent v (k1 + k2) n =
                   find_pure sparent (find_pure sparent v k1 n) k2 n)

/// Soundness: different roots ⟹ not reachable
val uf_inv_unreachable (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u v: nat)
  : Lemma (requires uf_inv sparent edges n ec /\ u < n /\ v < n /\
                    find_pure sparent u n n <> find_pure sparent v n n)
          (ensures ~(reachable edges u v))

/// find_pure with identity parent returns the vertex
val find_pure_identity (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires identity_parent n sparent /\ v < n)
          (ensures find_pure sparent v steps n = v)

/// Identity parent establishes initial uf_inv
val uf_inv_init (sparent: Seq.seq SZ.t) (n: nat)
  : Lemma (requires identity_parent n sparent /\ n > 0)
          (ensures uf_inv sparent [] n 0)

/// Edge membership implies reachability
val mem_edge_reachable (e: edge) (edges: list edge)
  : Lemma (requires mem_edge e edges)
          (ensures reachable edges e.u e.v)

//SNIPPET_START: uf_inv_union
/// Union preserves uf_inv when adding an edge and setting parent[root_u] := root_v
val uf_inv_union
    (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u_val v_val: nat) (root_u root_v: nat) (new_edge: edge)
  : Lemma (requires uf_inv sparent edges n ec /\
                    u_val < n /\ v_val < n /\
                    root_u = find_pure sparent u_val n n /\
                    root_v = find_pure sparent v_val n n /\
                    root_u <> root_v /\
                    valid_parents sparent' n /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    new_edge.u = u_val /\ new_edge.v = v_val /\
                    ec + 1 < n /\
                    all_edges_valid edges n)
          (ensures uf_inv sparent' (new_edge :: edges) n (ec + 1))
//SNIPPET_END: uf_inv_union

/// Unreachable endpoints means edge not in list
val not_mem_when_unreachable (e: edge) (edges: list edge)
  : Lemma (requires ~(reachable edges e.u e.v))
          (ensures ~(mem_edge e edges))

/// Acyclicity is permutation-invariant (cons vs append)
val acyclic_cons_to_append (n: nat) (e: edge) (t: list edge)
  : Lemma (requires acyclic n (e :: t))
          (ensures acyclic n (t @ [e]))

/// uf_inv is permutation-invariant (cons vs append)
val uf_inv_cons_to_append (sparent: Seq.seq SZ.t) (e: edge) (t: list edge) (n ec: nat)
  : Lemma (requires uf_inv sparent (e :: t) n ec /\ all_edges_valid (e :: t) n)
          (ensures uf_inv sparent (t @ [e]) n ec)

/// Empty edge list is acyclic
val acyclic_empty (n: nat) : Lemma (acyclic n [])

/// find_pure agrees when parent values agree
val find_pure_eq (sparent sparent': Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires Seq.length sparent = n /\ Seq.length sparent' = n /\
                    (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) = SZ.v (Seq.index sparent' i)))
          (ensures find_pure sparent v steps n = find_pure sparent' v steps n)

/// uf_inv preserved when parent values are unchanged
val uf_inv_eq (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
  : Lemma (requires uf_inv sparent edges n ec /\ Seq.length sparent' = n /\
                    (forall (i: nat). i < n ==> SZ.v (Seq.index sparent' i) = SZ.v (Seq.index sparent i)))
          (ensures uf_inv sparent' edges n ec)
