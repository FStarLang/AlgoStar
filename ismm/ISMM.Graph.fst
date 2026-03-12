(**
 * ISMM: Graph Model, Reachability, and SCC Specification
 *
 * Paper: "Reference Counting Deeply Immutable Data Structures with Cycles"
 *        Parkinson, Clebsch, Wrigstad — ISMM '24
 *
 * Defines:
 *   - Graph representation (flat adjacency matrix, same as CLRS.Ch22)
 *   - k-step reachability
 *   - Reachability (existential over steps)
 *   - SCC equivalence relation
 *   - Predicates for freeze postconditions
 *)
module ISMM.Graph

open FStar.Mul
module Seq = FStar.Seq

(*** Graph Representation ***)

/// Edge predicate for flat adjacency matrix: adj[u*n+v] <> 0 means edge u → v.
let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

/// k-step reachability: source can reach dst in exactly `steps` hops.
let rec reachable_in (adj: Seq.seq int) (n: nat) (src dst: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then dst == src
    else exists (u: nat). u < n /\ reachable_in adj n src u (steps - 1) /\ has_edge adj n u dst

/// Reachability: there exist some number of steps from src to dst.
let reachable (adj: Seq.seq int) (n: nat) (src dst: nat) : prop =
  exists (k: nat). reachable_in adj n src dst k

(*** SCC Equivalence ***)

/// Two nodes are SCC-equivalent iff mutually reachable.
let scc_equiv (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  reachable adj n u v /\ reachable adj n v u

/// SCC equivalence is reflexive (0-step path).
let scc_equiv_refl (adj: Seq.seq int) (n: nat) (u: nat)
  : Lemma (requires u < n)
          (ensures scc_equiv adj n u u)
  = assert (reachable_in adj n u u 0);
    assert (reachable adj n u u)

(*** Freeze Postcondition Predicates ***)

/// After freeze: all nodes reachable from root are frozen (REP or RC).
let all_reachable_frozen
  (stag: Seq.seq int) (adj: Seq.seq int) (n: nat) (root: nat)
  : prop
  = n <= Seq.length stag /\
    (forall (v: nat). v < n /\ reachable adj n root v ==>
      (Seq.index stag v == 2 (* REP *) \/ Seq.index stag v == 3 (* RC *)))

/// After freeze: non-reachable nodes remain UNMARKED.
let unreachable_unchanged
  (stag: Seq.seq int) (adj: Seq.seq int) (n: nat) (root: nat)
  : prop
  = n <= Seq.length stag /\
    (forall (v: nat). v < n /\ ~(reachable adj n root v) ==>
      Seq.index stag v == 0 (* UNMARKED *))

(*** Arithmetic Helpers (for adjacency matrix indexing) ***)

let product_strict_bound (a b c d: nat)
  : Lemma (requires c < a /\ d < b)
          (ensures c * b + d < a * b)
  = ()
