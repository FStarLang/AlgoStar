module CLRS.Ch25.FloydWarshall.Paths

(**
 * Graph-theoretic shortest path formalism for Floyd-Warshall.
 *
 * Defines walks, walk weights, and restricted walks over an adjacency matrix.
 * Proves the base case: fw_entry at k=0 equals the direct-edge walk weight.
 * Proves any walk restricted to k=0 must be the direct edge.
 *
 * TODO: Complete the inductive step proving
 *   fw_entry adj n i j k == min walk weight over walks restricted to k
 * This would connect the FW recurrence to true δ(i,j) at k=n.
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
module Seq = FStar.Seq
open FStar.List.Tot
open CLRS.Ch25.FloydWarshall
open CLRS.Ch25.FloydWarshall.Spec

(* ========================================================================
   § 1. Walk Definitions
   ======================================================================== *)

// A walk is a list of vertices [v0; v1; ...; vp] with at least 2 elements.
let is_walk (w: list nat) : bool = length w >= 2

// Source and destination of a walk
let walk_src (w: list nat{is_walk w}) : nat = hd w
let walk_dst (w: list nat{is_walk w}) : nat = last w

// Weight of a walk: sum of edge weights along the walk.
// Returns inf for out-of-bounds accesses (invalid walk for the given graph).
let rec walk_weight (adj: Seq.seq int) (n: nat) (w: list nat) : Tot int (decreases w) =
  match w with
  | [] | [_] -> 0
  | u :: v :: rest -> 
    if u * n + v >= Seq.length adj then inf
    else Seq.index adj (u * n + v) + walk_weight adj n (v :: rest)

// All vertices in the walk are valid (< n)
let walk_valid (w: list nat) (n: nat) : bool =
  for_all #nat (fun (v:nat) -> v < n) w

// Intermediate vertices of a walk [v0; v1; ...; vp] are [v1; ...; v_{p-1}]
let intermediates (w: list nat) : Tot (list nat) =
  match w with
  | [] | [_] -> []
  | _ :: rest -> if Nil? rest then [] else init #nat rest

// A walk is restricted to level k if all intermediate vertices are < k
let walk_restricted (w: list nat) (k: nat) : bool =
  for_all #nat (fun (v:nat) -> v < k) (intermediates w)

// A walk is a valid walk from i to j restricted to level k
let valid_restricted_walk (adj: Seq.seq int) (n: nat) (i j: nat) (k: nat) (w: list nat) : prop =
  is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
  walk_restricted w k /\ Seq.length adj == n * n

(* ========================================================================
   § 2. Basic Walk Properties
   ======================================================================== *)

// The direct edge [i; j] is a valid walk restricted to any k
let lemma_direct_walk_valid (adj: Seq.seq int) (n: nat) (i j: nat) (k: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures valid_restricted_walk adj n i j k [i; j])
  = ()

// The weight of the direct edge walk [i; j] is adj[i*n+j]
let lemma_direct_walk_weight (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures walk_weight adj n [i; j] == Seq.index adj (i * n + j))
  = ()

(* ========================================================================
   § 3. Base Case: fw_entry at k=0
   ======================================================================== *)

// At k=0, fw_entry equals the direct edge weight, which equals the walk weight of [i; j]
let lemma_fw_entry_base (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures fw_entry adj n i j 0 == walk_weight adj n [i; j])
  = ()

// Any walk restricted to k=0 must be exactly [i; j] (no intermediates allowed)
let lemma_restricted_0_is_direct (w: list nat) (n: nat) (i j: nat)
  : Lemma (requires is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
                    walk_restricted w 0)
          (ensures w == [i; j])
  = match w with
    | [_; _] -> ()
    | _ :: b :: _ :: _ ->
      // b is an intermediate vertex, but walk_restricted w 0 requires all intermediates < 0
      // Since b : nat, b < 0 is impossible — contradiction
      assert (mem b (intermediates w));
      assert (b < 0)

// Corollary: at k=0, fw_entry is the unique restricted walk weight
let lemma_fw_entry_k0_is_shortest (adj: Seq.seq int) (n: nat) (i j: nat) (w: list nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n /\
                    valid_restricted_walk adj n i j 0 w)
          (ensures fw_entry adj n i j 0 == walk_weight adj n w)
  = lemma_restricted_0_is_direct w n i j;
    lemma_fw_entry_base adj n i j

(* ========================================================================
   § 4. Summary of What's Proven and What Remains
   ======================================================================== *)

// PROVEN:
// 1. Walk formalism: types, weights, restricted walks
// 2. Base case (k=0): fw_entry adj n i j 0 == walk_weight [i; j]
//    and [i; j] is the only walk restricted to k=0
//
// TODO (future work):
// 3. Inductive step: for k > 0, prove
//    fw_entry adj n i j k == min over all valid_restricted_walk adj n i j k w
//                              of walk_weight adj n w
//    This requires:
//    a. Walk decomposition: any walk through {0..k-1} that uses vertex k-1
//       can be split into two walks through {0..k-2}
//    b. Walk composition: two walks i→(k-1) and (k-1)→j through {0..k-2}
//       can be concatenated
//    c. Optimality: fw_entry selects the minimum of the two cases
//
// 4. Final theorem: fw_entry adj n i j n == shortest path distance δ(i,j)
//    (since at k=n, all vertices are available as intermediates)
