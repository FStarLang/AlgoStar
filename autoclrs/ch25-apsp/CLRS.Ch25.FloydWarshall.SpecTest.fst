module CLRS.Ch25.FloydWarshall.SpecTest

(**
 * Concrete output verification for the 3x3 Floyd-Warshall test case.
 * Uses fw_entry (the closed-form DP recurrence) which the SMT solver
 * can evaluate directly, then connects to fw_outer via the Spec theorem.
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec
open CLRS.Ch25.FloydWarshall.Lemmas

// 3x3 test adjacency matrix (row-major):
//     0   1   2
// 0 [ 0   5  inf ]
// 1 [ 50  0   15 ]
// 2 [ 30 inf  0  ]
let test_adj : seq int = seq_of_list [0; 5; 1000000; 50; 0; 15; 30; 1000000; 0]

// Expected shortest-path distances:
//     0   1   2
// 0 [ 0   5   20 ]
// 1 [ 45  0   15 ]
// 2 [ 30  35  0  ]

// Verify each entry of the FW recurrence at level n=3
#push-options "--fuel 8 --ifuel 2 --z3rlimit 10 --split_queries always"
let test_00 () : Lemma (fw_entry test_adj 3 0 0 3 == 0) = ()
let test_01 () : Lemma (fw_entry test_adj 3 0 1 3 == 5) = ()
let test_02 () : Lemma (fw_entry test_adj 3 0 2 3 == 20) = ()
let test_10 () : Lemma (fw_entry test_adj 3 1 0 3 == 45) = ()
let test_11 () : Lemma (fw_entry test_adj 3 1 1 3 == 0) = ()
let test_12 () : Lemma (fw_entry test_adj 3 1 2 3 == 15) = ()
let test_20 () : Lemma (fw_entry test_adj 3 2 0 3 == 30) = ()
let test_21 () : Lemma (fw_entry test_adj 3 2 1 3 == 35) = ()
let test_22 () : Lemma (fw_entry test_adj 3 2 2 3 == 0) = ()

// Non-negative diagonal at all levels (no negative cycles in test graph)
let test_no_neg_cycle () : Lemma (
    forall (k: nat) (v: nat). k <= 3 /\ v < 3 ==> fw_entry test_adj 3 v v k >= 0)
  = assert_norm (weights_bounded test_adj 3);
    let aux (k v: nat) : Lemma
      (requires k <= 3 /\ v < 3)
      (ensures fw_entry test_adj 3 v v k >= 0)
      = lemma_weights_bounded_nonneg_entry test_adj 3 v v k
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

// The main Spec theorem connects fw_entry to fw_outer:
//   index (fw_outer adj n 0) (qi*n+qj) == fw_entry adj n qi qj n
// Combined with the concrete fw_entry values above, this proves the
// imperative output matches the expected shortest-path distances.
let test_correctness (qi qj: nat) : Lemma
    (requires qi < 3 /\ qj < 3)
    (ensures index (fw_outer test_adj 3 0) (qi * 3 + qj) == fw_entry test_adj 3 qi qj 3)
  = test_no_neg_cycle ();
    floyd_warshall_computes_shortest_paths test_adj 3 qi qj

// Test: weights_bounded holds for the test adjacency matrix
let test_weights_bounded () : Lemma (weights_bounded test_adj 3)
  = assert_norm (weights_bounded test_adj 3)

// Test: floyd_warshall_full_correctness derives shortest paths from weights_bounded alone
let test_full_correctness (qi qj: nat) : Lemma
    (requires qi < 3 /\ qj < 3)
    (ensures index (fw_outer test_adj 3 0) (qi * 3 + qj) == fw_entry test_adj 3 qi qj 3)
  = floyd_warshall_full_correctness test_adj 3 qi qj

// Test: weights_bounded implies all fw_entry values are non-negative
let test_nonneg_entry () : Lemma (
    forall (i j: nat) (k: nat). i < 3 /\ j < 3 /\ k <= 3 ==>
      fw_entry test_adj 3 i j k >= 0)
  = let aux (i j k: nat) : Lemma
      (requires i < 3 /\ j < 3 /\ k <= 3)
      (ensures fw_entry test_adj 3 i j k >= 0)
    = lemma_weights_bounded_nonneg_entry test_adj 3 i j k
    in
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 aux)

#pop-options
