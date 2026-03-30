(*
   CLRS Chapter 7: Partition — Spec Validation Test

   Tests that the partition API's postcondition (ownership split,
   bounds, strict ordering, permutation, exact complexity) is
   satisfiable and meaningful for a concrete 3-element input [3; 1; 2].

   The partition spec is intentionally relational: it does not prescribe
   which element becomes the pivot. The Lomuto implementation uses the
   last element, but the Impl.fsti postcondition does not expose this.
   This test verifies that the postcondition constrains the output
   sufficiently despite this degree of freedom.
*)
module CLRS.Ch07.Partition.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch07.Partition.Impl
open CLRS.Ch07.Partition.Lemmas
open CLRS.Common.SortSpec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module GR = Pulse.Lib.GhostReference
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SS = CLRS.Common.SortSpec

(* Runtime comparison helpers that survive KaRaMeL extraction to C.
   Use Prims operators directly to avoid BoundedIntegers typeclass dispatch
   which KaRaMeL cannot extract. *)
inline_for_extraction
let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b

inline_for_extraction
let int_leq (a b: int) : (r:bool{r <==> Prims.op_LessThanOrEqual a b}) =
  Prims.op_LessThanOrEqual a b

// Test file: concrete 3-element reasoning needs fuel for count/permutation unfolding.
// split_queries helps Z3 handle count facts independently.
#push-options "--fuel 4 --z3rlimit 20 --split_queries always"

(* Lemma: for input [3; 1; 2], the partition postcondition determines
   that the three sub-sequences form a valid split of exactly these elements.
   From permutation s0 (s1 ++ s_pivot ++ s2) with bounds constraints,
   we derive:
   - Total length is preserved
   - All output elements are within the input bounds [1, 3]
   - The partition ordering invariant constrains element placement:
     left elements ≤ pivot, right elements > pivot
   - For each possible pivot value, the sub-array sizes are forced
*)
let partition_permutation_valid
  (s1 s_pivot s2: Seq.seq int)
  (pivot: int)
  : Lemma
    (requires
      Seq.length s_pivot == 1 /\
      Seq.index s_pivot 0 == pivot /\
      1 <= pivot /\ pivot <= 3 /\
      between_bounds s1 1 pivot /\
      strictly_larger_than s2 pivot /\
      between_bounds s2 pivot 3 /\
      SP.permutation int (Seq.seq_of_list [3; 1; 2])
                         (Seq.append s1 (Seq.append s_pivot s2)))
    (ensures
      Seq.length s1 + 1 + Seq.length s2 == 3 /\
      // All left elements are within [1, pivot]
      (forall (k:nat). k < Seq.length s1 ==> 1 <= Seq.index s1 k /\ Seq.index s1 k <= pivot) /\
      // All right elements are within (pivot, 3]
      (forall (k:nat). k < Seq.length s2 ==> pivot < Seq.index s2 k /\ Seq.index s2 k <= 3) /\
      // Pivot value constrains sub-array sizes:
      // pivot=1 => |s1|=0, pivot=2 => |s1|=1, pivot=3 => |s1|=2
      (pivot == 1 ==> Seq.length s1 == 0 /\ Seq.length s2 == 2) /\
      (pivot == 2 ==> Seq.length s1 == 1 /\ Seq.length s2 == 1) /\
      (pivot == 3 ==> Seq.length s1 == 2 /\ Seq.length s2 == 0))
= SP.perm_len (Seq.seq_of_list [3; 1; 2])
              (Seq.append s1 (Seq.append s_pivot s2));
  // Count-based reasoning: the permutation preserves element counts
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0)

(* Completeness: calling partition proves satisfiability;
   postcondition constraints are verified in-line.
   Runtime checks verify the partition property survives extraction. *)
```pulse
fn test_partition_3 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  // Bind input ghost
  with s0. assert (A.pts_to arr s0);

  // Convert pts_to -> pts_to_range for partition API
  A.pts_to_range_intro arr 1.0R s0;

  // Create ghost counter (starts at 0)
  let ctr = GR.alloc #nat 0;

  // Call partition: lo=0, hi=3, bounds [1, 3]
  let p = clrs_partition_wrapper_with_ticks arr 0 3 (hide 1) (hide 3) ctr #(hide 0);

  // Bind existential witnesses from postcondition
  with s1. assert (A.pts_to_range arr 0 p s1);
  with s_pivot. assert (A.pts_to_range arr p (p+1) s_pivot);
  with s2. assert (A.pts_to_range arr (p+1) 3 s2);
  with cf. assert (GR.pts_to ctr cf);

  // === Verify postcondition properties ===

  // 1. Pivot index is in range
  assert (pure (0 <= p /\ p < 3));

  // 2. Sub-array lengths are consistent
  assert (pure (Seq.length s1 == p /\ Seq.length s_pivot == 1 /\ Seq.length s2 == 2 - p));

  // 3. Pivot value is within bounds [1, 3]
  assert (pure (1 <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= 3));

  // 4. Left partition elements are ≤ pivot
  assert (pure (between_bounds s1 1 (Seq.index s_pivot 0)));

  // 5. Right partition elements are strictly > pivot
  assert (pure (strictly_larger_than s2 (Seq.index s_pivot 0)));

  // 6. Exact complexity: 2 comparisons (hi - lo - 1 = 3 - 0 - 1 = 2)
  assert (pure (complexity_exact_linear cf 0 2));

  // 7. Result is a permutation of input
  reveal_opaque (`%SS.permutation) (SS.permutation s0 (Seq.append s1 (Seq.append s_pivot s2)));

  // 8. Verify the multiset is preserved (length check via permutation)
  partition_permutation_valid s1 s_pivot s2 (Seq.index s_pivot 0);

  // Free ghost counter
  GR.free ctr;

  // Rejoin ranges for cleanup and runtime reads
  A.pts_to_range_join arr p (p+1) 3;
  A.pts_to_range_join arr 0 p 3;

  // Convert back to pts_to so we can read elements
  with s_final. assert (A.pts_to_range arr 0 3 s_final);
  A.pts_to_range_elim arr 1.0R s_final;

  // Runtime checks: read all 3 elements and verify bounds [1,3].
  // The ghost proof (between_bounds on sub-sequences) guarantees each element
  // is in [1,3]; these comparisons survive extraction as real C checks.
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  let ok = (int_leq 1 v0 && int_leq v0 3) &&
           (int_leq 1 v1 && int_leq v1 3) &&
           (int_leq 1 v2 && int_leq v2 3);

  // Cleanup
  with s_cleanup. assert (A.pts_to arr s_cleanup);
  rewrite (A.pts_to arr s_cleanup) as (A.pts_to (V.vec_to_array v) s_cleanup);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

#pop-options
