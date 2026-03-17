(*
   Spec Validation Test: Union-Find (CLRS §21.3)

   Tests CLRS.Ch21.UnionFind.Impl.fsti on a concrete 3-element instance.

   Validates:
   1. make_set precondition is satisfiable
   2. After make_set, find_set returns self for each element (postcondition precision)
   3. After union(0,1), find(0)==find(1) (merge correctness)
   4. After union(0,1), find(2)==2 (stability of disjoint elements)
   5. Chained union: union(0,1) then union(1,2), proves find(0)==find(1)==find(2)
      (requires rank bound postcondition to chain unions)

   No admits. No assumes. Fully verified by F* and Z3.
*)

module CLRS.Ch21.UnionFind.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch21.UnionFind.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch21.UnionFind.Spec

(* ---------- Pure helper: fresh forest has pure_find(x) == x ---------- *)

(* When uf_inv holds and all ranks are 0, every element must be a root.
   Proof: rank_invariant says non-root x has rank[x] < rank[parent[x]],
   but with all ranks 0 this gives 0 < 0, contradiction. So parent[x] == x,
   and pure_find_root gives pure_find(forest, x) == x. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let fresh_forest_find (sp sr: Seq.seq SZ.t) (n: nat) (x: nat)
  : Lemma
    (requires
      n > 0 /\ x < n /\
      n <= Seq.length sp /\ n <= Seq.length sr /\
      Spec.uf_inv (to_uf sp sr n) /\
      (forall (i: nat). i < n /\ i < Seq.length sr ==> SZ.v (Seq.index sr i) == 0))
    (ensures
      Spec.pure_find (to_uf sp sr n) x == x)
  = let f = to_uf sp sr n in
    // Show that rank[x] == 0 in the spec forest
    // to_nat_seq sr n = Seq.init n (...) so Seq.index (to_nat_seq sr n) x == SZ.v (Seq.index sr x) == 0
    assert (Seq.index f.Spec.rank x == 0);
    // rank_invariant: if parent[x] != x then rank[x] < rank[parent[x]], i.e. 0 < 0, contradiction
    // So parent[x] == x
    assert (Seq.index f.Spec.parent x == x);
    // By pure_find_root
    Spec.pure_find_root f x
#pop-options

(* ---------- Test function ---------- *)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
```pulse
fn test_union_find ()
  requires emp
  returns _: unit
  ensures emp
{
  let n = 3sz;

  // ===== Allocate parent and rank arrays =====
  let vp = V.alloc 0sz 3sz;
  V.to_array_pts_to vp;
  let parent = V.vec_to_array vp;
  rewrite (A.pts_to (V.vec_to_array vp) (Seq.create 3 0sz))
       as (A.pts_to parent (Seq.create 3 0sz));

  let vr = V.alloc 0sz 3sz;
  V.to_array_pts_to vr;
  let rank = V.vec_to_array vr;
  rewrite (A.pts_to (V.vec_to_array vr) (Seq.create 3 0sz))
       as (A.pts_to rank (Seq.create 3 0sz));

  A.pts_to_len parent;
  A.pts_to_len rank;

  // ===== make_set: initialize 3-element forest =====
  make_set parent rank n;

  // Bind ghost witnesses from make_set postcondition
  with sp sr. assert (A.pts_to parent sp ** A.pts_to rank sr);

  // ===== Test 1: find_set on fresh forest returns self =====

  // Helper: all-zero ranks + uf_inv implies pure_find(x) == x
  fresh_forest_find sp sr 3 0;
  fresh_forest_find sp sr 3 1;
  fresh_forest_find sp sr 3 2;

  // find_set(0) should return 0
  let r0 = find_set parent 0sz n #_ #sr;
  with sp1. assert (A.pts_to parent sp1);
  assert (pure (SZ.v r0 == 0));

  // find_set(1) should return 1
  let r1 = find_set parent 1sz n #_ #sr;
  with sp2. assert (A.pts_to parent sp2);
  assert (pure (SZ.v r1 == 1));

  // find_set(2) should return 2
  let r2 = find_set parent 2sz n #_ #sr;
  with sp3. assert (A.pts_to parent sp3);
  assert (pure (SZ.v r2 == 2));

  // ===== Test 2: union(0, 1) =====

  // Establish rank bound precondition: all ranks are 0 < 3
  // (rank unchanged by find_set, still sr from make_set)
  union parent rank 0sz 1sz n;
  with sp4 sr4. assert (A.pts_to parent sp4 ** A.pts_to rank sr4);

  // --- Merge verification: find(0) == find(1) ---
  let r0' = find_set parent 0sz n #_ #sr4;
  with sp5. assert (A.pts_to parent sp5);

  let r1' = find_set parent 1sz n #_ #sr4;
  with sp6. assert (A.pts_to parent sp6);

  assert (pure (SZ.v r0' == SZ.v r1'));

  // --- Stability verification: find(2) == 2 (disjoint from 0 and 1) ---
  let r2' = find_set parent 2sz n #_ #sr4;
  with sp7. assert (A.pts_to parent sp7);
  assert (pure (SZ.v r2' == 2));

  // ===== Test 3: chained union — union(1, 2) after union(0, 1) =====

  // The rank bound postcondition from the first union, combined with
  // make_set's all-zero ranks, ensures sr4[i] <= 0 + 1 = 1 < 3 = n.
  // This satisfies the second union's rank precondition.
  union parent rank 1sz 2sz n;
  with sp8 sr8. assert (A.pts_to parent sp8 ** A.pts_to rank sr8);

  // --- Transitivity: find(0) == find(1) == find(2) ---
  let r0'' = find_set parent 0sz n #_ #sr8;
  with sp9. assert (A.pts_to parent sp9);

  let r1'' = find_set parent 1sz n #_ #sr8;
  with sp10. assert (A.pts_to parent sp10);

  let r2'' = find_set parent 2sz n #_ #sr8;
  with sp11. assert (A.pts_to parent sp11);

  // Merge from second union: find(1) == find(2)
  assert (pure (SZ.v r1'' == SZ.v r2''));

  // Membership from second union: 0 was in 1's class (from first union),
  // so find(0) == find(1) in the merged forest
  assert (pure (SZ.v r0'' == SZ.v r1''));

  // Transitivity: all three elements in the same equivalence class
  assert (pure (SZ.v r0'' == SZ.v r2''));

  // ===== Cleanup =====
  rewrite (A.pts_to parent sp11) as (A.pts_to (V.vec_to_array vp) sp11);
  V.to_vec_pts_to vp;
  V.free vp;

  rewrite (A.pts_to rank sr8) as (A.pts_to (V.vec_to_array vr) sr8);
  V.to_vec_pts_to vr;
  V.free vr;
  ()
}
```
#pop-options
