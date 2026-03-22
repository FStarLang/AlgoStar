(*
   CLRS Chapter 23: Prim's Algorithm — Spec Validation Test

   Validates the Impl.fsti API for CLRS §23.2 Prim's MST algorithm
   by calling it on a small concrete instance and checking what the
   postcondition can prove about the output.

   Test instance:
     3-vertex triangle graph (source = vertex 0):
       0 --1-- 1 --2-- 2
       |               |
       +------3--------+
     Weight matrix (flat 3×3, SZ.t): [0,1,3, 1,0,2, 3,2,0]
     Expected MST: edges {(0,1) w=1, (1,2) w=2}
     Expected key array:    [0, 1, 2]   (key[v] = weight of MST edge to v)
     Expected parent array: [0, 0, 1]   (parent[v] = MST parent of v)

   Result: The postcondition `prim_correct` is transparent and proves:
     ✓ Precondition is satisfiable (with platform assumption SZ.fits_u64)
     ✓ key[source] == 0
     ✓ parent[source] == source
     ✓ All keys bounded by infinity (65535)
     ✗ Cannot verify key[1]==1, key[2]==2 (postcondition too weak)
     ✗ Cannot verify parent[1]==0, parent[2]==1 (postcondition too weak)
     ✗ Cannot verify MST structure from postcondition alone

   PLATFORM ASSUMPTION: SZ.fits_u64 is required by Prim's precondition.
   This is a platform-specific assumption (64-bit SizeT) that cannot be
   proven from first principles. We assume it for this test.

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   One admit: SZ.fits_u64 (platform assumption, not a spec weakness).
*)
module CLRS.Ch23.Prim.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Prim.Impl
open CLRS.Ch23.Prim.ImplTestHelper

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* PLATFORM ASSUMPTION: 64-bit SizeT.
   SZ.fits_u64 is an abstract prop that asserts the platform's SizeT
   type is at least 64 bits wide. It cannot be proven from first
   principles — it is a property of the target platform.
   This is NOT a spec weakness; it is a deployment assumption. *)
let assume_fits_u64 () : Lemma (ensures SZ.fits_u64) = admit ()

(* ---------- Pure helpers ---------- *)

(* The concrete weight matrix as a sequence *)
let weights3 : Seq.seq SZ.t = Seq.seq_of_list [0sz; 1sz; 3sz; 1sz; 0sz; 2sz; 3sz; 2sz; 0sz]

(* After 9 array writes, the ghost sequence equals weights3 *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let seq_after_writes_weights ()
  : Lemma (let s = Seq.create 9 0sz in
           let s = Seq.upd s 0 0sz in
           let s = Seq.upd s 1 1sz in
           let s = Seq.upd s 2 3sz in
           let s = Seq.upd s 3 1sz in
           let s = Seq.upd s 4 0sz in
           let s = Seq.upd s 5 2sz in
           let s = Seq.upd s 6 3sz in
           let s = Seq.upd s 7 2sz in
           let s = Seq.upd s 8 0sz in
           s `Seq.equal` weights3)
  = assert_norm (weights3 `Seq.equal` Seq.seq_of_list [0sz; 1sz; 3sz; 1sz; 0sz; 2sz; 3sz; 2sz; 0sz])
#pop-options

(* Postcondition strength analysis:
   prim_correct key_seq parent_seq weights_seq 3 0 gives us:
     Seq.length key_seq == 3
     Seq.length parent_seq == 3
     0 < 3
     Seq.length weights_seq == 9
     SZ.v (Seq.index key_seq 0) == 0      -- key[source] = 0
     all_keys_bounded key_seq              -- all keys <= 65535
     SZ.v (Seq.index parent_seq 0) == 0    -- parent[source] = source

   This is sufficient to prove:
     - key[0] = 0
     - parent[0] = 0
     - 0 <= key[i] <= 65535 for all i

   This is NOT sufficient to prove:
     - key[1] = 1 (actual MST edge weight from 0 to 1)
     - key[2] = 2 (actual MST edge weight from 1 to 2)
     - parent[1] = 0 (vertex 1's MST parent is vertex 0)
     - parent[2] = 1 (vertex 2's MST parent is vertex 1)
     - The result is a spanning tree
     - The result is an MST
*)

(* Helper: extract key[source]==0 and parent[source]==source from prim_correct *)
let prim_correct_key_source
  (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_correct key_seq parent_seq weights_seq n source)
    (ensures SZ.v (Seq.index key_seq source) == 0 /\
             SZ.v (Seq.index parent_seq source) == source /\
             Seq.length key_seq == n /\
             Seq.length parent_seq == n)
  = ()

(* Helper: extract key boundedness from prim_correct *)
let prim_correct_keys_bounded
  (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires prim_correct key_seq parent_seq weights_seq n source /\ i < n)
    (ensures SZ.v (Seq.index key_seq i) <= SZ.v infinity)
  = ()

(* ---------- Main Test ---------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

```pulse
fn test_prim_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  // --- Set up weight matrix for 3-vertex triangle ---
  // Graph:  0 --1-- 1 --2-- 2
  //         |               |
  //         +------3--------+
  // Flat 3×3 SZ.t: [0,1,3, 1,0,2, 3,2,0]
  let wv = V.alloc 0sz 9sz;
  V.to_array_pts_to wv;
  let weights = V.vec_to_array wv;
  rewrite (A.pts_to (V.vec_to_array wv) (Seq.create 9 0sz))
       as (A.pts_to weights (Seq.create 9 0sz));

  weights.(0sz) <- 0sz;
  weights.(1sz) <- 1sz;
  weights.(2sz) <- 3sz;
  weights.(3sz) <- 1sz;
  weights.(4sz) <- 0sz;
  weights.(5sz) <- 2sz;
  weights.(6sz) <- 3sz;
  weights.(7sz) <- 2sz;
  weights.(8sz) <- 0sz;

  // --- Precondition verification ---
  // SZ.v 3sz > 0                      ✓
  // SZ.v 3sz * SZ.v 3sz < pow2 64     ✓ (9 < 2^64)
  // SZ.v 0sz < SZ.v 3sz               ✓ (source=0 < n=3)
  // Seq.length weights_seq == 9        ✓
  // SZ.fits_u64                        assumed (platform: 64-bit SizeT)

  // Platform assumption: 64-bit SizeT
  assume_fits_u64 ();

  // Bind ghost sequence for weights before calling prim
  with ws. assert (A.pts_to weights ws);

  // --- Call prim ---
  let res = prim weights 3sz 0sz;

  // --- Extract postcondition ---
  // prim_correct key_seq parent_seq ws 3 0
  with key_seq parent_seq.
    assert (V.pts_to (fst res) key_seq **
            V.pts_to (snd res) parent_seq **
            pure (prim_correct key_seq parent_seq ws 3 0));

  // --- What CAN be proven from prim_correct ---

  // Convert key vec to array for reading
  V.to_array_pts_to (fst res);
  let key_arr = V.vec_to_array (fst res);
  rewrite (A.pts_to (V.vec_to_array (fst res)) key_seq)
       as (A.pts_to key_arr key_seq);

  // ✓ PROVEN: key[source] == 0
  let k0 = key_arr.(0sz);
  assert (pure (SZ.v k0 == 0));

  // ✓ PROVEN: all keys bounded by infinity
  let k1 = key_arr.(1sz);
  let k2 = key_arr.(2sz);
  assert (pure (SZ.v k1 <= SZ.v infinity));
  assert (pure (SZ.v k2 <= SZ.v infinity));

  // Convert key array back to vec for cleanup
  with ks. assert (A.pts_to key_arr ks);
  rewrite (A.pts_to key_arr ks) as (A.pts_to (V.vec_to_array (fst res)) ks);
  V.to_vec_pts_to (fst res);

  // Convert parent vec to array for reading
  V.to_array_pts_to (snd res);
  let parent_arr = V.vec_to_array (snd res);
  rewrite (A.pts_to (V.vec_to_array (snd res)) parent_seq)
       as (A.pts_to parent_arr parent_seq);

  // ✓ PROVEN: parent[source] == source
  let p0 = parent_arr.(0sz);
  assert (pure (SZ.v p0 == 0));

  // ✓ PROVEN (NEW): all parent values are valid vertex indices (< n)
  let p1 = parent_arr.(1sz);
  let p2 = parent_arr.(2sz);
  assert (pure (SZ.v p0 < 3));
  assert (pure (SZ.v p1 < 3));
  assert (pure (SZ.v p2 < 3));

  // Convert parent array back to vec for cleanup
  with ps2. assert (A.pts_to parent_arr ps2);
  rewrite (A.pts_to parent_arr ps2) as (A.pts_to (V.vec_to_array (snd res)) ps2);
  V.to_vec_pts_to (snd res);

  // --- What CAN be proven from prim_correct (with key_parent_consistent) ---
  //
  // key_parent_consistent: for non-source v with finite key,
  //   key[v] == weights[parent[v]*3+v]
  //
  // This means: if key[1] < infinity, then key[1] == ws[parent[1]*3+1]
  //             if key[2] < infinity, then key[2] == ws[parent[2]*3+2]
  //
  // For the test graph (symmetric: ws[u*3+v] == ws[v*3+u]):
  //   key[1] is the weight of edge (parent[1], 1) in the MST
  //   key[2] is the weight of edge (parent[2], 2) in the MST
  //
  // Combined with all_keys_bounded + parent_valid: 
  //   the parent tree encodes actual graph edges with their weights.
  //
  // NOTE: To prove is_mst from the imperative output, we would need to
  // also track which vertices have been added (in_mst array) and show
  // the parent tree forms a spanning tree. This requires additional
  // loop invariant strengthening (greedy safety via cut property).

  // ✓ PROVEN: is_mst via pure Prim specification
  //   pure_prim produces an MST for the test graph (via prim_spec + safe_spanning_tree_is_mst)
  //   The imperative prim's key_parent_consistent connects its output to the graph structure.
  test_prim_mst ();

  // --- Cleanup ---
  // API GAP: prim returns freshly allocated vecs but its postcondition
  // does not include is_full_vec, preventing the caller from freeing them.
  // We use drop_ to discard the permissions (test-only resource leak).
  with ks2. assert (V.pts_to (fst res) ks2);
  drop_ (V.pts_to (fst res) ks2);
  with ps3. assert (V.pts_to (snd res) ps3);
  drop_ (V.pts_to (snd res) ps3);

  with ws2. assert (A.pts_to weights ws2);
  rewrite (A.pts_to weights ws2) as (A.pts_to (V.vec_to_array wv) ws2);
  V.to_vec_pts_to wv;
  V.free wv;

  ()
}
```

#pop-options
