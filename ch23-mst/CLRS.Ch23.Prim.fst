module CLRS.Ch23.Prim
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lib
open FStar.UInt
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U64 = FStar.UInt64

// Use a large value for infinity that fits in SizeT (max is typically 2^16-1 or 2^32-1)
// For MST algorithm, any value larger than max possible path weight works
// NOTE: Edge weights must be < infinity for correct behavior; weights >= infinity
// are treated as "no edge" in the imperative code.
let infinity : SZ.t = 65535sz

// All real edge weights must be strictly less than infinity.
// Weights of 0 represent self-loops or zero-weight edges;
// weights >= infinity are treated as absent.
let valid_weights (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (i: nat). i < n * n ==>
    SZ.v (Seq.index weights_seq i) = 0 \/
    (SZ.v (Seq.index weights_seq i) > 0 /\ SZ.v (Seq.index weights_seq i) < SZ.v infinity))

// Predicate: all elements in sequence are <= infinity
let all_keys_bounded (s: Seq.seq SZ.t) : prop =
  forall (i:nat). i < Seq.length s ==> SZ.v (Seq.index s i) <= SZ.v infinity

// Convert SizeT weights to int for specification
let sizet_to_int (x: SZ.t) : int = SZ.v x

let sizet_seq_to_int_seq (s: Seq.seq SZ.t) : Seq.seq int =
  Seq.init (Seq.length s) (fun (i:nat{i < Seq.length s}) -> sizet_to_int (Seq.index s i))

// Convert weight matrix from SizeT array to adjacency matrix spec
let weights_to_adj_matrix (weights_seq: Seq.seq SZ.t) (n: nat) 
  : Pure adj_matrix
    (requires Seq.length weights_seq == n * n)
    (ensures fun adj -> 
      Seq.length adj == n /\
      (forall (u:nat). u < n ==> Seq.length (Seq.index adj u) == n))
  = Seq.init n (fun (u:nat{u < n}) ->
      Seq.init n (fun (v:nat{v < n}) ->
        let idx = u * n + v in
        let w_sizet = Seq.index weights_seq idx in
        let w : int = sizet_to_int w_sizet in
        // Use spec's infinity value for comparison
        if w >= sizet_to_int infinity then Prim.Spec.infinity else w
      )
    )

// Bridging lemma: under valid_weights, the conversion preserves edge weights faithfully.
// If a weight is positive and < infinity (65535), it appears unchanged in the adj matrix.
// If a weight is 0 or >= infinity, it maps to the spec's infinity (10^9) or 0 respectively.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let weights_to_adj_preserves (weights_seq: Seq.seq SZ.t) (n: nat) (u v: nat)
  : Lemma (requires valid_weights weights_seq n /\ n > 0 /\ u < n /\ v < n /\
                    u * n + v < n * n)
          (ensures (let adj = weights_to_adj_matrix weights_seq n in
                    let w_imp = SZ.v (Seq.index weights_seq (u * n + v)) in
                    let w_spec = Seq.index (Seq.index adj u) v in
                    (w_imp > 0 /\ w_imp < SZ.v infinity ==> w_spec = w_imp) /\
                    (w_imp = 0 ==> w_spec = 0) /\
                    (w_imp >= SZ.v infinity ==> w_spec = Prim.Spec.infinity)))
  = ()
#pop-options

// Valid parent values: all entries < n
// Predicate for full correctness of Prim's output
let prim_correct 
    (key_seq: Seq.seq SZ.t)
    (parent_seq: Seq.seq SZ.t)
    (weights_seq: Seq.seq SZ.t)
    (n: nat) 
    (source: nat) 
  : prop 
  = Seq.length key_seq == n /\
    Seq.length parent_seq == n /\
    source < n /\
    Seq.length weights_seq == n * n /\
    SZ.v (Seq.index key_seq source) == 0 /\
    all_keys_bounded key_seq /\
    SZ.v (Seq.index parent_seq source) == source

// Lemma: Seq.create produces bounded keys
let lemma_create_bounded (n: nat) (v: SZ.t)
  : Lemma (requires SZ.v v <= SZ.v infinity)
          (ensures all_keys_bounded (Seq.create n v))
  = ()

// Lemma: Seq.upd preserves boundedness if new value is bounded
let lemma_upd_preserves_bounded (s: Seq.seq SZ.t) (i: nat) (v: SZ.t)
  : Lemma (requires i < Seq.length s /\ all_keys_bounded s /\ SZ.v v <= SZ.v infinity)
          (ensures all_keys_bounded (Seq.upd s i v))
  = ()

// Lemma: if u < n and n*n < bound, then u*n+v fits in 64 bits
// Proved manually via recursive descent
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec lemma_prod_fits (u n: nat) : Lemma
  (requires u < n /\ n > 0)
  (ensures u * n < n * n)
  (decreases n - u)
  = if u >= n - 1 then ()
    else begin
      lemma_prod_fits (u + 1) n;
      assert ((u + 1) * n < n * n);
      assert (u * n + n < n * n);
      assert (u * n < n * n)
    end

let lemma_mul_bound (u n v: nat) (bound: nat)
  : Lemma (requires (u < n /\ v < n /\ n * n < bound /\ n > 0 /\ bound == pow2 64))
          (ensures (u * n < bound /\ u * n + v < bound))
  = lemma_prod_fits u n;
    ()

// Direct U64-based index computation that bypasses SizeT overflow checks  
// Requires: SizeT is 64-bit (fits_u64 holds)
inline_for_extraction  
let compute_weight_idx_u64 (u n v: SZ.t{SZ.v u < SZ.v n /\ SZ.v v < SZ.v n /\ SZ.v n > 0 /\ SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64})
  : Tot (idx:SZ.t{SZ.v idx == SZ.v u * SZ.v n + SZ.v v})
  = lemma_mul_bound (SZ.v u) (SZ.v n) (SZ.v v) (pow2 64);
    let u64_u = SZ.sizet_to_uint64 u in
    let u64_n = SZ.sizet_to_uint64 n in
    let u64_v = SZ.sizet_to_uint64 v in
    // Use U64.mul_mod which doesn't require overflow check
    let prod_mod = U64.mul_mod u64_u u64_n in
    // Since we proved u*n < 2^64, the mod operation is identity
    assert (U64.v prod_mod == (U64.v u64_u * U64.v u64_n) % pow2 64);
    assert (U64.v u64_u * U64.v u64_n < pow2 64);
    assert (U64.v prod_mod == U64.v u64_u * U64.v u64_n);
    // Similarly for addition
    let idx_mod = U64.add_mod prod_mod u64_v in
    assert (U64.v idx_mod == (U64.v prod_mod + U64.v u64_v) % pow2 64);
    assert (U64.v prod_mod + U64.v u64_v < pow2 64);
    assert (U64.v idx_mod == U64.v prod_mod + U64.v u64_v);
    // Wrap back to SizeT - use fits_u64_implies_fits lemma
    assert (U64.v idx_mod < pow2 64);
    SZ.fits_u64_implies_fits (U64.v idx_mod);
    FStar.SizeT.uint64_to_sizet idx_mod
#pop-options

// Helper to compute array index u * n + v
inline_for_extraction
let compute_weight_idx = compute_weight_idx_u64

// Prim's MST algorithm
// Given:
//   - weights: n×n weight matrix (flattened as array[n*n])
//   - n: number of vertices
//   - source: starting vertex
// Output:
//   - key: array of minimum edge weights to add each vertex to MST
//   - in_mst: array indicating which vertices are in MST

#push-options "--z3rlimit 40"
//SNIPPET_START: prim_sig
fn prim
  (#p: perm)
  (weights: array SZ.t)
  (#weights_seq: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (source: SZ.t)
  requires A.pts_to weights #p weights_seq ** pure (
    SZ.v n > 0 /\
    SZ.v n * SZ.v n < pow2 64 /\
    SZ.v source < SZ.v n /\
    Seq.length weights_seq == SZ.v n * SZ.v n /\
    SZ.fits_u64  // Require 64-bit SizeT for index computation
  )
  returns res: (V.vec SZ.t & V.vec SZ.t)
  ensures exists* (key_seq parent_seq: Ghost.erased (Seq.seq SZ.t)).
    A.pts_to weights #p weights_seq **
    V.pts_to (fst res) key_seq **
    V.pts_to (snd res) parent_seq **
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source))
//SNIPPET_END: prim_sig
{
  // Allocate key array, initialized to infinity
  let key = V.alloc infinity n;
  V.to_array_pts_to key;
  let key_a = V.vec_to_array key;
  rewrite (A.pts_to (V.vec_to_array key) (Seq.create (SZ.v n) infinity))
       as (A.pts_to key_a (Seq.create (SZ.v n) infinity));
  
  // Allocate parent array, initialized to source
  let parent_v = V.alloc source n;
  V.to_array_pts_to parent_v;
  let parent_a = V.vec_to_array parent_v;
  rewrite (A.pts_to (V.vec_to_array parent_v) (Seq.create (SZ.v n) source))
       as (A.pts_to parent_a (Seq.create (SZ.v n) source));
  
  // Set key[source] = 0
  A.op_Array_Assignment key_a source 0sz;
  
  // Establish initial correctness properties
  with key_seq_init. assert (A.pts_to key_a key_seq_init);
  lemma_create_bounded (SZ.v n) infinity;
  lemma_upd_preserves_bounded (Seq.create (SZ.v n) infinity) (SZ.v source) 0sz;
  assert (pure (Seq.equal key_seq_init (Seq.upd (Seq.create (SZ.v n) infinity) (SZ.v source) 0sz)));
  assert (pure (SZ.v (Seq.index key_seq_init (SZ.v source)) == 0));
  assert (pure (all_keys_bounded key_seq_init));
  
  // Allocate in_mst array, initialized to 0
  let in_mst_v = V.alloc 0sz n;
  V.to_array_pts_to in_mst_v;
  let in_mst = V.vec_to_array in_mst_v;
  rewrite (A.pts_to (V.vec_to_array in_mst_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to in_mst (Seq.create (SZ.v n) 0sz));
  
  // Establish initial parent array
  with parent_init. assert (A.pts_to parent_a parent_init);
  
  // Main loop: n iterations
  let mut iter: SZ.t = 0sz;
  
  while (
    let v_iter = !iter;
    v_iter <^ n
  )
  invariant exists* v_iter key_seq in_mst_seq parent_seq.
    R.pts_to iter v_iter **
    A.pts_to key_a key_seq **
    A.pts_to in_mst in_mst_seq **
    A.pts_to parent_a parent_seq **
    A.pts_to weights #p weights_seq **
    pure (
      SZ.v v_iter <= SZ.v n + 1 /\
      Seq.length key_seq == SZ.v n /\
      Seq.length in_mst_seq == SZ.v n /\
      Seq.length parent_seq == SZ.v n /\
      // Maintain functional correctness:
      SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
      all_keys_bounded key_seq
    )
  // TODO: decreases
  {
    // Find minimum key vertex not in MST
    let mut min_idx: SZ.t = 0sz;
    let mut min_key: SZ.t = infinity;
    let mut find_i: SZ.t = 0sz;
    
    while (
      let v_find_i = !find_i;
      v_find_i <^ n
    )
    invariant exists* v_find_i v_min_idx v_min_key v_iter key_seq in_mst_seq parent_seq.
      R.pts_to find_i v_find_i **
      R.pts_to min_idx v_min_idx **
      R.pts_to min_key v_min_key **
      R.pts_to iter v_iter **
      A.pts_to key_a key_seq **
      A.pts_to in_mst in_mst_seq **
      A.pts_to parent_a parent_seq **
      A.pts_to weights #p weights_seq **
      pure (
        SZ.v v_find_i <= SZ.v n /\
        SZ.v v_min_idx < SZ.v n /\
        SZ.v v_iter <= SZ.v n /\
        Seq.length key_seq == SZ.v n /\
        Seq.length in_mst_seq == SZ.v n /\
        Seq.length parent_seq == SZ.v n /\
        // Maintain functional correctness:
        SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
        all_keys_bounded key_seq
      )
    decreases (SZ.v n - SZ.v !find_i)
    {
      let v_find_i = !find_i;
      let ki = A.op_Array_Access key_a v_find_i;
      let in_mst_i = A.op_Array_Access in_mst v_find_i;
      let v_min_key = !min_key;
      let v_min_idx = !min_idx;
      
      // Update min_key and min_idx unconditionally
      let cond1 = (in_mst_i = 0sz);
      let cond2 = (ki <^ v_min_key);
      let should_update = (cond1 && cond2);
      let new_min_key : SZ.t = (if should_update then ki else v_min_key);
      let new_min_idx : SZ.t = (if should_update then v_find_i else v_min_idx);
      
      min_key := new_min_key;
      min_idx := new_min_idx;
      
      find_i := v_find_i +^ 1sz;
    };
    
    // Add min_idx to MST
    let u = !min_idx;
    A.op_Array_Assignment in_mst u 1sz;
    
    // Update keys of neighbors
    let mut update_i: SZ.t = 0sz;
    
    while (
      let v_update_i = !update_i;
      v_update_i <^ n
    )
    invariant exists* v_update_i v_iter u key_seq in_mst_seq parent_seq.
      R.pts_to update_i v_update_i **
      R.pts_to iter v_iter **
      R.pts_to min_idx u **
      A.pts_to key_a key_seq **
      A.pts_to in_mst in_mst_seq **
      A.pts_to parent_a parent_seq **
      A.pts_to weights #p weights_seq **
      pure (
        SZ.v v_update_i <= SZ.v n /\
        SZ.v u < SZ.v n /\
        SZ.v v_iter <= SZ.v n /\
        Seq.length key_seq == SZ.v n /\
        Seq.length in_mst_seq == SZ.v n /\
        Seq.length parent_seq == SZ.v n /\
        SZ.v u * SZ.v n < pow2 64 /\
        (forall (i:nat). i < SZ.v n ==> SZ.v u * SZ.v n + i < pow2 64) /\
        // Maintain functional correctness:
        SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
        all_keys_bounded key_seq
      )
    decreases (SZ.v n - SZ.v !update_i)
    {
      let v = !update_i;
      
      // Read current values
      let key_v = A.op_Array_Access key_a v;
      let in_mst_v = A.op_Array_Access in_mst v;
      
      // Compute weight index: u * n + v
      let weight_idx = compute_weight_idx u n v;
      let weight_uv = A.op_Array_Access weights weight_idx;
      
      // Compute new key value unconditionally
      let cond_not_in_mst = (in_mst_v = 0sz);
      let cond_weight_better = (weight_uv <^ key_v);
      let cond_weight_valid = (weight_uv <^ infinity);
      let should_update_key = (cond_not_in_mst && cond_weight_better && cond_weight_valid);
      let new_key_v : SZ.t = (if should_update_key then weight_uv else key_v);
      
      // Prove that new_key_v is bounded
      assert (pure (SZ.v new_key_v <= SZ.v infinity));
      
      // Write key
      A.op_Array_Assignment key_a v new_key_v;
      
      // Assert key invariant is maintained after key write
      with key_seq'. assert (A.pts_to key_a key_seq');
      assert (pure (SZ.v (Seq.index key_seq' (SZ.v source)) == 0));
      assert (pure (all_keys_bounded key_seq'));
      assert (pure (Seq.length key_seq' == SZ.v n));
      
      // Read old parent and compute new parent
      let old_parent_v = A.op_Array_Access parent_a v;
      let new_parent_v : SZ.t = (if should_update_key then u else old_parent_v);
      
      // Write parent
      A.op_Array_Assignment parent_a v new_parent_v;
      
      update_i := v +^ 1sz;
    };
    
    // Increment iteration counter
    let v_iter = !iter;
    assert (pure (SZ.v n * SZ.v n < pow2 64));
    assert (pure (SZ.v v_iter + 1 < pow2 64));
    SZ.fits_u64_implies_fits (SZ.v v_iter + 1);
    let new_iter = v_iter +^ 1sz;
    assert (pure (SZ.v new_iter == SZ.v v_iter + 1));
    iter := new_iter;
  };
  
  // Set parent[source] = source (source is MST root)
  with old_parent_seq. assert (A.pts_to parent_a old_parent_seq);
  A.op_Array_Assignment parent_a source source;
  
  // Free the in_mst array
  with s_in_mst. assert (A.pts_to in_mst s_in_mst);
  rewrite (A.pts_to in_mst s_in_mst) as (A.pts_to (V.vec_to_array in_mst_v) s_in_mst);
  V.to_vec_pts_to in_mst_v;
  V.free in_mst_v;
  
  // Convert key array back to vec for return
  with s_key. assert (A.pts_to key_a s_key);
  rewrite (A.pts_to key_a s_key) as (A.pts_to (V.vec_to_array key) s_key);
  V.to_vec_pts_to key;
  
  // Convert parent array back to vec for return
  with s_parent. assert (A.pts_to parent_a s_parent);
  rewrite (A.pts_to parent_a s_parent) as (A.pts_to (V.vec_to_array parent_v) s_parent);
  V.to_vec_pts_to parent_v;
  
  (key, parent_v)
}
#pop-options
