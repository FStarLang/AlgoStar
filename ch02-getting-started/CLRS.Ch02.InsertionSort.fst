(*
   Insertion Sort - Verified implementation in Pulse
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch02.InsertionSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical

//SNIPPET_START: definitions
// ========== Definitions ==========

let sorted (s: Seq.seq int)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let prefix_sorted (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i <= j /\ j < k ==> Seq.index s i <= Seq.index s j)

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
//SNIPPET_END: definitions

// ========== Permutation lemmas ==========

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    Seq.Properties.perm_len s1 s2

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
  = reveal_opaque (`%permutation) (permutation s s)

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    reveal_opaque (`%permutation) (permutation s2 s3);
    reveal_opaque (`%permutation) (permutation s1 s3);
    Seq.perm_len s1 s2;
    Seq.perm_len s1 s3;
    Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1)

// ========== Swap lemmas ==========

let lemma_swap_is_two_upds (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s /\ i <> j)
          (ensures (let vi = Seq.index s i in
                    let vj = Seq.index s j in
                    let s1 = Seq.upd s i vj in
                    let s2 = Seq.upd s1 j vi in
                    Seq.swap s i j == s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    let sw = Seq.swap s i j in
    let aux (k: nat{k < Seq.length s})
      : Lemma (Seq.index s2 k == Seq.index sw k) = ()
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_elim s2 sw

let swap_is_permutation (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures (let s1 = Seq.upd s i (Seq.index s j) in
                    let s2 = Seq.upd s1 j (Seq.index s i) in
                    permutation s s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    reveal_opaque (`%permutation) (permutation s s2);
    if i = j then (
      Seq.lemma_index_upd1 s i vj;
      Seq.lemma_eq_elim s1 s;
      Seq.lemma_index_upd1 s1 j vi;
      Seq.lemma_eq_elim s2 s1
    ) else (
      lemma_swap_is_two_upds s i j;
      if i < j then Seq.Properties.lemma_swap_permutes s i j
      else Seq.Properties.lemma_swap_permutes s j i
    )

// ========== Sortedness lemmas ==========

// Derive that all prefix elements are <= key from exit condition + prefix sortedness
// When vi > 0: exit says s[vi-1] <= key. Since prefix_sorted s vi, s[k] <= s[vi-1] for k < vi.
// When vi = 0: vacuous.
let lemma_prefix_le_key
  (s s_outer: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires
      vi <= vj /\ vj < Seq.length s /\ Seq.length s == Seq.length s_outer /\
      prefix_sorted s_outer vj /\
      prefix_sorted s vi /\
      (forall (k: nat). k < vi ==> Seq.index s k == Seq.index s_outer k) /\
      // exit condition: vi = 0 or (vi > 0 /\ s_outer[vi-1] <= key)
      // Note: s[vi-1] = s_outer[vi-1] since vi-1 < vi
      // We encode this as: forall k. k + 1 = vi ==> s_outer[k] <= key
      (forall (k: nat). k + 1 == vi ==> Seq.index s_outer k <= key))
    (ensures forall (k: nat). k < vi ==> Seq.index s k <= key)
  = if vi = 0 then ()
    else
      let pred = vi - 1 in
      assert (pred + 1 == vi);
      assert (Seq.index s_outer pred <= key);
      assert (forall (k: nat). k < vi ==> k <= pred);
      assert (forall (k: nat). k <= pred /\ pred < vj ==> Seq.index s_outer k <= Seq.index s_outer pred);
      ()

let lemma_combine_sorted_regions
  (s: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires vi <= vj /\ vj < Seq.length s /\
      prefix_sorted s vi /\
      Seq.index s vi == key /\
      (forall (k: nat). k < vi ==> Seq.index s k <= key) /\
      (forall (k: nat). vi < k /\ k <= vj ==> Seq.index s k > key) /\
      (forall (k1 k2: nat). vi < k1 /\ k1 <= k2 /\ k2 <= vj ==>
        Seq.index s k1 <= Seq.index s k2))
    (ensures prefix_sorted s (vj + 1))
  = ()

//SNIPPET_START: insertion_sort_sig
// ========== Main Algorithm ==========

fn insertion_sort
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  ensures exists* s. A.pts_to a s ** pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s
  )
//SNIPPET_END: insertion_sort_sig
{
//SNIPPET_START: outer_loop
  let mut j: SZ.t = 1sz;
  
  while (!j <^ len)
  invariant exists* vj s.
    R.pts_to j vj **
    A.pts_to a s **
    pure (
      SZ.v vj > 0 /\
      SZ.v vj <= SZ.v len /\
      Seq.length s == Seq.length s0 /\
      Seq.length s <= A.length a /\
      permutation s0 s /\
      prefix_sorted s (SZ.v vj)
    )
//SNIPPET_END: outer_loop
  {
    let vj = !j;
    with s_outer. assert (A.pts_to a s_outer);
    let key = a.(vj);
    
    let mut i: SZ.t = vj;
    let mut continue: bool = true;
    
    if (vj >^ 0sz) {
      let prev = a.(vj - 1sz);
      continue := (prev > key);
    } else {
      continue := false;
    };
    
    // Inner loop: swap key backwards until it finds its position
    // Invariant tracks three regions: [0..vi) sorted prefix, [vi] = key, (vi..vj] shifted & sorted & > key
    // Additional: prefix elements <= shifted elements (cross-region ordering)
    while (!continue)
    invariant exists* vi vcont s_inner.
      R.pts_to i vi **
      R.pts_to continue vcont **
      R.pts_to j vj **
      A.pts_to a s_inner **
      pure (
        SZ.v vi <= SZ.v vj /\
        SZ.v vj < SZ.v len /\
        Seq.length s_inner == Seq.length s0 /\
        Seq.length s_inner <= A.length a /\
        permutation s_outer s_inner /\
        Seq.index s_inner (SZ.v vi) == key /\
        (vcont ==> (SZ.v vi > 0 /\ Seq.index s_inner (SZ.v vi - 1) > key)) /\
        ((not vcont /\ SZ.v vi > 0) ==> Seq.index s_inner (SZ.v vi - 1) <= key) /\
        prefix_sorted s_inner (SZ.v vi) /\
        (forall (k: nat). k < SZ.v vi ==> Seq.index s_inner k == Seq.index s_outer k) /\
        (forall (k: nat). SZ.v vi < k /\ k <= SZ.v vj ==> Seq.index s_inner k > key) /\
        (forall (k1 k2: nat). SZ.v vi < k1 /\ k1 <= k2 /\ k2 <= SZ.v vj ==>
          Seq.index s_inner k1 <= Seq.index s_inner k2) /\
        // Cross-region: all prefix elements <= all shifted elements
        (forall (k1 k2: nat). k1 < SZ.v vi /\ SZ.v vi < k2 /\ k2 <= SZ.v vj ==>
          Seq.index s_inner k1 <= Seq.index s_inner k2)
      )
    {
      let vi = !i;
      with s_pre. assert (A.pts_to a s_pre);
      
      let val_prev = a.(vi - 1sz);
      let val_curr = a.(vi);
      
      a.(vi - 1sz) <- val_curr;
      a.(vi) <- val_prev;
      
      with s_post. assert (A.pts_to a s_post);
      swap_is_permutation s_pre (SZ.v vi - 1) (SZ.v vi);
      
      i := vi - 1sz;
      let new_i = vi - 1sz;
      
      if (new_i >^ 0sz) {
        let new_prev = a.(new_i - 1sz);
        continue := (new_prev > key);
      } else {
        continue := false;
      };
      
      // Need to prove the invariant with vi replaced by vi-1.
      // s_post = Seq.upd (Seq.upd s_pre (vi-1) key) vi val_prev
      // 1. s_post[vi-1] = key ✓ (by upd)
      // 2. prefix_sorted s_post (vi-1): positions < vi-1 unchanged, s_pre was prefix_sorted vi ✓
      // 3. forall k < vi-1: s_post[k] = s_outer[k]: positions < vi-1 unchanged ✓
      // 4. forall k in (vi-1..vj]: s_post[k] > key:
      //      k=vi: s_post[vi] = val_prev > key (from loop condition) ✓
      //      k>vi: s_post[k] = s_pre[k] > key (from pre-invariant) ✓
      // 5. sorted (vi-1..vj]:
      //      For k1=vi, k2>vi: need val_prev <= s_pre[k2].
      //        val_prev = s_pre[vi-1] = s_outer[vi-1].
      //        For k2 > vi: s_pre[k2] = s_inner[k2] from pre-invariant.
      //        From cross-region: s_outer[vi-1] = s_pre[vi-1], and vi-1 < vi < k2,
      //        so s_pre[vi-1] <= s_pre[k2] by the cross-region invariant. ✓
      //      For k1>vi, k2>vi: s_post[k1] = s_pre[k1], s_post[k2] = s_pre[k2], sorted by pre-inv ✓
      // 6. cross-region for (vi-1):
      //      For k1 < vi-1, k2 > vi-1 with k2 <= vj:
      //        If k2 = vi: s_post[k1] = s_pre[k1] = s_outer[k1], s_post[vi] = val_prev = s_outer[vi-1].
      //          Need s_outer[k1] <= s_outer[vi-1]. Since s_outer prefix_sorted(vj+1) and k1 < vi-1, ✓
      //        If k2 > vi: s_post[k1] = s_outer[k1], s_post[k2] = s_pre[k2].
      //          From cross-region pre-inv: s_pre[k1] <= s_pre[k2] since k1 < vi < k2. 
      //          And s_pre[k1] = s_outer[k1] = s_post[k1]. ✓
      ()
    };
    
    // After inner loop
    with s_after. assert (A.pts_to a s_after);
    let vi_final = !i;
    
    // The exit condition (vcont = false) gives us:
    // if vi_final > 0 then s_after[vi_final - 1] <= key
    // Since s_after[k] = s_outer[k] for k < vi_final, and vi_final - 1 < vi_final,
    // this means s_outer[vi_final - 1] <= key.
    // Encoded as: forall k. k + 1 == vi_final ==> s_outer[k] <= key
    // This is what lemma_prefix_le_key needs.
    
    // Help SMT: the exit condition in the invariant uses s_inner[vi - 1], 
    // but s_inner[vi-1] = s_outer[vi-1] from the unchanged-prefix invariant.
    // So the exit condition implies the precondition of lemma_prefix_le_key.
    assert (pure (forall (k: nat). k + 1 == SZ.v vi_final ==> Seq.index s_outer k <= key));
    
    lemma_prefix_le_key s_after s_outer (SZ.v vi_final) (SZ.v vj) key;
    lemma_combine_sorted_regions s_after (SZ.v vi_final) (SZ.v vj) key;
    
    j := vj + 1sz;
  };
  
  with s_final. assert (A.pts_to a s_final);
  assert (pure (prefix_sorted s_final (Seq.length s0)));
  ()
}
