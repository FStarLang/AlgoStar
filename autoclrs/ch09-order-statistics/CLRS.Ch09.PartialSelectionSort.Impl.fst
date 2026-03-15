(*
   Selection Algorithm — Verified implementation in Pulse

   Implements the k-th smallest element finder using partial selection sort.

   Every comparison is ghost-ticked; there is ONE version of each function
   that proves both correctness and complexity.

   Verification:
   - NO admits, NO assumes ✓
   - Correctness: permutation, sorted_prefix, prefix_leq_suffix ✓
   - Complexity: total comparisons ≤ k*(n-1) ✓
*)

module CLRS.Ch09.PartialSelectionSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Common.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical
module GR = Pulse.Lib.GhostReference

// ========== Definitions ==========

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

let is_min_in_range (s: Seq.seq int) (i: nat) (start: nat) (len: nat) : prop =
  start <= i /\ i < len /\ len <= Seq.length s /\
  (forall (j: nat). start <= j /\ j < len ==> Seq.index s i <= Seq.index s j)

let sorted_prefix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)

let prefix_leq_suffix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < bound /\ bound <= j /\ j < Seq.length s ==>
    Seq.index s i <= Seq.index s j)

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

// ========== find_min_index_from — ticks once per comparison ==========

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn find_min_index_from
  (#p: perm)
  (a: array int)
  (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s ** GR.pts_to ctr c0 **
    pure (
      SZ.v start < SZ.v len /\
      SZ.v len == Seq.length s /\
      SZ.v len == A.length a
    )
  returns min_idx: SZ.t
  ensures exists* (cf: nat).
    A.pts_to a #p s ** GR.pts_to ctr cf **
    pure (
      SZ.v start <= SZ.v min_idx /\
      SZ.v min_idx < SZ.v len /\
      is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v len - SZ.v start - 1
    )
{
  let mut min_idx: SZ.t = start;
  let mut i: SZ.t = start + 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin_idx (vc: nat).
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    GR.pts_to ctr vc **
    A.pts_to a #p s **
    pure (
      SZ.v vi > SZ.v start /\
      SZ.v vi <= SZ.v len /\
      SZ.v start <= SZ.v vmin_idx /\
      SZ.v vmin_idx < SZ.v len /\
      SZ.v vmin_idx < SZ.v vi /\
      (forall (j: nat). SZ.v start <= j /\ j < SZ.v vi ==>
        Seq.index s (SZ.v vmin_idx) <= Seq.index s j) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi - SZ.v start - 1
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let vmin_idx = !min_idx;
    let curr = a.(vi);
    let min_val = a.(vmin_idx);
    
    tick ctr;
    if (curr < min_val) {
      min_idx := vi;
    };
    
    i := vi + 1sz;
  };
  
  !min_idx
}
#pop-options

// ========== select — single function, correctness + complexity ==========

#push-options "--z3rlimit 20 --ifuel 2 --fuel 2"
//SNIPPET_START: select
fn select
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s0 /\
      SZ.v n == A.length a /\
      SZ.v n > 0 /\
      SZ.v k > 0 /\
      SZ.v k <= SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1) /\
      complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
    )
//SNIPPET_END: select
{
  let mut round: SZ.t = 0sz;
  
  while (!round <^ k)
  invariant exists* vround s_curr (vc: nat).
    R.pts_to round vround **
    A.pts_to a s_curr **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v k /\
      Seq.length s_curr == Seq.length s0 /\
      permutation s0 s_curr /\
      sorted_prefix s_curr (SZ.v vround) /\
      prefix_leq_suffix s_curr (SZ.v vround) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= op_Multiply (SZ.v vround) (SZ.v n - 1)
    )
  decreases (SZ.v k `Prims.op_Subtraction` SZ.v !round)
  {
    let vround = !round;
    with s_pre. assert (A.pts_to a s_pre);
    
    let min_idx = find_min_index_from a vround n ctr;
    
    let val_round = a.(vround);
    let val_min = a.(min_idx);
    
    a.(vround) <- val_min;
    a.(min_idx) <- val_round;
    
    with s_post. assert (A.pts_to a s_post);
    swap_is_permutation s_pre (SZ.v vround) (SZ.v min_idx);
    
    round := vround + 1sz;
  };
  
  let idx = k - 1sz;
  with s_arr. assert (A.pts_to a s_arr);
  let value = a.(idx);
  assert (pure (value == Seq.index s_arr (SZ.v idx)));
  value
}
#pop-options
