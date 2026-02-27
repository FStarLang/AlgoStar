(*
   CLRS Chapter 9.2: RANDOMIZED-SELECT (Quickselect) — Verified in Pulse

   Finds the k-th smallest element using partition-based selection.
   Algorithm: pick last element as pivot, partition, recurse on relevant half.

   Complexity: O(n²) worst case (deterministic pivot; O(n) expected requires
   randomized pivot, which is not implemented here).
   This replaces the O(nk) selection sort approach in PartialSelectionSort.fst.

   Verification:
   - NO admits, NO assumes
   - Permutation: output array is a rearrangement of input
   - Partition ordering: elements [0,k) ≤ a[k] and elements (k,n) ≥ a[k]
   - Correctness: result == select_spec s0 k (the k-th order statistic)
     Uses bridge lemmas in Helpers.fst to connect Seq.Properties.permutation
     to count_occ-based is_permutation, then applies pulse_correctness_hint
     from Correctness.fst
*)

module CLRS.Ch09.Quickselect
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical
module Helpers = CLRS.Ch09.Quickselect.Helpers
module Correctness = CLRS.Ch09.PartialSelectionSort.Correctness
module Spec = CLRS.Ch09.PartialSelectionSort.Spec

// ========== Permutation infrastructure ==========

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

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

// ========== Swap ==========

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
      let sw = Seq.swap s (if i < j then i else j) (if i < j then j else i) in
      let aux (k: nat{k < Seq.length s})
        : Lemma (Seq.index s2 k == Seq.index sw k) = ()
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_elim s2 sw;
      if i < j then Seq.Properties.lemma_swap_permutes s i j
      else Seq.Properties.lemma_swap_permutes s j i
    )

// ========== Partition correctness predicates ==========

// Elements outside [lo, hi) are unchanged
let unchanged_outside (s1 s2: Seq.seq int) (lo hi: nat) : prop =
  Seq.length s1 == Seq.length s2 /\
  lo <= hi /\ hi <= Seq.length s1 /\
  (forall (i: nat). i < Seq.length s1 ==>
    (i < lo \/ hi <= i) ==>
    Seq.index s1 i == Seq.index s2 i)

//SNIPPET_START: partition_ordered
// Partition ordering property
let partition_ordered (s: Seq.seq int) (lo p hi: nat) : prop =
  lo <= p /\ p < hi /\ hi <= Seq.length s /\
  (forall (idx: nat). idx < Seq.length s ==>
    (lo <= idx /\ idx < p) ==> Seq.index s idx <= Seq.index s p) /\
  (forall (idx: nat). idx < Seq.length s ==>
    (p < idx /\ idx < hi) ==> Seq.index s idx >= Seq.index s p)
//SNIPPET_END: partition_ordered

// ========== In-place partition of a[lo..hi) using a[hi-1] as pivot ==========
// Returns pivot position p such that:
//   - a[lo..p) all <= pivot_value
//   - a[p] == pivot_value
//   - a[p+1..hi) all > pivot_value

#push-options "--z3rlimit 120 --ifuel 2 --fuel 2"
//SNIPPET_START: partition_in_range
fn partition_in_range
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t)
  (hi: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v lo < SZ.v hi /\
    SZ.v hi <= Seq.length s0 /\
    Seq.length s0 == A.length a
  )
  returns pivot_pos: SZ.t
  ensures exists* s1.
    A.pts_to a s1 **
    pure (
      Seq.length s1 == Seq.length s0 /\
      SZ.v lo <= SZ.v pivot_pos /\
      SZ.v pivot_pos < SZ.v hi /\
      permutation s0 s1 /\
      partition_ordered s1 (SZ.v lo) (SZ.v pivot_pos) (SZ.v hi) /\
      unchanged_outside s0 s1 (SZ.v lo) (SZ.v hi)
    )
//SNIPPET_END: partition_in_range
{
  // CLRS partition: use a[hi-1] as pivot
  let hi_m1 = hi -^ 1sz;
  let pivot = A.op_Array_Access a hi_m1;

  let mut i_ref: SZ.t = lo;
  let mut j_ref: SZ.t = lo;

  while (
    let vj = !j_ref;
    vj <^ hi_m1
  )
  invariant exists* vi vj s_cur.
    R.pts_to i_ref vi **
    R.pts_to j_ref vj **
    A.pts_to a s_cur **
    pure (
      SZ.v lo <= SZ.v vi /\
      SZ.v vi <= SZ.v vj /\
      SZ.v vj <= SZ.v hi_m1 /\
      Seq.length s_cur == Seq.length s0 /\
      permutation s0 s_cur /\
      Seq.index s_cur (SZ.v hi_m1) == pivot /\
      // [lo, vi) all <= pivot
      (forall (idx: nat). idx < Seq.length s_cur ==>
        (SZ.v lo <= idx /\ idx < SZ.v vi) ==> Seq.index s_cur idx <= pivot) /\
      // [vi, vj) all > pivot
      (forall (idx: nat). idx < Seq.length s_cur ==>
        (SZ.v vi <= idx /\ idx < SZ.v vj) ==> Seq.index s_cur idx > pivot) /\
      // Elements outside [lo, hi) are unchanged from s0
      unchanged_outside s0 s_cur (SZ.v lo) (SZ.v hi)
    )
  {
    let vj = !j_ref;
    let vi = !i_ref;

    // Always increment j first
    j_ref := vj +^ 1sz;

    with s_pre. assert (A.pts_to a s_pre);

    let aj = A.op_Array_Access a vj;
    let ai = A.op_Array_Access a vi;

    let should_swap = (aj <= pivot);

    let new_ai = (if should_swap then aj else ai);
    let new_aj = (if should_swap then ai else aj);
    A.op_Array_Assignment a vi new_ai;
    A.op_Array_Assignment a vj new_aj;
    with s_post. assert (A.pts_to a s_post);

    if (should_swap) {
      swap_is_permutation s_pre (SZ.v vi) (SZ.v vj);
      i_ref := vi +^ 1sz;
      ()
    } else {
      assert (pure (new_ai == ai /\ new_aj == aj));
      assert (pure (Seq.equal s_post s_pre));
      ()
    };
  };

  // Swap pivot (at hi-1) with a[i] to put pivot in final position
  let vi = !i_ref;
  let ai = A.op_Array_Access a vi;
  with s_pre2. assert (A.pts_to a s_pre2);
  A.op_Array_Assignment a vi pivot;
  A.op_Array_Assignment a hi_m1 ai;
  with s_final. assert (A.pts_to a s_final);
  swap_is_permutation s_pre2 (SZ.v vi) (SZ.v hi_m1);

  vi
}
#pop-options

// ========== Main quickselect algorithm (iterative) ==========

// Wrappers for helper lemmas that reveal opaque permutation
#push-options "--z3rlimit 40"
let perm_lower_bound_forall (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              permutation s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m) ==>
              v <= Seq.index s1 j)
  = reveal_opaque (`%permutation) (permutation s_pre s1);
    assert (Seq.Properties.permutation int s_pre s1);
    Helpers.perm_unchanged_lower_bound_forall s_pre s1 lo hi

let perm_upper_bound_forall (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              permutation s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v) ==>
              Seq.index s1 j <= v)
  = reveal_opaque (`%permutation) (permutation s_pre s1);
    assert (Seq.Properties.permutation int s_pre s1);
    Helpers.perm_unchanged_upper_bound_forall s_pre s1 lo hi
#pop-options

// Bridge from opaque permutation + partition ordering to select_spec
let quickselect_correctness (s0 s_final: Seq.seq int) (k: nat)
  : Lemma
    (requires k < Seq.length s0 /\
              Seq.length s_final == Seq.length s0 /\
              permutation s0 s_final /\
              (forall (i: nat). i < k ==> Seq.index s_final i <= Seq.index s_final k) /\
              (forall (i: nat). k < i /\ i < Seq.length s_final ==>
                Seq.index s_final k <= Seq.index s_final i))
    (ensures Seq.index s_final k == Spec.select_spec s0 k)
  = reveal_opaque (`%permutation) (permutation s0 s_final);
    Helpers.seq_perm_implies_is_perm s0 s_final;
    Correctness.pulse_correctness_hint s0 s_final k

#push-options "--z3rlimit 200 --ifuel 2 --fuel 2"
//SNIPPET_START: quickselect
fn quickselect
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v n == Seq.length s0 /\
    SZ.v n == A.length a /\
    SZ.v n > 0 /\
    SZ.v k < SZ.v n
  )
  returns result: int
  ensures exists* s_final.
    A.pts_to a s_final **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      SZ.v k < Seq.length s_final /\
      result == Seq.index s_final (SZ.v k) /\
      // Partition ordering: result is the k-th order statistic
      (forall (i: nat). i < SZ.v k /\ i < Seq.length s_final ==>
        Seq.index s_final i <= result) /\
      (forall (i: nat). SZ.v k < i /\ i < Seq.length s_final ==>
        result <= Seq.index s_final i) /\
      // Correctness: result is the k-th order statistic
      result == Spec.select_spec s0 (SZ.v k)
    )
//SNIPPET_END: quickselect
{
  let mut lo_ref: SZ.t = 0sz;
  let mut hi_ref: SZ.t = n;

  while (
    let vlo = !lo_ref;
    let vhi = !hi_ref;
    vhi -^ vlo >^ 1sz
  )
  invariant exists* vlo vhi s_cur.
    R.pts_to lo_ref vlo **
    R.pts_to hi_ref vhi **
    A.pts_to a s_cur **
    pure (
      SZ.v vlo <= SZ.v k /\
      SZ.v k < SZ.v vhi /\
      SZ.v vhi <= SZ.v n /\
      Seq.length s_cur == Seq.length s0 /\
      permutation s0 s_cur /\
      // Elements before vlo are <= all elements in [vlo, vhi)
      (forall (i j: nat). i < Seq.length s_cur /\ j < Seq.length s_cur /\
        i < SZ.v vlo /\ SZ.v vlo <= j /\ j < SZ.v vhi ==>
        Seq.index s_cur i <= Seq.index s_cur j) /\
      // Elements at or after vhi are >= all elements in [vlo, vhi)
      (forall (i j: nat). i < Seq.length s_cur /\ j < Seq.length s_cur /\
        SZ.v vlo <= i /\ i < SZ.v vhi /\ SZ.v vhi <= j ==>
        Seq.index s_cur i <= Seq.index s_cur j)
    )
  {
    let vlo = !lo_ref;
    let vhi = !hi_ref;

    with s_pre. assert (A.pts_to a s_pre);

    let p = partition_in_range a vlo vhi;

    with s_after. assert (A.pts_to a s_after);

    // Helper lemma calls: values rearranged within [vlo, vhi) preserve bounds
    perm_lower_bound_forall s_pre s_after (SZ.v vlo) (SZ.v vhi);
    perm_upper_bound_forall s_pre s_after (SZ.v vlo) (SZ.v vhi);

    if (k <^ p) {
      hi_ref := p;
    } else {
      if (p <^ k) {
        lo_ref := p +^ 1sz;
      } else {
        // k == p, found it
        lo_ref := k;
        hi_ref := k +^ 1sz;
      };
    };
  };

  let result = A.op_Array_Access a k;
  with s_final. assert (A.pts_to a s_final);
  quickselect_correctness s0 s_final (SZ.v k);
  result
}
#pop-options
