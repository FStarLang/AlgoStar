(*
   CLRS Chapter 9.2: RANDOMIZED-SELECT (Quickselect) — Pulse Implementation

   Finds the k-th smallest element using partition-based selection.
   Algorithm: pick last element as pivot, partition, recurse on relevant half.

   Complexity: O(n²) worst case (deterministic pivot; O(n) expected requires
   randomized pivot, which is not implemented here).

   Every comparison is ghost-ticked; there is ONE version of each function
   that proves both correctness and complexity.

   Verification:
   - NO admits, NO assumes
   - Permutation: output array is a rearrangement of input
   - Partition ordering: elements [0,k) ≤ a[k] and elements (k,n) ≥ a[k]
   - Correctness: result == select_spec s0 k (the k-th order statistic)
   - Complexity: total comparisons ≤ qs_cost(n) ≤ n²
*)

module CLRS.Ch09.Quickselect.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open FStar.Mul
open CLRS.Common.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical
module QSpec = CLRS.Ch09.Quickselect.Spec
module Lemmas = CLRS.Ch09.Quickselect.Lemmas
module PSSLemmas = CLRS.Ch09.PartialSelectionSort.Lemmas
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec
module GR = Pulse.Lib.GhostReference
module QC = CLRS.Ch09.Quickselect.Complexity

// permutation, unchanged_outside, partition_ordered are already defined in the .fsti
let permutation_same_length = QSpec.permutation_same_length
let permutation_refl = QSpec.permutation_refl
let compose_permutations = QSpec.compose_permutations
let swap_is_permutation = QSpec.swap_is_permutation

// ========== In-place partition — ticks once per comparison ==========

#push-options "--z3rlimit 10 --ifuel 2 --fuel 2"
//SNIPPET_START: partition_in_range
fn partition_in_range
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t)
  (hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v lo < SZ.v hi /\
      SZ.v hi <= Seq.length s0 /\
      Seq.length s0 == A.length a
    )
  returns pivot_pos: SZ.t
  ensures exists* s1 (cf: nat).
    A.pts_to a s1 ** GR.pts_to ctr cf **
    pure (
      Seq.length s1 == Seq.length s0 /\
      SZ.v lo <= SZ.v pivot_pos /\
      SZ.v pivot_pos < SZ.v hi /\
      permutation s0 s1 /\
      partition_ordered s1 (SZ.v lo) (SZ.v pivot_pos) (SZ.v hi) /\
      unchanged_outside s0 s1 (SZ.v lo) (SZ.v hi) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v hi - SZ.v lo - 1
    )
//SNIPPET_END: partition_in_range
{
  let hi_m1 = hi -^ 1sz;
  let pivot = A.op_Array_Access a hi_m1;

  let mut i_ref: SZ.t = lo;
  let mut j_ref: SZ.t = lo;

  while (
    let vj = !j_ref;
    vj <^ hi_m1
  )
  invariant exists* vi vj s_cur (vc: nat).
    R.pts_to i_ref vi **
    R.pts_to j_ref vj **
    A.pts_to a s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v lo <= SZ.v vi /\
      SZ.v vi <= SZ.v vj /\
      SZ.v vj <= SZ.v hi_m1 /\
      Seq.length s_cur == Seq.length s0 /\
      permutation s0 s_cur /\
      Seq.index s_cur (SZ.v hi_m1) == pivot /\
      (forall (idx: nat). idx < Seq.length s_cur ==>
        (SZ.v lo <= idx /\ idx < SZ.v vi) ==> Seq.index s_cur idx <= pivot) /\
      (forall (idx: nat). idx < Seq.length s_cur ==>
        (SZ.v vi <= idx /\ idx < SZ.v vj) ==> Seq.index s_cur idx > pivot) /\
      unchanged_outside s0 s_cur (SZ.v lo) (SZ.v hi) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vj - SZ.v lo
    )
  decreases (SZ.v hi_m1 `Prims.op_Subtraction` SZ.v !j_ref)
  {
    let vj = !j_ref;
    let vi = !i_ref;

    with s_pre. assert (A.pts_to a s_pre);

    let aj = A.op_Array_Access a vj;
    let ai = A.op_Array_Access a vi;

    tick ctr;
    let should_swap = (aj <= pivot);

    j_ref := vj +^ 1sz;

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

// ========== Helper lemma wrappers ==========

#push-options "--z3rlimit 20 --split_queries always"
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
  = reveal_opaque (`%QSpec.permutation) (QSpec.permutation s_pre s1);
    assert (Seq.Properties.permutation int s_pre s1);
    Lemmas.perm_unchanged_lower_bound_forall s_pre s1 lo hi

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
  = reveal_opaque (`%QSpec.permutation) (QSpec.permutation s_pre s1);
    assert (Seq.Properties.permutation int s_pre s1);
    Lemmas.perm_unchanged_upper_bound_forall s_pre s1 lo hi
#pop-options

let quickselect_correctness (s0 s_final: Seq.seq int) (k: nat)
  : Lemma
    (requires k < Seq.length s0 /\
              Seq.length s_final == Seq.length s0 /\
              permutation s0 s_final /\
              (forall (i: nat). i < k ==> Seq.index s_final i <= Seq.index s_final k) /\
              (forall (i: nat). k < i /\ i < Seq.length s_final ==>
                Seq.index s_final k <= Seq.index s_final i))
    (ensures Seq.index s_final k == PSSSpec.select_spec s0 k)
  = reveal_opaque (`%QSpec.permutation) (QSpec.permutation s0 s_final);
    Lemmas.seq_perm_implies_is_perm s0 s_final;
    PSSLemmas.pulse_correctness_hint s0 s_final k

// ========== Quickselect — single function, correctness + complexity ==========

#push-options "--z3rlimit 20 --ifuel 2 --fuel 2"
//SNIPPET_START: quickselect
fn quickselect
  (a: A.array int)
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
      SZ.v k < SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      SZ.v k < Seq.length s_final /\
      result == Seq.index s_final (SZ.v k) /\
      (forall (i: nat). i < SZ.v k /\ i < Seq.length s_final ==>
        Seq.index s_final i <= result) /\
      (forall (i: nat). SZ.v k < i /\ i < Seq.length s_final ==>
        result <= Seq.index s_final i) /\
      result == PSSSpec.select_spec s0 (SZ.v k) /\
      complexity_bounded_quickselect cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: quickselect
{
  let mut lo_ref: SZ.t = 0sz;
  let mut hi_ref: SZ.t = n;
  let mut go: bool = (n >^ 1sz);

  while (!go)
  invariant exists* vlo vhi s_cur (vc: nat) vgo.
    R.pts_to lo_ref vlo **
    R.pts_to hi_ref vhi **
    R.pts_to go vgo **
    A.pts_to a s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v vlo <= SZ.v k /\
      SZ.v k < SZ.v vhi /\
      SZ.v vhi <= SZ.v n /\
      Seq.length s_cur == Seq.length s0 /\
      permutation s0 s_cur /\
      (vgo ==> SZ.v vhi - SZ.v vlo > 1) /\
      (not vgo ==> SZ.v vhi - SZ.v vlo <= 1) /\
      (forall (i j: nat). i < Seq.length s_cur /\ j < Seq.length s_cur /\
        i < SZ.v vlo /\ SZ.v vlo <= j /\ j < SZ.v vhi ==>
        Seq.index s_cur i <= Seq.index s_cur j) /\
      (forall (i j: nat). i < Seq.length s_cur /\ j < Seq.length s_cur /\
        SZ.v vlo <= i /\ i < SZ.v vhi /\ SZ.v vhi <= j ==>
        Seq.index s_cur i <= Seq.index s_cur j) /\
      vc >= reveal c0 /\
      vc - reveal c0 + QC.qs_cost (SZ.v vhi - SZ.v vlo) <= QC.qs_cost (SZ.v n)
    )
  decreases (SZ.v !hi_ref `Prims.op_Subtraction` SZ.v !lo_ref)
  {
    let vlo = !lo_ref;
    let vhi = !hi_ref;

    with s_pre. assert (A.pts_to a s_pre);

    let p = partition_in_range a vlo vhi ctr;

    with s_after. assert (A.pts_to a s_after);

    perm_lower_bound_forall s_pre s_after (SZ.v vlo) (SZ.v vhi);
    perm_upper_bound_forall s_pre s_after (SZ.v vlo) (SZ.v vhi);

    QC.qs_cost_unfold (SZ.v vhi - SZ.v vlo);

    if (k <^ p) {
      QC.qs_cost_monotone (SZ.v p - SZ.v vlo) (SZ.v vhi - SZ.v vlo - 1);
      hi_ref := p;
      go := (p >^ vlo +^ 1sz);
    } else {
      if (p <^ k) {
        QC.qs_cost_monotone (SZ.v vhi - SZ.v p - 1) (SZ.v vhi - SZ.v vlo - 1);
        lo_ref := p +^ 1sz;
        go := (vhi >^ p +^ 1sz +^ 1sz);
      } else {
        QC.qs_cost_monotone 1 (SZ.v vhi - SZ.v vlo - 1);
        lo_ref := k;
        hi_ref := k +^ 1sz;
        go := false;
      };
    };
  };

  let result = A.op_Array_Access a k;
  with s_final. assert (A.pts_to a s_final);
  quickselect_correctness s0 s_final (SZ.v k);
  result
}
#pop-options
