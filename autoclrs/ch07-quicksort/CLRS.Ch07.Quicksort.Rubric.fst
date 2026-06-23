(*
   CLRS Chapter 7: Quicksort — shared sorting-rubric instance.

   This module is intentionally separate from the extraction-facing int API in
   CLRS.Ch07.Quicksort.Impl.  It exposes the chapter sorting algorithm through
   the common array_sort typeclass, using the rubric's total-order comparator
   and monotonic tick counter.
*)
module CLRS.Ch07.Quicksort.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module QC = CLRS.Ch07.Quicksort.Complexity
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

let nat_smaller (n: nat) = i:nat{i < n}

let le_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.le (x `ord.TO.compare` y)

let lt_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.lt (x `ord.TO.compare` y)

let gt_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.gt (x `ord.TO.compare` y)

let smaller_than (#a: Type) (ord: TO.total_order a) (s: Seq.seq a) (pivot: a) : prop =
  forall (k: nat). {:pattern (Seq.index s k)}
    k < Seq.length s ==> le_ord ord (Seq.index s k) pivot

let larger_than (#a: Type) (ord: TO.total_order a) (s: Seq.seq a) (pivot: a) : prop =
  forall (k: nat). {:pattern (Seq.index s k)}
    k < Seq.length s ==> gt_ord ord (Seq.index s k) pivot

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) : GTot _ =
  Seq.swap s j i

let complexity_bounded_by_worst_case (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= QC.worst_case_comparisons n

let partition_pred (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (lo: nat) (j: nat) (i_plus_1: nat) (pivot: a)
: prop =
  forall (k: nat). {:pattern (Seq.index s k)}
    k < Seq.length s ==> (
      let kk = k + lo in
      (lo <= kk /\ kk < i_plus_1 ==> le_ord ord (Seq.index s k) pivot) /\
      (i_plus_1 <= kk /\ kk < j ==> gt_ord ord (Seq.index s k) pivot))

let rec sc_count_eq_sp_count (#a: eqtype) (x: a) (s: Seq.seq a)
  : Lemma (ensures SC.count x s == SP.count x s)
          (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else sc_count_eq_sp_count x (Seq.tail s)

let sc_permutation_of_sp_permutation (#a: eqtype) (s0 s1: Seq.seq a)
  : Lemma
    (requires SP.permutation a s0 s1)
    (ensures SC.permutation s0 s1)
  = let aux (x: a)
      : Lemma (SC.count x s0 == SC.count x s1)
      = sc_count_eq_sp_count x s0;
        sc_count_eq_sp_count x s1
    in
    FStar.Classical.forall_intro aux

let sp_permutation_refl (#a: eqtype) (s: Seq.seq a)
  : Lemma (ensures SP.permutation a s s)
  = ()

let sp_permutation_trans (#a: eqtype) (s0 s1 s2: Seq.seq a)
  : Lemma
    (requires SP.permutation a s0 s1 /\ SP.permutation a s1 s2)
    (ensures SP.permutation a s0 s2)
  = ()

let seq_swap_commute (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s))
  : Lemma (seq_swap s i j == seq_swap s j i)
  = let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji

let sp_permutation_swap (#a: eqtype) (s: Seq.seq a) (i j: nat_smaller (Seq.length s))
  : Lemma (ensures SP.permutation a s (seq_swap s i j))
  = if j <= i
    then SP.lemma_swap_permutes s j i
    else (SP.lemma_swap_permutes s i j; seq_swap_commute s i j)

let sp_append_permutations_3 (#a: eqtype)
  (s1 s2 s3 s1' s3': Seq.seq a)
  : Lemma
    (requires SP.permutation a s1 s1' /\ SP.permutation a s3 s3')
    (ensures SP.permutation a (Seq.append s1 (Seq.append s2 s3))
                             (Seq.append s1' (Seq.append s2 s3')))
  = sp_permutation_refl s2;
    SP.append_permutations s2 s3 s2 s3';
    SP.append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')

let le_ord_refl (#a: Type) (ord: TO.total_order a) (x: a)
  : Lemma (ensures le_ord ord x x)
  = ()

let gt_ord_implies_pivot_le (#a: Type) (ord: TO.total_order a) (x pivot: a)
  : Lemma
    (requires gt_ord ord x pivot)
    (ensures le_ord ord pivot x)
  = ()

let permutation_preserves_smaller_than (#a: eqtype) (ord: TO.total_order a)
  (s0 s1: Seq.seq a) (pivot: a)
  : Lemma
    (requires SP.permutation a s0 s1 /\ smaller_than ord s0 pivot)
    (ensures smaller_than ord s1 pivot)
  = let aux (k: nat{k < Seq.length s1})
      : Lemma (ensures le_ord ord (Seq.index s1 k) pivot)
      = let x = Seq.index s1 k in
        SP.seq_mem_k s1 k;
        assert (SP.mem x s1);
        assert (SP.count x s1 > 0);
        assert (SP.count x s0 == SP.count x s1);
        assert (SP.mem x s0);
        let i = SP.index_mem x s0 in
        assert (Seq.index s0 i == x);
        assert (le_ord ord (Seq.index s0 i) pivot)
    in
    FStar.Classical.forall_intro aux

let permutation_preserves_larger_than (#a: eqtype) (ord: TO.total_order a)
  (s0 s1: Seq.seq a) (pivot: a)
  : Lemma
    (requires SP.permutation a s0 s1 /\ larger_than ord s0 pivot)
    (ensures larger_than ord s1 pivot)
  = let aux (k: nat{k < Seq.length s1})
      : Lemma (ensures gt_ord ord (Seq.index s1 k) pivot)
      = let x = Seq.index s1 k in
        SP.seq_mem_k s1 k;
        assert (SP.mem x s1);
        assert (SP.count x s1 > 0);
        assert (SP.count x s0 == SP.count x s1);
        assert (SP.mem x s0);
        let i = SP.index_mem x s0 in
        assert (Seq.index s0 i == x);
        assert (gt_ord ord (Seq.index s0 i) pivot)
    in
    FStar.Classical.forall_intro aux

let sorted_singleton (#a: Type) (ord: TO.total_order a) (s: Seq.seq a)
  : Lemma
    (requires Seq.length s <= 1)
    (ensures SC.sorted #a #ord s)
  = ()

let sorted_append_with_pivot (#a: Type) (ord: TO.total_order a)
  (left pivot_seq right: Seq.seq a) (pivot: a)
  : Lemma
    (requires
      SC.sorted #a #ord left /\
      SC.sorted #a #ord pivot_seq /\
      SC.sorted #a #ord right /\
      Seq.length pivot_seq == 1 /\
      Seq.index pivot_seq 0 == pivot /\
      smaller_than ord left pivot /\
      larger_than ord right pivot)
    (ensures SC.sorted #a #ord (Seq.append left (Seq.append pivot_seq right)))
  = ()

let quicksort_complexity_step (n n_left n_right: nat)
  : Lemma
    (requires n > 1 /\ n_left + 1 + n_right == n)
    (ensures
      n - 1 + QC.worst_case_comparisons n_left + QC.worst_case_comparisons n_right
      <= QC.worst_case_comparisons n)
  = QC.partition_split_bounded n n_left

let op_Array_Access
  (#a: Type)
  (arr: A.array a)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq a))
  (#p: perm)
: stt a
    (requires A.pts_to_range arr l r #p s)
    (ensures fun res ->
      A.pts_to_range arr l r #p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= pts_to_range_index arr i #l #r #s #p

let op_Array_Assignment
  (#a: Type)
  (arr: A.array a)
  (i: SZ.t)
  (v: a)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq a))
: stt unit
    (requires A.pts_to_range arr l r s0)
    (ensures fun _ ->
      exists* s.
        A.pts_to_range arr l r s **
        pure (
          Seq.length s0 == r - l /\
          s == Seq.upd s0 (SZ.v i - l) v
        ))
= pts_to_range_upd arr i v #l #r

fn swap (#a: eqtype) (arr: A.array a) (i j: nat) (#l:nat{l <= i /\ l <= j}) (#r:nat{i < r /\ j < r})
  (#s0: Ghost.erased (Seq.seq a))
  requires A.pts_to_range arr l r s0
  ensures
    exists* s.
      A.pts_to_range arr l r s **
      pure (Seq.length s0 = r - l /\
            s == seq_swap s0 (i - l) (j - l) /\
            SP.permutation a s0 s)
{
  A.pts_to_range_prop arr;
  let vi = arr.(SZ.uint_to_t i);
  let vj = arr.(SZ.uint_to_t j);
  (arr.(SZ.uint_to_t i) <- vj);
  (arr.(SZ.uint_to_t j) <- vi);
  with s1. assert (A.pts_to_range arr l r s1);
  sp_permutation_swap s0 (i - l) (j - l);
  assert (pure (SP.permutation a s0 (seq_swap s0 (i - l) (j - l))))
}

fn partition_with_ticks (#a: eqtype)
  (arr: A.array a)
  (lo: nat)
  (hi: (hi:nat{lo < hi}))
  (#ord: erased (TO.total_order a))
  (ctr: SC.ticks_t)
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires (
    A.pts_to_range arr lo hi s0 **
    MR.pts_to ctr #1.0R c0 **
    pure (hi <= A.length arr /\ Seq.length s0 = hi - lo)
  )
  returns p: nat
  ensures exists* s (cf: nat).
    A.pts_to_range arr lo hi s **
    MR.pts_to ctr #1.0R cf **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo /\
      lo <= p /\ p < hi /\ hi <= A.length arr /\
      (forall (k:nat). k < Seq.length s ==> (
        let kk = k + lo in
        (lo <= kk /\ kk < p ==> le_ord ord (Seq.index s k) (Seq.index s (p - lo))) /\
        (kk == p ==> Seq.index s k == Seq.index s (p - lo)) /\
        (p < kk /\ kk < hi ==> gt_ord ord (Seq.index s k) (Seq.index s (p - lo)))
      )) /\
      SP.permutation a s0 s /\
      cf == reveal c0 + (hi - lo - 1)
    )
{
  let pivot = arr.(SZ.uint_to_t (hi - 1));
  let mut i_plus_1 = lo;
  let mut j = lo;

  while (let vj = !j; vj < hi - 1)
    invariant exists* s (vc: nat). (
      A.pts_to_range arr lo hi s **
      MR.pts_to ctr #1.0R vc **
      live i_plus_1 ** live j **
      pure (
        lo <= !j /\ !j <= hi - 1 /\
        lo <= !i_plus_1 /\ !i_plus_1 <= !j /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot /\
        partition_pred ord s lo (!j) (!i_plus_1) pivot /\
        SP.permutation a s0 s /\
        vc == reveal c0 + (!j - lo)
      ))
  decreases (hi - !j)
  {
    let vj = !j;
    let aj = arr.(SZ.uint_to_t vj);

    let cmp = iord aj pivot;

    if (O.le cmp) {
      let vi_plus_1 = !i_plus_1;
      swap arr vi_plus_1 vj;
      i_plus_1 := vi_plus_1 + 1;
      j := vj + 1;
    } else {
      j := vj + 1;
    };
  };

  let vi_plus_1 = !i_plus_1;
  swap arr vi_plus_1 (hi - 1);

  vi_plus_1
}

fn partition_wrapper_with_ticks (#a: eqtype)
  (arr: A.array a)
  (lo: nat)
  (hi: (hi:nat{lo < hi}))
  (#ord: erased (TO.total_order a))
  (ctr: SC.ticks_t)
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires (
    A.pts_to_range arr lo hi s0 **
    MR.pts_to ctr #1.0R c0 **
    pure (hi <= A.length arr /\ Seq.length s0 = hi - lo)
  )
  returns p: nat
  ensures exists* s1 s_pivot s2 (cf: nat). (
    A.pts_to_range arr lo p s1 **
    A.pts_to_range arr p (p+1) s_pivot **
    A.pts_to_range arr (p+1) hi s2 **
    MR.pts_to ctr #1.0R cf **
    pure (
      lo <= p /\ p < hi /\ hi <= A.length arr /\
      Seq.length s1 == p - lo /\ Seq.length s_pivot == 1 /\ Seq.length s2 == hi - (p+1) /\
      smaller_than ord s1 (Seq.index s_pivot 0) /\
      larger_than ord s2 (Seq.index s_pivot 0) /\
      SP.permutation a s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      cf == reveal c0 + (hi - lo - 1)
    ))
{
  let p = partition_with_ticks arr lo hi #ord ctr iord #s0 #c0;
  with s. assert (A.pts_to_range arr lo hi s);
  with cf_partition. assert (MR.pts_to ctr #1.0R cf_partition);

  pts_to_range_split arr lo p hi;
  with s_left. assert (A.pts_to_range arr lo p s_left);
  with s_right_plus. assert (A.pts_to_range arr p hi s_right_plus);

  pts_to_range_split arr p (p+1) hi;
  with s_pivot. assert (A.pts_to_range arr p (p+1) s_pivot);
  with s_right. assert (A.pts_to_range arr (p+1) hi s_right);

  p
}

fn rec quicksort_core (#a: eqtype)
  (arr: A.array a)
  (lo: nat)
  (hi: (hi:nat{lo <= hi}))
  (#ord: erased (TO.total_order a))
  (ctr: SC.ticks_t)
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires (
    A.pts_to_range arr lo hi s0 **
    MR.pts_to ctr #1.0R c0 **
    pure (hi <= A.length arr /\ Seq.length s0 = hi - lo)
  )
  ensures exists* s (cf: nat).
    A.pts_to_range arr lo hi s **
    MR.pts_to ctr #1.0R cf **
    pure (
      SC.sorted #a #ord s /\
      SP.permutation a s0 s /\
      complexity_bounded_by_worst_case cf (reveal c0) (hi - lo)
    )
{
  if (lo < hi) {
    if (hi <= lo + 1) {
      sorted_singleton ord s0;
      sp_permutation_refl s0;
      ()
    } else {
      let p = partition_wrapper_with_ticks arr lo hi #ord ctr iord #s0 #c0;

      with s_left. assert (A.pts_to_range arr lo p s_left);
      with s_pivot. assert (A.pts_to_range arr p (p+1) s_pivot);
      with s_right. assert (A.pts_to_range arr (p+1) hi s_right);
      with c_after_partition. assert (MR.pts_to ctr #1.0R c_after_partition);

      quicksort_core arr lo p #ord ctr iord #s_left #c_after_partition;
      with s_left'. assert (A.pts_to_range arr lo p s_left');
      with c_after_left. assert (MR.pts_to ctr #1.0R c_after_left);

      quicksort_core arr (p+1) hi #ord ctr iord #s_right #c_after_left;
      with s_right'. assert (A.pts_to_range arr (p+1) hi s_right');
      with c_final. assert (MR.pts_to ctr #1.0R c_final);

      permutation_preserves_smaller_than ord s_left s_left' (Seq.index s_pivot 0);
      permutation_preserves_larger_than ord s_right s_right' (Seq.index s_pivot 0);
      sorted_singleton ord s_pivot;
      sorted_append_with_pivot ord s_left' s_pivot s_right' (Seq.index s_pivot 0);
      sp_append_permutations_3 s_left s_pivot s_right s_left' s_right';

      pts_to_range_join arr p (p+1) hi;
      pts_to_range_join arr lo p hi;

      quicksort_complexity_step (hi - lo) (p - lo) (hi - (p + 1));
      ()
    }
  } else {
    sorted_singleton ord s0;
    sp_permutation_refl s0;
    ()
  }
}

fn quicksort_sort (#a: eqtype)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s: erased (Seq.seq a))
  (#i: erased nat)
  requires arr |-> s ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
  ensures exists* s' ticks.
    arr |-> s' **
    MR.pts_to ctr #1.0R ticks **
    pure (SC.sorted #a #ord s' /\
          SC.permutation s s' /\
          ticks <= reveal i + QC.worst_case_comparisons (Seq.length s))
{
  A.pts_to_len arr;
  A.pts_to_range_intro arr 1.0R s;
  quicksort_core arr 0 (SZ.v len) #ord ctr iord #s #i;
  with s_out. assert (A.pts_to_range arr 0 (A.length arr) s_out);
  with cf. assert (MR.pts_to ctr #1.0R cf);
  sc_permutation_of_sp_permutation s s_out;
  assert (pure (cf <= reveal i + QC.worst_case_comparisons (Seq.length s)));
  A.pts_to_range_elim arr 1.0R s_out
}

instance quicksort_array_sort (a: eqtype) : SC.array_sort a QC.worst_case_comparisons = {
  sort = quicksort_sort #a;
}
