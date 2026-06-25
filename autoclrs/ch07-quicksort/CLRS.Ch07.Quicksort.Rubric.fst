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
open Pulse.Lib.TotalOrder

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

let rec count (#a: Type) {| TO.total_order a |} (x: a) (s: Seq.seq a)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else if Seq.head s ==? x
    then 1 + count x (Seq.tail s)
    else count x (Seq.tail s)

let permutation (#a: Type) {| TO.total_order a |} (s0 s1: Seq.seq a) =
  forall (x: a). count x s0 == count x s1

let mem (#a: Type) {| TO.total_order a |} (x: a) (s: Seq.seq a) =
  count x s > 0

let rec index_mem (#a: Type) {| TO.total_order a |} (x: a) (s: Seq.seq a)
  : Pure nat
      (requires mem x s)
      (ensures fun i -> i < Seq.length s /\ Seq.index s i == x)
      (decreases (Seq.length s))
  = if Seq.head s ==? x then 0 else 1 + index_mem x (Seq.tail s)

let rec seq_mem_k (#a: Type) {| TO.total_order a |} (s: Seq.seq a) (k: nat{k < Seq.length s})
  : Lemma (ensures mem (Seq.index s k) s)
          (decreases (Seq.length s))
  = if k = 0 then () else seq_mem_k (Seq.tail s) (k - 1)

let rec count_eq (#a: Type) {| ord: TO.total_order a |} (x: a) (s: Seq.seq a)
  : Lemma (ensures count x s == SC.count x s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s ==? x <==> Seq.head s == x);
      count_eq x (Seq.tail s)
    )

let is_permutation_to_sc (#a: Type) {| ord: TO.total_order a |} (s0 s1: Seq.seq a)
  : Lemma
    (requires permutation s0 s1)
    (ensures SC.permutation s0 s1)
  = let aux (x: a)
      : Lemma (SC.count x s0 == SC.count x s1)
      = count_eq x s0;
        count_eq x s1
    in
    FStar.Classical.forall_intro aux

let permutation_refl (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (ensures permutation s s)
  = ()

let permutation_trans (#a: Type) {| ord: TO.total_order a |} (s0 s1 s2: Seq.seq a)
  : Lemma
    (requires permutation s0 s1 /\ permutation s1 s2)
    (ensures permutation s0 s2)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec count_append (#a: Type) {| ord: TO.total_order a |} (x: a) (s1 s2: Seq.seq a)
  : Lemma (ensures count x (Seq.append s1 s2) == count x s1 + count x s2)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      SP.lemma_head_append s1 s2;
      SP.lemma_tail_append s1 s2;
      SP.lemma_append_cons s1 s2;
      count_append x (Seq.tail s1) s2;
      if Seq.head s1 ==? x then (
        assert (count x (Seq.append s1 s2) == 1 + count x (Seq.append (Seq.tail s1) s2));
        assert (count x s1 == 1 + count x (Seq.tail s1));
        assert (count x (Seq.append s1 s2) == count x s1 + count x s2)
      ) else (
        assert (count x (Seq.append s1 s2) == count x (Seq.append (Seq.tail s1) s2));
        assert (count x s1 == count x (Seq.tail s1));
        assert (count x (Seq.append s1 s2) == count x s1 + count x s2)
      )
    )
#pop-options

let seq_swap_commute (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s))
  : Lemma (seq_swap s i j == seq_swap s j i)
  = let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji

let rec upd_count (#a: Type) {| TO.total_order a |} (s: Seq.seq a) (i: nat) (x: a) (z: a)
   : Lemma
     (requires i < Seq.length s)
     (ensures (
       if Seq.index s i ==? x
       then Seq.upd s i x == s
       else (
         if z ==? x
         then count x (Seq.upd s i x) == count x s + 1
         else if z ==? Seq.index s i
         then count z (Seq.upd s i x) == count z s - 1
         else count z (Seq.upd s i x) == count z s)
     ))
     (decreases Seq.length s)
     [SMTPat (count z (Seq.upd s i x))]
   = if Seq.index s i ==? x
     then assert (Seq.equal (Seq.upd s i x) s)
     else (
       if i = 0 then ()
       else upd_count (Seq.tail s) (i - 1) x z
     )

let permutation_swap (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a) (i j: nat_smaller (Seq.length s))
  : Lemma (ensures permutation s (seq_swap s i j))
  = let x = Seq.index s i in
    let y = Seq.index s j in
    if i = j then assert (Seq.equal (seq_swap s i j) s)
    else if x ==? y then assert (Seq.equal (seq_swap s i j) s)
    else
      let s1 = Seq.upd s i y in
      let aux (z: a) : Lemma (count z s == count z (seq_swap s i j)) =
        Seq.lemma_index_upd2 s i y j;
        assert (Seq.index s1 j == y);
        upd_count s i y z;
        upd_count s1 j x z
      in
      FStar.Classical.forall_intro aux

let append_permutations (#a: Type) {| ord: TO.total_order a |} (s1 s2 s1' s2': Seq.seq a)
  : Lemma
    (requires permutation s1 s1' /\ permutation s2 s2')
    (ensures permutation (Seq.append s1 s2) (Seq.append s1' s2'))
  = let aux (x: a) : Lemma (count x (Seq.append s1 s2) == count x (Seq.append s1' s2')) =
      count_append x s1 s2;
      count_append x s1' s2'
    in
    FStar.Classical.forall_intro aux

let append_permutations_3 (#a: Type) {| ord: TO.total_order a |}
  (s1 s2 s3 s1' s3': Seq.seq a)
  : Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3))
                         (Seq.append s1' (Seq.append s2 s3')))
  = permutation_refl s2;
    append_permutations s2 s3 s2 s3';
    append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')

let le_ord_refl (#a: Type) (ord: TO.total_order a) (x: a)
  : Lemma (ensures le_ord ord x x)
  = ()

let gt_ord_implies_pivot_le (#a: Type) (ord: TO.total_order a) (x pivot: a)
  : Lemma
    (requires gt_ord ord x pivot)
    (ensures le_ord ord pivot x)
  = ()

let permutation_preserves_smaller_than (#a: Type) (ord: TO.total_order a)
  (s0 s1: Seq.seq a) (pivot: a)
  : Lemma
    (requires permutation #a #ord s0 s1 /\ smaller_than ord s0 pivot)
    (ensures smaller_than ord s1 pivot)
  = let aux (k: nat{k < Seq.length s1})
      : Lemma (ensures le_ord ord (Seq.index s1 k) pivot)
      = let x = Seq.index s1 k in
        seq_mem_k #a #ord s1 k;
        assert (mem #a #ord x s1);
        assert (count #a #ord x s1 > 0);
        assert (count #a #ord x s0 == count #a #ord x s1);
        assert (mem #a #ord x s0);
        let i = index_mem #a #ord x s0 in
        assert (Seq.index s0 i == x);
        assert (le_ord ord (Seq.index s0 i) pivot)
    in
    FStar.Classical.forall_intro aux

let permutation_preserves_larger_than (#a: Type) (ord: TO.total_order a)
  (s0 s1: Seq.seq a) (pivot: a)
  : Lemma
    (requires permutation #a #ord s0 s1 /\ larger_than ord s0 pivot)
    (ensures larger_than ord s1 pivot)
  = let aux (k: nat{k < Seq.length s1})
      : Lemma (ensures gt_ord ord (Seq.index s1 k) pivot)
      = let x = Seq.index s1 k in
        seq_mem_k #a #ord s1 k;
        assert (mem #a #ord x s1);
        assert (count #a #ord x s1 > 0);
        assert (count #a #ord x s0 == count #a #ord x s1);
        assert (mem #a #ord x s0);
        let i = index_mem #a #ord x s0 in
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

fn swap (#a: Type0) (#ord: erased (TO.total_order a)) (arr: A.array a) (i j: nat) (#l:nat{l <= i /\ l <= j}) (#r:nat{i < r /\ j < r})
  (#s0: Ghost.erased (Seq.seq a))
  requires A.pts_to_range arr l r s0
  ensures
    exists* s.
      A.pts_to_range arr l r s **
      pure (Seq.length s0 = r - l /\
            s == seq_swap s0 (i - l) (j - l) /\
            permutation #a #ord s0 s)
{
  A.pts_to_range_prop arr;
  let vi = arr.(SZ.uint_to_t i);
  let vj = arr.(SZ.uint_to_t j);
  (arr.(SZ.uint_to_t i) <- vj);
  (arr.(SZ.uint_to_t j) <- vi);
  with s1. assert (A.pts_to_range arr l r s1);
  permutation_swap #a #ord s0 (i - l) (j - l);
  assert (pure (permutation #a #ord s0 (seq_swap s0 (i - l) (j - l))))
}

fn partition_with_ticks (#a: Type0)
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
      permutation #a #ord s0 s /\
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
        Seq.index s (hi - 1 - lo) == pivot /\
        partition_pred ord s lo (!j) (!i_plus_1) pivot /\
        permutation #a #ord s0 s /\
        vc == reveal c0 + (!j - lo)
      ))
  decreases (hi - !j)
  {
    let vj = !j;
    let aj = arr.(SZ.uint_to_t vj);

    let cmp = iord aj pivot;

    if (O.le cmp) {
      let vi_plus_1 = !i_plus_1;
      swap #a #ord arr vi_plus_1 vj;
      i_plus_1 := vi_plus_1 + 1;
      j := vj + 1;
    } else {
      j := vj + 1;
    };
  };

  let vi_plus_1 = !i_plus_1;
  swap #a #ord arr vi_plus_1 (hi - 1);

  vi_plus_1
}

fn partition_wrapper_with_ticks (#a: Type0)
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
      permutation #a #ord s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
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

fn rec quicksort_core (#a: Type0)
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
      permutation #a #ord s0 s /\
      complexity_bounded_by_worst_case cf (reveal c0) (hi - lo)
    )
{
  if (lo < hi) {
    if (hi <= lo + 1) {
      sorted_singleton ord s0;
      permutation_refl #a #ord s0;
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
      append_permutations_3 #a #ord s_left s_pivot s_right s_left' s_right';

      pts_to_range_join arr p (p+1) hi;
      pts_to_range_join arr lo p hi;

      quicksort_complexity_step (hi - lo) (p - lo) (hi - (p + 1));
      ()
    }
  } else {
    sorted_singleton ord s0;
    permutation_refl #a #ord s0;
    ()
  }
}

fn quicksort_sort (#a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s: erased (Seq.seq a))
  (#i: erased nat)
  requires arr |-> s ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
  ensures exists* s' (ticks: nat).
    arr |-> s' **
    MR.pts_to ctr #1.0R ticks **
    pure (SC.sorted #a #ord s' /\
          SC.permutation s s' /\
          ticks <= reveal i + Seq.length s * (Seq.length s - 1) / 2)
{
  A.pts_to_len arr;
  A.pts_to_range_intro arr 1.0R s;
  quicksort_core arr 0 (SZ.v len) #ord ctr iord #s #i;
  with s_out. assert (A.pts_to_range arr 0 (A.length arr) s_out);
  with cf. assert (MR.pts_to ctr #1.0R cf);
  is_permutation_to_sc #a #ord s s_out;
  QC.worst_case_bound (Seq.length s);
  assert (pure (QC.worst_case_comparisons (Seq.length s) <= Seq.length s * (Seq.length s - 1) / 2));
  assert (pure (cf <= reveal i + Seq.length s * (Seq.length s - 1) / 2));
  A.pts_to_range_elim arr 1.0R s_out
}

fn quicksort_sort_poly (a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
  requires arr |-> s ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
  ensures exists* s' (ticks: nat).
    arr |-> s' **
    MR.pts_to ctr #1.0R ticks **
    pure (SC.sorted #a #ord s' /\
          SC.permutation s s' /\
          ticks <= reveal i + Seq.length s * (Seq.length s - 1) / 2)
{
  quicksort_sort #a arr len ctr #ord iord #s #i
}

instance quicksort_array_sort : SC.array_sort (fun n -> n * (n - 1) / 2) = {
  sort = quicksort_sort_poly;
}
