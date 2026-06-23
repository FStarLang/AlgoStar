(*
   CLRS Chapter 2: merge sort as an instance of the shared sorting rubric.

   This module is separate from the extraction-facing int implementation.  It is
   a generic top-down merge sort whose only element comparisons go through the
   shared instrumented comparator, and whose final tick count is padded to the
   ch02 merge-sort recurrence budget.
*)
module CLRS.Ch02.MergeSort.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.TotalOrder
open Pulse.Lib.Array
open Pulse.Lib.Array.PtsToRange

module A = Pulse.Lib.Array
module MS = CLRS.Ch02.MergeSort.Complexity
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module R = Pulse.Lib.Reference
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder
module V = Pulse.Lib.Vec

let merge_sort_comparisons (n: nat) : nat =
  if n = 0 then 0 else MS.merge_sort_ops n

let range_len (lo hi: SZ.t) : nat =
  if SZ.v lo <= SZ.v hi then SZ.v hi - SZ.v lo else 0

let le_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.le (x `ord.TO.compare` y)

let rec count (#t: Type) {| total_order t |} (x: t) (s: Seq.seq t)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else if Seq.head s ==? x
    then 1 + count x (Seq.tail s)
    else count x (Seq.tail s)

let permutation (#t: Type) {| total_order t |} (s0 s1: Seq.seq t) =
  forall (x: t). count x s0 == count x s1

let permutation_trans (#t: Type) {| total_order t |} (s0 s1 s2: Seq.seq t)
  : Lemma (requires permutation s0 s1 /\ permutation s1 s2)
          (ensures permutation s0 s2)
  = let aux (x: t) : Lemma (count x s0 == count x s2) = ()
    in
    FStar.Classical.forall_intro aux

let sorted (#t: Type) {| total_order t |} (s: Seq.seq t) =
  forall (i j: nat). {:pattern (Seq.index s i); (Seq.index s j)}
    i <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j

let rec count_eq (#a: Type) {| ord: TO.total_order a |} (x: a) (s: Seq.seq a)
  : Lemma (ensures count x s == SC.count x s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s ==? x <==> Seq.head s == x);
      count_eq x (Seq.tail s)
    )

let is_permutation_to_sc (#a: Type) {| ord: TO.total_order a |} (s0 s1: Seq.seq a)
  : Lemma (requires permutation s0 s1)
          (ensures SC.permutation s0 s1)
  = let aux (x: a)
      : Lemma (SC.count x s0 == SC.count x s1)
      = count_eq x s0;
        count_eq x s1
    in
    FStar.Classical.forall_intro aux

let is_sorted_to_sc (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (requires sorted s)
          (ensures SC.sorted #a #ord s)
  = ()

ghost
fn set_ticks (ctr: SC.ticks_t) (#cur: erased nat) (target: nat)
  requires MR.pts_to ctr #1.0R cur
  requires pure (reveal cur <= target)
  ensures MR.pts_to ctr #1.0R target
{
  MR.update ctr target
}

let rec seq_merge (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Tot (Seq.seq a) (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then s2
    else if Seq.length s2 = 0 then s1
    else
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      if h1 <=? h2
      then Seq.cons h1 (seq_merge (Seq.tail s1) s2)
      else Seq.cons h2 (seq_merge s1 (Seq.tail s2))

let all_ge (#a: Type) {| ord: TO.total_order a |} (v: a) (s: Seq.seq a) : prop =
  forall (i: nat). i < Seq.length s ==> v <=? Seq.index s i

let small_sorted (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (requires Seq.length s <= 1)
          (ensures sorted #a #ord s)
  = ()

let permutation_refl (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (ensures permutation #a #ord s s)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let rec count_append (#a: Type) {| ord: TO.total_order a |} (x: a) (s1 s2: Seq.seq a)
  : Lemma (ensures count x (Seq.append s1 s2) == count x s1 + count x s2)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal (Seq.append s1 s2) s2)
    )
    else (
      SeqP.lemma_head_append s1 s2;
      SeqP.lemma_tail_append s1 s2;
      SeqP.lemma_append_cons s1 s2;
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

let count_empty (#a: Type) {| ord: TO.total_order a |} (x: a) (s: Seq.seq a)
  : Lemma (requires Seq.length s = 0)
          (ensures count x s == 0)
  = ()

let count_cons (#a: Type) {| ord: TO.total_order a |} (x h: a) (t: Seq.seq a)
  : Lemma (ensures count x (Seq.cons h t) == (if h ==? x then 1 else 0) + count x t)
  = assert (Seq.head (Seq.cons h t) == h);
    assert (Seq.tail (Seq.cons h t) `Seq.equal` t)

#pop-options

let rec seq_merge_length (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (ensures Seq.length (seq_merge s1 s2) == Seq.length s1 + Seq.length s2)
          (decreases (Seq.length s1 + Seq.length s2))
          [SMTPat (Seq.length (seq_merge s1 s2))]
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <=? Seq.head s2 then seq_merge_length (Seq.tail s1) s2
    else seq_merge_length s1 (Seq.tail s2)

let rec seq_merge_count (#a: Type) {| ord: TO.total_order a |} (x: a) (s1 s2: Seq.seq a)
  : Lemma (ensures count x (seq_merge s1 s2) == count x s1 + count x s2)
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then (
      count_empty x s1;
      assert (seq_merge s1 s2 == s2)
    )
    else if Seq.length s2 = 0 then (
      count_empty x s2;
      assert (seq_merge s1 s2 == s1)
    )
    else
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      if h1 <=? h2 then (
        seq_merge_count x (Seq.tail s1) s2;
        count_cons x h1 (seq_merge (Seq.tail s1) s2)
      ) else (
        seq_merge_count x s1 (Seq.tail s2);
        count_cons x h2 (seq_merge s1 (Seq.tail s2))
      )

let seq_merge_permutation (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (ensures permutation #a #ord (Seq.append s1 s2) (seq_merge s1 s2))
  = let aux (x: a) : Lemma (count x (Seq.append s1 s2) == count x (seq_merge s1 s2)) =
      count_append x s1 s2;
      seq_merge_count x s1 s2
    in
    FStar.Classical.forall_intro aux

let sorted_all_ge_head (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (requires Seq.length s > 0 /\ sorted #a #ord s)
          (ensures all_ge #a #ord (Seq.head s) s)
  = ()

let sorted_tail (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (requires Seq.length s > 0 /\ sorted #a #ord s)
          (ensures sorted #a #ord (Seq.tail s))
  = ()

let sorted_cons (#a: Type) {| ord: TO.total_order a |} (h: a) (t: Seq.seq a)
  : Lemma (requires sorted #a #ord t /\ all_ge #a #ord h t)
          (ensures sorted #a #ord (Seq.cons h t))
  = ()

let rec seq_merge_all_ge (#a: Type) {| ord: TO.total_order a |} (v: a) (s1 s2: Seq.seq a)
  : Lemma (requires all_ge #a #ord v s1 /\ all_ge #a #ord v s2)
          (ensures all_ge #a #ord v (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <=? Seq.head s2 then seq_merge_all_ge v (Seq.tail s1) s2
    else seq_merge_all_ge v s1 (Seq.tail s2)

let rec seq_merge_sorted (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (requires sorted #a #ord s1 /\ sorted #a #ord s2)
          (ensures sorted #a #ord (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      sorted_tail s1;
      sorted_tail s2;
      if h1 <=? h2 then (
        seq_merge_sorted (Seq.tail s1) s2;
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        seq_merge_all_ge h1 (Seq.tail s1) s2;
        sorted_cons h1 (seq_merge (Seq.tail s1) s2)
      ) else (
        seq_merge_sorted s1 (Seq.tail s2);
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        seq_merge_all_ge h2 s1 (Seq.tail s2);
        sorted_cons h2 (seq_merge s1 (Seq.tail s2))
      )

let seq_merge_head_right (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (requires Seq.length s1 = 0 /\ Seq.length s2 > 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s2)
  = ()

let seq_merge_head_left (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 = 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s1)
  = ()

let seq_merge_take_left (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                    Seq.head s1 <=? Seq.head s2)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge (Seq.tail s1) s2)
  = assert (Seq.head (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)) == Seq.head s1);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)))
                      (seq_merge (Seq.tail s1) s2))

let seq_merge_take_right (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                    ~(Seq.head s1 <=? Seq.head s2))
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge s1 (Seq.tail s2))
  = assert (Seq.head (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))) == Seq.head s2);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))))
                      (seq_merge s1 (Seq.tail s2)))

let slice_cons (#a: Type) (s: Seq.seq a) (i len: nat)
  : Lemma (requires i < len /\ len <= Seq.length s)
          (ensures Seq.length (Seq.slice s i len) > 0 /\
                   Seq.head (Seq.slice s i len) == Seq.index s i /\
                   Seq.tail (Seq.slice s i len) == Seq.slice s (i + 1) len)
  = assert (Seq.equal (Seq.tail (Seq.slice s i len)) (Seq.slice s (i + 1) len))

let suffix_step_left (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a) (i l1 j l2: nat)
  : Lemma
      (requires i < l1 /\ l1 <= Seq.length s1 /\ j <= l2 /\ l2 <= Seq.length s2 /\
                (j = l2 \/ le_ord ord (Seq.index s1 i) (Seq.index s2 j)))
      (ensures
        Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
        Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s1 i /\
        Seq.equal
          (Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))
          (seq_merge (Seq.slice s1 (i + 1) l1) (Seq.slice s2 j l2)))
  = slice_cons s1 i l1;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl2 = 0 then (
      seq_merge_head_left sl1 sl2;
      assert (Seq.equal (Seq.tail sl1) (Seq.slice s1 (i + 1) l1))
    ) else (
      assert (j < l2);
      slice_cons s2 j l2;
      assert (Seq.head sl1 == Seq.index s1 i);
      assert (Seq.head sl2 == Seq.index s2 j);
      assert (Seq.head sl1 <=? Seq.head sl2);
      seq_merge_take_left sl1 sl2;
      assert (Seq.equal (Seq.tail sl1) (Seq.slice s1 (i + 1) l1))
    )

let suffix_step_right (#a: Type) {| ord: TO.total_order a |} (s1 s2: Seq.seq a) (i l1 j l2: nat)
  : Lemma
      (requires j < l2 /\ l2 <= Seq.length s2 /\ i <= l1 /\ l1 <= Seq.length s1 /\
                (i = l1 \/ ~(le_ord ord (Seq.index s1 i) (Seq.index s2 j))))
      (ensures
        Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
        Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s2 j /\
        Seq.equal
          (Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))
          (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 (j + 1) l2)))
  = slice_cons s2 j l2;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl1 = 0 then (
      seq_merge_head_right sl1 sl2;
      assert (Seq.equal (Seq.tail sl2) (Seq.slice s2 (j + 1) l2))
    ) else (
      assert (i < l1);
      slice_cons s1 i l1;
      assert (Seq.head sl1 == Seq.index s1 i);
      assert (Seq.head sl2 == Seq.index s2 j);
      assert (~(Seq.head sl1 <=? Seq.head sl2));
      seq_merge_take_right sl1 sl2;
      assert (Seq.equal (Seq.tail sl2) (Seq.slice s2 (j + 1) l2))
    )

let suffix_gives_index (#a: Type) (merged: Seq.seq a) (k: nat) (suffix: Seq.seq a)
  : Lemma (requires k < Seq.length merged /\ Seq.length suffix > 0 /\
                    Seq.equal (Seq.slice merged k (Seq.length merged)) suffix)
          (ensures Seq.index merged k == Seq.head suffix)
  = ()

let upd_prefix_extend (#a: Type) (old new_s target: Seq.seq a) (k: nat) (v: a)
  : Lemma (requires k < Seq.length old /\
                    k < Seq.length target /\
                    Seq.length new_s == Seq.length old /\
                    new_s == Seq.upd old k v /\
                    (forall (p: nat). p < k ==> Seq.index old p == Seq.index target p) /\
                    v == Seq.index target k)
          (ensures forall (p: nat). p < k + 1 ==> Seq.index new_s p == Seq.index target p)
  = let aux (p: nat)
      : Lemma (p < k + 1 ==> Seq.index new_s p == Seq.index target p)
      = if p < k + 1 then
          if p = k then
            Seq.lemma_index_upd1 old k v
          else (
            assert (p < k);
            Seq.lemma_index_upd2 old k v p
          )
    in
    FStar.Classical.forall_intro aux

let append_permutations (#a: Type) {| ord: TO.total_order a |} (s1 s2 s1' s2': Seq.seq a)
  : Lemma (requires permutation #a #ord s1 s1' /\ permutation #a #ord s2 s2')
          (ensures permutation #a #ord (Seq.append s1 s2) (Seq.append s1' s2'))
  = let aux (x: a) : Lemma (count x (Seq.append s1 s2) == count x (Seq.append s1' s2')) =
      count_append x s1 s2;
      count_append x s1' s2'
    in
    FStar.Classical.forall_intro aux

let merge_sort_comparisons_split (n: nat)
  : Lemma (requires n > 1)
          (ensures merge_sort_comparisons (n / 2) + merge_sort_comparisons (n - n / 2) + n
                   <= merge_sort_comparisons n)
  = MS.merge_sort_ops_split n

let merge_sort_comparisons_nonnegative (n: nat)
  : Lemma (ensures 0 <= merge_sort_comparisons n)
  = ()

fn copy_range (#a: Type0)
  (src dst: A.array a)
  (src_lo dst_lo len: SZ.t)
  (#s_src #s_dst: Ghost.erased (Seq.seq a))
  requires
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_dst
  ensures
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_src
{
  pts_to_range_prop src;
  pts_to_range_prop dst;
  let mut i = 0sz;
  while (SZ.(!i <^ len))
  invariant exists* vi s_cur.
    R.pts_to i vi **
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_cur **
    pure (
      SZ.v vi <= SZ.v len /\
      Seq.length s_cur == SZ.v len /\
      Seq.length s_src == SZ.v len /\
      (forall (k: nat). k < SZ.v vi ==> Seq.index s_cur k == Seq.index s_src k) /\
      (forall (k: nat). SZ.v vi <= k /\ k < SZ.v len ==> Seq.index s_cur k == Seq.index s_dst k)
    )
  decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let v = pts_to_range_index src (SZ.(src_lo +^ vi));
    pts_to_range_upd dst (SZ.(dst_lo +^ vi)) v;
    i := SZ.(vi +^ 1sz);
  };
  with s_final. assert (pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_final);
  assert (pure (forall (k: nat). k < Seq.length s_final ==> Seq.index s_final k == Seq.index s_src k));
  assert (pure (Seq.equal s_final s_src));
  ()
}

fn merge (#a: Type0)
  (arr: A.array a)
  (lo mid hi: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#c0: erased nat)
  (#s1 #s2: Ghost.erased (Seq.seq a))
  requires
    pts_to_range arr (SZ.v lo) (SZ.v mid) s1 **
    pts_to_range arr (SZ.v mid) (SZ.v hi) s2 **
    MR.pts_to ctr #1.0R c0 **
    pure (
      SZ.v lo < SZ.v mid /\
      SZ.v mid < SZ.v hi /\
      sorted #a #ord s1 /\
      sorted #a #ord s2)
  ensures exists* s_out (cf: nat).
    pts_to_range arr (SZ.v lo) (SZ.v hi) s_out **
    MR.pts_to ctr #1.0R cf **
    pure (
      sorted #a #ord s_out /\
      permutation #a #ord (Seq.append s1 s2) s_out /\
      cf <= reveal c0 + (SZ.v hi - SZ.v lo))
{
  pts_to_range_prop arr #(SZ.v lo) #(SZ.v mid);
  pts_to_range_prop arr #(SZ.v mid) #(SZ.v hi);

  let l1 = SZ.(mid -^ lo);
  let l2 = SZ.(hi -^ mid);

  let init1 = pts_to_range_index arr lo #(SZ.v lo) #(SZ.v mid);
  let init2 = pts_to_range_index arr mid #(SZ.v mid) #(SZ.v hi);

  let tmp1_v = V.alloc init1 l1;
  V.to_array_pts_to tmp1_v;
  let tmp1 = V.vec_to_array tmp1_v;
  rewrite (A.pts_to (V.vec_to_array tmp1_v) (Seq.create (SZ.v l1) init1))
       as (A.pts_to tmp1 (Seq.create (SZ.v l1) init1));
  let tmp2_v = V.alloc init2 l2;
  V.to_array_pts_to tmp2_v;
  let tmp2 = V.vec_to_array tmp2_v;
  rewrite (A.pts_to (V.vec_to_array tmp2_v) (Seq.create (SZ.v l2) init2))
       as (A.pts_to tmp2 (Seq.create (SZ.v l2) init2));

  pts_to_range_intro tmp1 1.0R (Seq.create (SZ.v l1) init1);
  copy_range arr tmp1 lo 0sz l1;
  pts_to_range_elim tmp1 1.0R (reveal s1);

  pts_to_range_intro tmp2 1.0R (Seq.create (SZ.v l2) init2);
  copy_range arr tmp2 mid 0sz l2;
  pts_to_range_elim tmp2 1.0R (reveal s2);

  pts_to_range_join arr (SZ.v lo) (SZ.v mid) (SZ.v hi);

  let ghost_merged : Ghost.erased (Seq.seq a) = Ghost.hide (seq_merge #a #ord s1 s2);
  seq_merge_length #a #(reveal ord) s1 s2;

  let mut i = 0sz;
  let mut j = 0sz;
  let mut k = 0sz;

  while (SZ.(!i <^ l1) || SZ.(!j <^ l2))
  invariant exists* vi vj vk s_cur (vc: nat).
    R.pts_to i vi **
    R.pts_to j vj **
    R.pts_to k vk **
    A.pts_to tmp1 (reveal s1) **
    A.pts_to tmp2 (reveal s2) **
    pts_to_range arr (SZ.v lo) (SZ.v hi) s_cur **
    MR.pts_to ctr #1.0R vc **
    pure (
      SZ.v vi <= SZ.v l1 /\
      SZ.v vj <= SZ.v l2 /\
      SZ.v vk == SZ.v vi + SZ.v vj /\
      Seq.length s_cur == SZ.v l1 + SZ.v l2 /\
      (forall (p: nat). p < SZ.v vk ==> Seq.index s_cur p == Seq.index ghost_merged p) /\
      Seq.equal (Seq.slice ghost_merged (SZ.v vk) (Seq.length ghost_merged))
        (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1)) (Seq.slice s2 (SZ.v vj) (SZ.v l2))) /\
      vc <= reveal c0 + SZ.v vk)
  decreases ((SZ.v l1 - SZ.v !i) + (SZ.v l2 - SZ.v !j))
  {
    let vi = !i;
    let vj = !j;
    let vk = !k;

    if (vi = l1) {
      suffix_step_right #a #(reveal ord) s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
      let v = tmp2.(vj);
      suffix_gives_index ghost_merged (SZ.v vk)
        (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                        (Seq.slice s2 (SZ.v vj) (SZ.v l2)));
      assert (pure (v == Seq.index ghost_merged (SZ.v vk)));
      Seq.lemma_tail_slice ghost_merged (SZ.v vk) (Seq.length ghost_merged);
      assert (pure (
        Seq.equal (Seq.slice ghost_merged (SZ.v vk + 1) (Seq.length ghost_merged))
                  (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                                      (Seq.slice s2 (SZ.v vj + 1) (SZ.v l2)))));
      with s_before. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_before);
      assert (pure (forall (p: nat). p < SZ.v vk ==>
        Seq.index s_before p == Seq.index ghost_merged p));
      pts_to_range_upd arr (SZ.(lo +^ vk)) v;
      with s_next. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_next);
      Seq.lemma_len_upd (SZ.v vk) v s_before;
      assert (pure (Seq.length s_next == Seq.length s_before));
      upd_prefix_extend s_before s_next ghost_merged (SZ.v vk) v;
      j := SZ.(vj +^ 1sz);
      k := SZ.(vk +^ 1sz);
    } else {
      if (vj = l2) {
        suffix_step_left #a #(reveal ord) s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
        let v = tmp1.(vi);
        suffix_gives_index ghost_merged (SZ.v vk)
          (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                          (Seq.slice s2 (SZ.v vj) (SZ.v l2)));
        assert (pure (v == Seq.index ghost_merged (SZ.v vk)));
        Seq.lemma_tail_slice ghost_merged (SZ.v vk) (Seq.length ghost_merged);
        assert (pure (
          Seq.equal (Seq.slice ghost_merged (SZ.v vk + 1) (Seq.length ghost_merged))
                    (seq_merge #a #ord (Seq.slice s1 (SZ.v vi + 1) (SZ.v l1))
                                        (Seq.slice s2 (SZ.v vj) (SZ.v l2)))));
        with s_before. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_before);
        assert (pure (forall (p: nat). p < SZ.v vk ==>
          Seq.index s_before p == Seq.index ghost_merged p));
        pts_to_range_upd arr (SZ.(lo +^ vk)) v;
        with s_next. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_next);
        Seq.lemma_len_upd (SZ.v vk) v s_before;
        assert (pure (Seq.length s_next == Seq.length s_before));
        upd_prefix_extend s_before s_next ghost_merged (SZ.v vk) v;
        i := SZ.(vi +^ 1sz);
        k := SZ.(vk +^ 1sz);
      } else {
        let v1 = tmp1.(vi);
        let v2 = tmp2.(vj);
        with vc_pre. assert (MR.pts_to ctr #1.0R vc_pre);
        let cmp = iord v1 v2;
        assert (pure (cmp == v1 `ord.TO.compare` v2));
        assert (pure (O.le cmp == le_ord (reveal ord) v1 v2));
        if (O.le cmp) {
          assert (pure (le_ord (reveal ord) v1 v2));
          suffix_step_left #a #(reveal ord) s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
          suffix_gives_index ghost_merged (SZ.v vk)
            (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                            (Seq.slice s2 (SZ.v vj) (SZ.v l2)));
          assert (pure (v1 == Seq.index ghost_merged (SZ.v vk)));
          Seq.lemma_tail_slice ghost_merged (SZ.v vk) (Seq.length ghost_merged);
          assert (pure (
            Seq.equal (Seq.slice ghost_merged (SZ.v vk + 1) (Seq.length ghost_merged))
                      (seq_merge #a #ord (Seq.slice s1 (SZ.v vi + 1) (SZ.v l1))
                                          (Seq.slice s2 (SZ.v vj) (SZ.v l2)))));
          with s_before. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_before);
          assert (pure (forall (p: nat). p < SZ.v vk ==>
            Seq.index s_before p == Seq.index ghost_merged p));
          pts_to_range_upd arr (SZ.(lo +^ vk)) v1;
          with s_next. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_next);
          Seq.lemma_len_upd (SZ.v vk) v1 s_before;
          assert (pure (Seq.length s_next == Seq.length s_before));
          assert (pure (Seq.index s_next (SZ.v vk) == Seq.index ghost_merged (SZ.v vk)));
          upd_prefix_extend s_before s_next ghost_merged (SZ.v vk) v1;
          assert (pure (vc_pre + 1 <= reveal c0 + (SZ.v vk + 1)));
          i := SZ.(vi +^ 1sz);
          k := SZ.(vk +^ 1sz);
        } else {
          assert (pure (~(le_ord (reveal ord) v1 v2)));
          suffix_step_right #a #(reveal ord) s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
          suffix_gives_index ghost_merged (SZ.v vk)
            (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                            (Seq.slice s2 (SZ.v vj) (SZ.v l2)));
          assert (pure (v2 == Seq.index ghost_merged (SZ.v vk)));
          Seq.lemma_tail_slice ghost_merged (SZ.v vk) (Seq.length ghost_merged);
          assert (pure (
            Seq.equal (Seq.slice ghost_merged (SZ.v vk + 1) (Seq.length ghost_merged))
                      (seq_merge #a #ord (Seq.slice s1 (SZ.v vi) (SZ.v l1))
                                          (Seq.slice s2 (SZ.v vj + 1) (SZ.v l2)))));
          with s_before. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_before);
          assert (pure (forall (p: nat). p < SZ.v vk ==>
            Seq.index s_before p == Seq.index ghost_merged p));
          pts_to_range_upd arr (SZ.(lo +^ vk)) v2;
          with s_next. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_next);
          Seq.lemma_len_upd (SZ.v vk) v2 s_before;
          assert (pure (Seq.length s_next == Seq.length s_before));
          assert (pure (Seq.index s_next (SZ.v vk) == Seq.index ghost_merged (SZ.v vk)));
          upd_prefix_extend s_before s_next ghost_merged (SZ.v vk) v2;
          assert (pure (vc_pre + 1 <= reveal c0 + (SZ.v vk + 1)));
          j := SZ.(vj +^ 1sz);
          k := SZ.(vk +^ 1sz);
        };
      };
    };
  };

  with s_final. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_final);
  pts_to_range_prop arr #(SZ.v lo) #(SZ.v hi);
  assert (pure (Seq.equal s_final (reveal ghost_merged)));

  rewrite (A.pts_to tmp1 (reveal s1))
       as (A.pts_to (V.vec_to_array tmp1_v) (reveal s1));
  V.to_vec_pts_to tmp1_v;
  V.free tmp1_v;
  rewrite (A.pts_to tmp2 (reveal s2))
       as (A.pts_to (V.vec_to_array tmp2_v) (reveal s2));
  V.to_vec_pts_to tmp2_v;
  V.free tmp2_v;

  seq_merge_sorted #a #(reveal ord) s1 s2;
  seq_merge_permutation #a #(reveal ord) s1 s2;
  assert (pure (sorted #a #ord s_final));
  assert (pure (permutation #a #ord (Seq.append s1 s2) s_final));
  assert (pure (Seq.length s_final == SZ.v hi - SZ.v lo));
  assert (pure (SZ.v hi - SZ.v lo == SZ.v l1 + SZ.v l2));
  ()
}

fn rec merge_sort_aux (#a: Type0)
  (arr: A.array a)
  (lo hi: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#c0: erased nat)
  (#s: Ghost.erased (Seq.seq a))
  requires
    pts_to_range arr (SZ.v lo) (SZ.v hi) s **
    MR.pts_to ctr #1.0R c0
  requires pure (SZ.v lo <= SZ.v hi)
  ensures exists* s' (cf: nat).
    pts_to_range arr (SZ.v lo) (SZ.v hi) s' **
    MR.pts_to ctr #1.0R cf **
    pure (
      sorted #a #ord s' /\
      permutation #a #ord s s' /\
      cf <= reveal c0 + merge_sort_comparisons (range_len lo hi))
  decreases (range_len lo hi)
{
  pts_to_range_prop arr;
  let len = SZ.(hi -^ lo);
  if (SZ.(len <^ 2sz)) {
    assert (pure (Seq.length s <= 1));
    small_sorted #a #(reveal ord) s;
    permutation_refl #a #(reveal ord) s;
    merge_sort_comparisons_nonnegative (range_len lo hi);
    ()
  } else {
    assert (pure (SZ.v len >= 2));
    let half = SZ.(len /^ 2sz);
    let mid = SZ.(lo +^ half);
    assert (pure (SZ.v lo < SZ.v mid));
    assert (pure (SZ.v mid < SZ.v hi));
    assert (pure (SZ.v mid - SZ.v lo == SZ.v len / 2));
    assert (pure (SZ.v hi - SZ.v mid == SZ.v len - SZ.v len / 2));

    pts_to_range_split arr (SZ.v lo) (SZ.v mid) (SZ.v hi);
    with s1. assert (pts_to_range arr (SZ.v lo) (SZ.v mid) s1);
    with s2. assert (pts_to_range arr (SZ.v mid) (SZ.v hi) s2);

    merge_sort_aux arr lo mid ctr #ord iord;
    with s1' c1. assert (pts_to_range arr (SZ.v lo) (SZ.v mid) s1' ** MR.pts_to ctr #1.0R c1);

    merge_sort_aux arr mid hi ctr #ord iord;
    with s2' c2. assert (pts_to_range arr (SZ.v mid) (SZ.v hi) s2' ** MR.pts_to ctr #1.0R c2);

    append_permutations #a #(reveal ord) s1 s2 s1' s2';

    merge arr lo mid hi ctr #ord iord;
    with s_out cf. assert (pts_to_range arr (SZ.v lo) (SZ.v hi) s_out ** MR.pts_to ctr #1.0R cf);

    permutation_trans #a #(reveal ord) s (Seq.append s1 s2) (Seq.append s1' s2');
    permutation_trans #a #(reveal ord) s (Seq.append s1' s2') s_out;
    merge_sort_comparisons_split (SZ.v len);
    assert (pure (range_len lo mid == SZ.v mid - SZ.v lo));
    assert (pure (range_len mid hi == SZ.v hi - SZ.v mid));
    assert (pure (range_len lo hi == SZ.v hi - SZ.v lo));
    assert (pure (SZ.v len == range_len lo hi));
    assert (pure (merge_sort_comparisons (range_len lo mid) + merge_sort_comparisons (range_len mid hi) + range_len lo hi <= merge_sort_comparisons (range_len lo hi)));
    assert (pure (cf <= reveal c0 + merge_sort_comparisons (range_len lo hi)));
    ()
  }
}

fn merge_sort_sort (#a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s'. arr |-> s' ** pure (SC.sorted #a #ord s' /\ SC.permutation s0 s') **
  MR.pts_to ctr #1.0R (reveal i + merge_sort_comparisons (Seq.length s0))
{
  A.pts_to_len arr;
  assert (pure (A.length arr == Seq.length s0));
  assert (pure (Seq.length s0 == SZ.v len));
  pts_to_range_intro arr 1.0R (reveal s0);
  merge_sort_aux arr 0sz len ctr #ord iord;
  with s cf. assert (pts_to_range arr 0 (SZ.v len) s ** MR.pts_to ctr #1.0R cf);
  rewrite (pts_to_range arr 0 (SZ.v len) s)
      as (pts_to_range arr 0 (A.length arr) s);
  pts_to_range_elim arr 1.0R s;
  is_sorted_to_sc #a #(reveal ord) s;
  is_permutation_to_sc #a #(reveal ord) s0 s;
  assert (pure (merge_sort_comparisons (SZ.v len) == merge_sort_comparisons (Seq.length s0)));
  set_ticks ctr #cf (reveal i + merge_sort_comparisons (Seq.length s0));
}

instance merge_sort_array_sort (a: Type0) : SC.array_sort a merge_sort_comparisons =
  Pulse.Lib.Core.slprop_equivs ();
  {
    sort = merge_sort_sort #a
  }
