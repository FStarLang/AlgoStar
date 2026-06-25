(*
   CLRS Chapter 2: insertion sort as an instance of the shared sorting rubric.

   This module is separate from the extraction-facing int API in
   CLRS.Ch02.InsertionSort.Impl.  It exposes insertion sort through the common
   array_sort typeclass, parametric in the element type and total order.
*)
module CLRS.Ch02.InsertionSort.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.TotalOrder

module A = Pulse.Lib.Array
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module R = Pulse.Lib.Reference
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

let insertion_sort_comparisons (n: nat) : nat = n * (n - 1) / 2

let le_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.le (x `ord.TO.compare` y)

let gt_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.gt (x `ord.TO.compare` y)

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

let rec upd_count (#t: Type) {| total_order t |} (s: Seq.seq t) (i: nat) (x: t) (z: t)
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

let ordered
      (#t: Type)
      {| total_order t |}
      (s0 s1: Seq.seq t)
  =
  forall i j.
    0 <= i /\ i < Seq.length s0 /\
    0 <= j /\ j < Seq.length s1 ==>
    Seq.index s0 i <=? Seq.index s1 j

let slice_index (#t: Type) (s: Seq.seq t) (i j k: nat)
  : Lemma
    (ensures (i <= j /\ j < k /\ k <= Seq.length s ==>
              Seq.index s j == Seq.index (Seq.slice s i k) (j - i <: nat)))
    [SMTPat (Seq.slice s i k);
     SMTPat (Seq.index s j)]
  = ()

let sorted_concat
      (#t: Type)
      {| total_order t |}
      (s0 s1: Seq.seq t)
  : Lemma
    (requires
      sorted s0 /\
      sorted s1 /\
      ordered s0 s1)
    (ensures sorted (Seq.append s0 s1))
  = ()

let inner_invariant
      (#t: Type)
      {| total_order t |}
      (s0 s': Seq.seq t)
      (key: t)
      (vi vj: SZ.t)
      (done: bool)
  =
  0 <= SZ.v vi /\
  SZ.v vi < SZ.v vj /\
  SZ.v vj < Seq.length s' /\
  (
    let ai = Seq.index s' (SZ.v vi) in
    let lhs = Seq.slice s' 0 (SZ.v vi + 1 <: nat) in
    let rhs = Seq.slice s' (SZ.v vi + 1) (SZ.v vj + 1 <: nat) in
    let slot = Seq.index s' (SZ.v vi + 1 <: nat) in
    sorted lhs /\
    sorted rhs /\
    ordered lhs (Seq.upd rhs 0 ai) /\
    (if done
     then vi == 0sz /\ slot == ai /\ permutation s0 (Seq.upd s' 0 key)
     else if SZ.v vi + 1 = SZ.v vj then slot == key /\ permutation s0 s'
     else slot == Seq.index s' (SZ.v vi + 2) /\ permutation s0 (Seq.upd s' (SZ.v vi + 1) key)) /\
    (forall (k: nat). 0 <= k /\ k < Seq.length rhs ==> Seq.index rhs k >=? key)
  )

#push-options "--fuel 0 --ifuel 1 --split_queries no --z3rlimit_factor 5"
#restart-solver
let step_inner_invariant
      (#t: Type)
      {| total_order t |}
      (s s0 s1: Seq.seq t) (key: t)
      (vi vj: SZ.t)
  : Lemma
    (requires
      inner_invariant s s0 key vi vj false /\
      Seq.index s0 (SZ.v vi) >? key /\
      s1 == Seq.upd s0 (SZ.v vi + 1 <: nat) (Seq.index s0 (SZ.v vi)))
    (ensures (
      let vi' = if vi = 0sz then 0sz else SZ.(vi -^ 1sz) in
      let done = (vi = 0sz) in
      inner_invariant s s1 key vi' vj done))
  = ()
#pop-options

#push-options "--fuel 0 --ifuel 1 --split_queries no --z3rlimit_factor 2"
#restart-solver
let step_outer_invariant
      (#t: Type)
      {| total_order t |}
      (s s0: Seq.seq t) (key: t)
      (vi vj: SZ.t)
      (done: bool)
  : Lemma
    (requires
      inner_invariant s s0 key vi vj done /\
      (done \/ Seq.index s0 (SZ.v vi) <=? key))
    (ensures (
      let ix = if done then 0 else SZ.v vi + 1 <: nat in
      let s' = Seq.upd s0 ix key in
      sorted (Seq.slice s' 0 (SZ.v vj + 1 <: nat)) /\
      permutation s s'))
  = ()
#pop-options

let insertion_sort_comparisons_step (vj: nat)
  : Lemma (requires vj >= 1)
          (ensures insertion_sort_comparisons vj + vj == insertion_sort_comparisons (vj + 1))
  = CLRS.Ch02.InsertionSort.Lemmas.lemma_triangle_step vj

fn insertion_sort_core (#a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
requires (
  arr |-> s0 **
  MR.pts_to ctr #1.0R i
)
requires pure (Seq.length s0 == SZ.v len)
ensures exists* s' (cf: nat).
  arr |-> s' **
  MR.pts_to ctr #1.0R cf **
  pure (
    sorted #a #ord s' /\
    permutation #a #ord s0 s' /\
    cf <= reveal i + insertion_sort_comparisons (Seq.length s0))
{
  A.pts_to_len arr;
  if (len = 0sz) {
    ()
  } else {
    let mut j = 1sz;
    while (SZ.(!j <^ len))
    invariant exists* vj s (vc: nat).
      R.pts_to j vj **
      arr |-> s **
      MR.pts_to ctr #1.0R vc **
      pure (
        1 <= SZ.v vj /\
        SZ.v vj <= SZ.v len /\
        Seq.length s == Seq.length s0 /\
        sorted #a #ord (Seq.slice s 0 (SZ.v vj)) /\
        permutation #a #ord s0 s /\
        vc <= reveal i + insertion_sort_comparisons (SZ.v vj))
    decreases (SZ.v len - SZ.v !j)
    {
      A.pts_to_len arr;
      let vj = !j;
      j := SZ.(vj +^ 1sz);
      let key = arr.(vj);
      let mut idx : SZ.t = SZ.(vj -^ 1sz);
      let mut done = false;
      let mut cont = false;
      let mut fuel : SZ.t = vj;
      with ss. assert (arr |-> ss);
      with vc_before. assert (MR.pts_to ctr #1.0R vc_before);
      let first = arr.(!idx);
      let first_cmp = iord first key;
      cont := O.gt first_cmp;

      while (!cont)
      invariant exists* vi vdone vcont vfuel s_inner (vc_inner: nat) vj_next.
        R.pts_to idx vi **
        R.pts_to done vdone **
        R.pts_to cont vcont **
        R.pts_to fuel vfuel **
        R.pts_to j vj_next **
        arr |-> s_inner **
        MR.pts_to ctr #1.0R vc_inner **
        pure (
          vj_next == SZ.(vj +^ 1sz) /\
          (vcont ==> SZ.v vfuel == SZ.v vi + 1) /\
          SZ.v vfuel <= SZ.v vi + 1 /\
          inner_invariant #a #ord ss s_inner key vi vj vdone /\
          (vcont ==> not vdone /\ gt_ord ord (Seq.index s_inner (SZ.v vi)) key) /\
          ((not vcont /\ not vdone) ==> le_ord ord (Seq.index s_inner (SZ.v vi)) key) /\
          vc_inner <= reveal i + insertion_sort_comparisons (SZ.v vj) + (SZ.v vj - SZ.v vi))
      decreases (SZ.v !fuel)
      {
        let vi = !idx;
        let vfuel = !fuel;
        assert (pure (SZ.v vfuel >= 1));
        with s_pre. assert (arr |-> s_pre);
        let shifted = arr.(vi);
        arr.(SZ.(vi +^ 1sz)) <- shifted;
        with s_post. assert (arr |-> s_post);
        step_inner_invariant #a #ord ss s_pre s_post key vi vj;
        fuel := SZ.(vfuel -^ 1sz);
        if (SZ.(vi =^ 0sz)) {
          done := true;
          cont := false;
        } else {
          assert (pure (SZ.(vi =^ 0sz) == (SZ.v vi = 0)));
          assert (pure (not (SZ.v vi = 0)));
          SZ.size_v_inj vi;
          assert (pure (SZ.v vi <> 0));
          assert (pure (0 <= SZ.v vi));
          assert (pure (SZ.v vi > 0));
          assert (pure (SZ.v vi >= 1));
          let vi_next = SZ.(vi -^ 1sz);
          idx := vi_next;
          let next = arr.(vi_next);
          let cmp = iord next key;
          cont := O.gt cmp;
        }
      };

      with s_before_key. assert (arr |-> s_before_key);
      with vc_after_inner. assert (MR.pts_to ctr #1.0R vc_after_inner);
      let vi = !idx;
      let vdone = !done;
      let vcont = !cont;
      let vj_next = !j;
      let vj_next_val = !j;
      assert (pure (vj_next_val == SZ.(vj +^ 1sz)));
      assert (pure (not vcont));
      step_outer_invariant #a #ord ss s_before_key key vi vj vdone;
      let vi_plus = SZ.(vi +^ 1sz);
      let vi_plus_t : SZ.t = vi_plus;
      let dst : SZ.t = if (vdone) { vi } else { vi_plus_t };
      arr.(dst) <- key;
      with s_after_key. assert (arr |-> s_after_key);
      A.pts_to_len arr;
      assert (pure (A.length arr == Seq.length s_after_key));
      assert (pure (Seq.length s_after_key == Seq.length s0));
      assert (pure (SZ.v vj < SZ.v len));
      assert (pure (SZ.v vj + 1 <= SZ.v len));
      assert (pure (SZ.v vj_next == SZ.v vj + 1));
      assert (pure (sorted #a #ord (Seq.slice s_after_key 0 (SZ.v vj + 1 <: nat))));
      assert (pure (sorted #a #ord (Seq.slice s_after_key 0 (SZ.v vj_next))));
      assert (pure (permutation #a #ord ss s_after_key));
      permutation_trans #a #ord s0 ss s_after_key;
      insertion_sort_comparisons_step (SZ.v vj);
      assert (pure (SZ.v vi < SZ.v vj));
      assert (pure (SZ.v vj - SZ.v vi <= SZ.v vj));
      assert (pure (vc_after_inner <= reveal i + insertion_sort_comparisons (SZ.v vj) + SZ.v vj));
      assert (pure (vc_after_inner <= reveal i + insertion_sort_comparisons (SZ.v vj + 1)));
      assert (pure (insertion_sort_comparisons (SZ.v vj_next) == insertion_sort_comparisons (SZ.v vj + 1)));
      assert (pure (Seq.length s_after_key == Seq.length s0));
      assert (pure (SZ.v vj_next_val == SZ.v vj + 1));
      assert (pure (sorted #a #ord (Seq.slice s_after_key 0 (SZ.v vj_next_val))));
      assert (pure (SZ.v vj - SZ.v vi <= SZ.v vj));
      assert (pure (vc_after_inner <= reveal i + insertion_sort_comparisons (SZ.v vj) + SZ.v vj));
      assert (pure (vc_after_inner <= reveal i + insertion_sort_comparisons (SZ.v vj_next_val)));
    };
    with s'. assert (arr |-> s');
    assert (pure (Seq.slice s' 0 (Seq.length s') `Seq.equal` s'));
  }
}

fn insertion_sort_sort (#a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s' (ticks: nat).
  arr |-> s' **
  MR.pts_to ctr #1.0R ticks **
  pure (
    SC.sorted #a #ord s' /\
    SC.permutation s0 s' /\
    ticks <= reveal i + insertion_sort_comparisons (Seq.length s0))
{
  A.pts_to_len arr;
  insertion_sort_core arr len ctr #ord iord #s0 #i;
  with s cf. assert (arr |-> s ** MR.pts_to ctr #1.0R cf);
  is_sorted_to_sc #a #(reveal ord) s;
  is_permutation_to_sc #a #(reveal ord) s0 s;
  assert (pure (
    SC.sorted #a #ord s /\
    SC.permutation s0 s /\
    cf <= reveal i + insertion_sort_comparisons (Seq.length s0)));
}

fn insertion_sort_sort_poly (a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s' (ticks: nat).
  arr |-> s' **
  MR.pts_to ctr #1.0R ticks **
  pure (
    SC.sorted #a #ord s' /\
    SC.permutation s0 s' /\
    ticks <= reveal i + insertion_sort_comparisons (Seq.length s0))
{
  insertion_sort_sort #a arr len ctr #ord iord #s0 #i
}

instance insertion_sort_array_sort : SC.array_sort (fun n -> n * (n - 1) / 2) =
  Pulse.Lib.Core.slprop_equivs ();
  {
    sort = insertion_sort_sort_poly
  }
