(*
   CLRS Chapter 6: Heapsort — shared sorting-rubric instance.

   This module is separate from the extraction-facing int API in
   CLRS.Ch06.Heap.Impl.  It exposes heapsort through the common array_sort
   typeclass, using the rubric's total-order comparator and monotonic tick
   counter.
*)
module CLRS.Ch06.Heap.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.TotalOrder

module A = Pulse.Lib.Array
module CB = CLRS.Ch06.Heap.CostBound
module Classical = FStar.Classical
module HC = CLRS.Ch06.Heap.Complexity
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module R = Pulse.Lib.Reference
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

let nat_smaller (n: nat) = i:nat{i < n}

let parent_idx (i:nat{i > 0}) : nat = (i - 1) / 2
let left_idx (i:nat) : nat = 2 * i + 1
let right_idx (i:nat) : nat = 2 * i + 2

let le_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.le (x `ord.TO.compare` y)

let lt_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.lt (x `ord.TO.compare` y)

let gt_ord (#a: Type) (ord: TO.total_order a) (x y: a) : Tot bool =
  O.gt (x `ord.TO.compare` y)

let heap_down_at (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (len:nat) (i:nat{i < len /\ len <= Seq.length s}) : prop =
  (left_idx i < len ==> le_ord ord (Seq.index s (left_idx i)) (Seq.index s i)) /\
  (right_idx i < len ==> le_ord ord (Seq.index s (right_idx i)) (Seq.index s i))

let is_max_heap (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (len:nat{len <= Seq.length s}) : prop =
  forall (i:nat). i < len ==> heap_down_at ord s len i

let almost_heaps_from (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (len:nat{len <= Seq.length s}) (k:nat) (bad:nat{bad < len}) : prop =
  bad >= k /\
  (forall (j:nat). k <= j /\ j < len /\ j <> bad ==> heap_down_at ord s len j)

let heaps_from (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (len:nat{len <= Seq.length s}) (k:nat) : prop =
  forall (j:nat). k <= j /\ j < len ==> heap_down_at ord s len j

let suffix_sorted_upto (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (k: nat) (n: nat) : prop =
  k <= n /\ n <= Seq.length s /\
  (forall (i j: nat). k <= i /\ i <= j /\ j < n ==> le_ord ord (Seq.index s i) (Seq.index s j))

let prefix_le_suffix_upto (#a: Type) (ord: TO.total_order a)
  (s: Seq.seq a) (k: nat) (n: nat) : prop =
  k <= n /\ n <= Seq.length s /\
  (forall (i j: nat). i < k /\ k <= j /\ j < n ==> le_ord ord (Seq.index s i) (Seq.index s j))

let sorted_upto (#a: Type) (ord: TO.total_order a) (s: Seq.seq a) (n: nat) =
  n <= Seq.length s /\
  (forall (i j: nat). i <= j /\ j < n ==> le_ord ord (Seq.index s i) (Seq.index s j))

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

let swap_seq (#a: Type) (s:Seq.seq a) (i j:nat{i < Seq.length s /\ j < Seq.length s}) : Seq.seq a =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

let rec count_eq (#a: Type) {| ord: TO.total_order a |} (x: a) (s: Seq.seq a)
  : Lemma (ensures count x s == SC.count x s)
          (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s ==? x <==> Seq.head s == x);
      count_eq x (Seq.tail s)
    )

let permutation_to_sc (#a: Type) {| ord: TO.total_order a |} (s0 s1: Seq.seq a)
  : Lemma
    (requires permutation s0 s1)
    (ensures SC.permutation s0 s1)
  = let aux (x: a)
      : Lemma (SC.count x s0 == SC.count x s1)
      = count_eq x s0;
        count_eq x s1
    in
    Classical.forall_intro aux

let sp_permutation_refl (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a)
  : Lemma (ensures permutation s s)
  = ()

let sp_permutation_trans (#a: Type) {| ord: TO.total_order a |} (s0 s1 s2: Seq.seq a)
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

let count_slice (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a) (i: nat{i <= Seq.length s}) (x: a)
  : Lemma (ensures count x s == count x (Seq.slice s 0 i) + count x (Seq.slice s i (Seq.length s)))
  = Seq.lemma_split s i;
    count_append x (Seq.slice s 0 i) (Seq.slice s i (Seq.length s))

let rec upd_count (#a: Type) {| ord: TO.total_order a |} (s: Seq.seq a) (i: nat) (x: a) (z: a)
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

let parent_idx_lt (i:nat{i > 0}) : Lemma (parent_idx i < i) = ()

let bad_is_child_of_parent (bad:nat{bad > 0})
  : Lemma (left_idx (parent_idx bad) = bad \/ right_idx (parent_idx bad) = bad)
  = ()

let left_idx_inj (i j:nat) : Lemma (requires left_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()
let right_idx_inj (i j:nat) : Lemma (requires right_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()
let left_neq_right (i j:nat) : Lemma (left_idx i <> right_idx j) = ()

let left_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires left_idx i = bad) (ensures i = parent_idx bad) = ()
let right_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires right_idx i = bad) (ensures i = parent_idx bad) = ()

let le_ord_refl (#a: Type) (ord: TO.total_order a) (x: a)
  : Lemma (ensures le_ord ord x x)
  = ()

let lt_ord_implies_le (#a: Type) (ord: TO.total_order a) (x y: a)
  : Lemma (requires lt_ord ord x y) (ensures le_ord ord x y)
  = ()

let not_lt_ord_implies_ge (#a: Type) (ord: TO.total_order a) (x y: a)
  : Lemma (requires ~(lt_ord ord x y)) (ensures le_ord ord y x)
  = ()

let le_ord_trans (#a: Type) (ord: TO.total_order a) (x y z: a)
  : Lemma
    (requires le_ord ord x y /\ le_ord ord y z)
    (ensures le_ord ord x z)
  = ()

let heaps_from_to_almost (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s}) (k:nat) (bad:nat{bad < len})
  : Lemma (requires bad >= k /\ heaps_from ord s len (bad + 1))
          (ensures almost_heaps_from ord s len bad bad)
  = ()

let almost_to_full (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s}) (k:nat) (bad:nat{bad < len})
  : Lemma (requires almost_heaps_from ord s len k bad /\ heap_down_at ord s len bad)
          (ensures heaps_from ord s len k)
  = ()

let compose_permutations (#a: Type0) {| ord: TO.total_order a |} (s1 s2 s3: Seq.seq a)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
  = sp_permutation_trans s1 s2 s3

let swap_length (#a: Type) (s:Seq.seq a) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.length (swap_seq s i j) == Seq.length s) = ()

let swap_index_i (#a: Type) (s:Seq.seq a) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.index (swap_seq s i j) i == Seq.index s j) = ()

let swap_index_j (#a: Type) (s:Seq.seq a) (i j:nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma (Seq.index (swap_seq s i j) j == Seq.index s i) = ()

let swap_index_other (#a: Type) (s:Seq.seq a) (i j k:nat{i < Seq.length s /\ j < Seq.length s /\ k < Seq.length s /\ k <> i /\ k <> j})
  : Lemma (Seq.index (swap_seq s i j) k == Seq.index s k) = ()

let swap_unchanged_above (#a: Type)
  (s:Seq.seq a) (i j:nat{i < Seq.length s /\ j < Seq.length s}) (bound:nat)
  : Lemma (requires i < bound /\ j < bound)
          (ensures forall (k:nat). bound <= k /\ k < Seq.length s ==>
                    Seq.index (swap_seq s i j) k == Seq.index s k)
  = let aux (k:nat{bound <= k /\ k < Seq.length s})
      : Lemma (Seq.index (swap_seq s i j) k == Seq.index s k)
      = swap_index_other s i j k
    in
    Classical.forall_intro (Classical.move_requires aux)

let swap_is_permutation (#a: Type0) {| ord: TO.total_order a |} (s: Seq.seq a) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures permutation s (swap_seq s i j))
  = let x = Seq.index s i in
    let y = Seq.index s j in
    if i = j then
      Seq.lemma_eq_elim s (swap_seq s i j)
    else if x ==? y then
      assert (Seq.equal (swap_seq s i j) s)
    else (
      let s1 = Seq.upd s i y in
      let aux (z: a) : Lemma (count z s == count z (swap_seq s i j)) =
        Seq.lemma_index_upd2 s i y j;
        assert (Seq.index s1 j == y);
        upd_count s i y z;
        upd_count s1 j x z
      in
      Classical.forall_intro aux
    )

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_preserves_heap_down_other (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch})
  : Lemma (requires
            heap_down_at ord s len j /\
            left_idx j <> p /\ left_idx j <> ch /\
            right_idx j <> p /\ right_idx j <> ch)
          (ensures heap_down_at ord (swap_seq s p ch) len j)
  = swap_length s p ch;
    swap_index_other s p ch j;
    if left_idx j < len then swap_index_other s p ch (left_idx j);
    if right_idx j < len then swap_index_other s p ch (right_idx j)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_heap_down_at_parent (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires
            (ch = left_idx p \/ ch = right_idx p) /\
            lt_ord ord (Seq.index s p) (Seq.index s ch) /\
            (left_idx p < len /\ left_idx p <> ch ==> le_ord ord (Seq.index s (left_idx p)) (Seq.index s ch)) /\
            (right_idx p < len /\ right_idx p <> ch ==> le_ord ord (Seq.index s (right_idx p)) (Seq.index s ch)))
          (ensures heap_down_at ord (swap_seq s p ch) len p)
  = swap_length s p ch;
    swap_index_i s p ch;
    swap_index_j s p ch;
    lt_ord_implies_le ord (Seq.index s p) (Seq.index s ch);
    if ch = left_idx p then (
      let rp = right_idx p in
      if rp < len then (
        left_neq_right p p;
        swap_index_other s p ch rp
      )
    ) else (
      let lp = left_idx p in
      if lp < len then (
        left_neq_right p p;
        swap_index_other s p ch lp
      )
    )
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_heap_down_at_grandparent (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  (p:nat{p < len /\ p > 0}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch /\ (left_idx j = p \/ right_idx j = p)})
  : Lemma (requires
            heap_down_at ord s len j /\
            le_ord ord (Seq.index s ch) (Seq.index s j) /\
            left_idx j <> ch /\ right_idx j <> ch)
          (ensures heap_down_at ord (swap_seq s p ch) len j)
  = swap_length s p ch;
    swap_index_other s p ch j;
    if left_idx j = p then (
      swap_index_i s p ch;
      if right_idx j < len then
        swap_index_other s p ch (right_idx j)
    ) else (
      if left_idx j < len then
        swap_index_other s p ch (left_idx j)
    )
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_down_swap_lemma_from (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires
            almost_heaps_from ord s len k p /\
            (ch = left_idx p \/ ch = right_idx p) /\
            lt_ord ord (Seq.index s p) (Seq.index s ch) /\
            (left_idx p < len /\ left_idx p <> ch ==> le_ord ord (Seq.index s (left_idx p)) (Seq.index s ch)) /\
            (right_idx p < len /\ right_idx p <> ch ==> le_ord ord (Seq.index s (right_idx p)) (Seq.index s ch)) /\
            (p > 0 /\ parent_idx p >= k ==> le_ord ord (Seq.index s ch) (Seq.index s (parent_idx p))))
          (ensures almost_heaps_from ord (swap_seq s p ch) len k ch)
  = let s' = swap_seq s p ch in
    swap_length s p ch;
    swap_heap_down_at_parent ord s len p ch;
    let aux (j:nat{k <= j /\ j < len /\ j <> ch})
      : Lemma (heap_down_at ord s' len j)
      = if j = p then ()
        else (
          let lj = left_idx j in
          let rj = right_idx j in
          (if ch = left_idx p then
             (if lj = ch then left_idx_inj p ch)
           else
             (if lj = ch then left_neq_right j p));
          (if ch = left_idx p then
             (if rj = ch then left_neq_right p j)
           else
             (if rj = ch then right_idx_inj p ch));
          if lj = p || rj = p then (
            if lj = p then left_idx_parent p j
            else right_idx_parent p j;
            if p > 0 then (
              swap_heap_down_at_grandparent ord s len p ch j
            )
          ) else (
            swap_preserves_heap_down_other ord s len p ch j
          )
        )
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

let grandparent_after_swap_from (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires almost_heaps_from ord s len k p /\ (ch = left_idx p \/ ch = right_idx p))
          (ensures (left_idx ch < len ==> le_ord ord (Seq.index s (left_idx ch)) (Seq.index s ch)) /\
                   (right_idx ch < len ==> le_ord ord (Seq.index s (right_idx ch)) (Seq.index s ch)))
  = ()

let heaps_from_zero (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  : Lemma (requires heaps_from ord s len 0) (ensures is_max_heap ord s len)
  = ()

let heaps_from_half (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s})
  : Lemma (ensures heaps_from ord s len (len / 2))
  = ()

let rec root_ge_element (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s}) (i:nat)
  : Lemma (requires is_max_heap ord s len /\ len > 0 /\ i < len)
          (ensures le_ord ord (Seq.index s i) (Seq.index s 0))
          (decreases i)
  = if i = 0 then le_ord_refl ord (Seq.index s 0)
    else (
      let p = parent_idx i in
      parent_idx_lt i;
      root_ge_element ord s len p;
      bad_is_child_of_parent i;
      le_ord_trans ord (Seq.index s i) (Seq.index s p) (Seq.index s 0)
    )

let extract_almost_heaps (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap ord s len)
          (ensures (let new_len = len - 1 in
                    almost_heaps_from ord (swap_seq s 0 new_len) new_len 0 0))
  = let new_len = len - 1 in
    let s' = swap_seq s 0 new_len in
    swap_length s 0 new_len;
    let aux (j:nat{j < new_len /\ j > 0})
      : Lemma (heap_down_at ord s' new_len j)
      = swap_index_other s 0 new_len j;
        let lj = left_idx j in
        let rj = right_idx j in
        if lj < new_len then swap_index_other s 0 new_len lj;
        if rj < new_len then swap_index_other s 0 new_len rj
    in
    Classical.forall_intro (Classical.move_requires aux)

let slice_suffix_eq (#a: Type) (s1 s2:Seq.seq a) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j))
          (ensures Seq.equal (Seq.slice s1 k (Seq.length s1)) (Seq.slice s2 k (Seq.length s2)))
  = ()

let index_mem_intro (#a: Type0) {| ord: TO.total_order a |} (s:Seq.seq a) (idx:nat{idx < Seq.length s})
  : Lemma (ensures mem (Seq.index s idx) s)
  = seq_mem_k s idx

#push-options "--split_queries always --z3rlimit 10"
let extract_extends_sorted_upto (#a: Type) (ord: TO.total_order a)
  (s:Seq.seq a) (len n:nat)
  : Lemma (requires n <= Seq.length s /\ len <= n /\ len > 1 /\
                    is_max_heap ord s len /\
                    suffix_sorted_upto ord s len n /\
                    prefix_le_suffix_upto ord s len n)
          (ensures (let s' = swap_seq s 0 (len - 1) in
                    suffix_sorted_upto ord s' (len - 1) n /\
                    prefix_le_suffix_upto ord s' (len - 1) n))
  = let z : nat = 0 in
    let nl : nat = len - 1 in
    let s' = swap_seq s z nl in
    swap_length s z nl;
    swap_index_i s z nl;
    swap_index_j s z nl;
    let aux_root (i:nat{i < len})
      : Lemma (le_ord ord (Seq.index s i) (Seq.index s z))
      = root_ge_element ord s len i
    in
    Classical.forall_intro (Classical.move_requires aux_root)
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
private
let perm_prefix_witness (#a: Type0) {| ord: TO.total_order a |} (s1 s2:Seq.seq a) (k:nat) (x:a)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (m:nat). k <= m /\ m < Seq.length s1 ==> Seq.index s2 m == Seq.index s1 m) /\
                    permutation s1 s2 /\
                    mem x (Seq.slice s2 0 k))
          (ensures mem x (Seq.slice s1 0 k))
  = let len = Seq.length s1 in
    let sl1 = Seq.slice s1 0 k in
    let sl2 = Seq.slice s2 0 k in
    let suf1 = Seq.slice s1 k len in
    let suf2 = Seq.slice s2 k len in
    slice_suffix_eq s1 s2 k;
    Seq.lemma_eq_elim suf1 suf2;
    count_slice s1 k x;
    count_slice s2 k x;
    assert (count x s1 == count x s2);
    assert (count x suf1 == count x suf2);
    assert (count x sl2 > 0);
    assert (count x sl1 > 0)
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries always"
private
let perm_prefix_bounded_aux_upto (#a: Type0) (ord: TO.total_order a)
  (s1 s2:Seq.seq a) (k n:nat) (i:nat) (j:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= n /\ n <= Seq.length s1 /\
                    suffix_sorted_upto ord s1 k n /\
                    prefix_le_suffix_upto ord s1 k n /\
                    (forall (m:nat). k <= m /\ m < Seq.length s1 ==> Seq.index s2 m == Seq.index s1 m) /\
                    permutation #a #ord s1 s2 /\
                    i < k /\ j >= k /\ j < n)
          (ensures le_ord ord (Seq.index s2 i) (Seq.index s2 j))
  = let len = Seq.length s1 in
    let sl1 = Seq.slice s1 0 k in
    let sl2 = Seq.slice s2 0 k in
    let x = Seq.index sl2 i in
    Seq.lemma_index_slice s2 0 k i;
    index_mem_intro #a #ord sl2 i;
    perm_prefix_witness #a #ord s1 s2 k x;
    let m = index_mem #a #ord x sl1 in
    Seq.lemma_index_slice s1 0 k m;
    assert (Seq.index s1 m == x);
    assert (m < k /\ k <= j /\ j < n);
    assert (Seq.index s2 j == Seq.index s1 j)
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
let perm_preserves_sorted_suffix_upto (#a: Type0) (ord: TO.total_order a)
  (s1 s2:Seq.seq a) (k n:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= n /\ n <= Seq.length s1 /\
                    suffix_sorted_upto ord s1 k n /\
                    prefix_le_suffix_upto ord s1 k n /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation #a #ord s1 s2)
          (ensures suffix_sorted_upto ord s2 k n /\ prefix_le_suffix_upto ord s2 k n)
  = let aux (i:nat) (j:nat)
      : Lemma (ensures (i < k /\ k <= j /\ j < n) ==> le_ord ord (Seq.index s2 i) (Seq.index s2 j))
      = if i < k && k <= j && j < n then
          perm_prefix_bounded_aux_upto ord s1 s2 k n i j
        else ()
    in
    Classical.forall_intro_2 aux
#pop-options

let sorted_upto_from_parts (#a: Type) (ord: TO.total_order a) (s:Seq.seq a) (n:nat)
  : Lemma (requires suffix_sorted_upto ord s 1 n /\ prefix_le_suffix_upto ord s 1 n)
          (ensures sorted_upto ord s n)
  = ()

let sorted_upto_implies_sc_sorted (#a: Type) (ord: TO.total_order a) (s: Seq.seq a)
  : Lemma
    (requires sorted_upto ord s (Seq.length s))
    (ensures SC.sorted #a #ord s)
  = assert_norm (SC.sorted #a #ord s ==
      (forall (i j:nat). i <= j /\ j < Seq.length s ==>
        le_ord ord (Seq.index s i) (Seq.index s j)))

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let extract_step_lemma (#a: Type0) (ord: TO.total_order a)
  (s_cur: Seq.seq a) (s_heapified: Seq.seq a) (s0: Seq.seq a)
  (vsz n: nat)
  : Lemma
    (requires
      vsz > 1 /\ vsz <= n /\ n <= Seq.length s_cur /\
      Seq.length s_cur == Seq.length s0 /\
      permutation #a #ord s_cur (swap_seq s_cur 0 (vsz - 1)) /\
      Seq.length (swap_seq s_cur 0 (vsz - 1)) == Seq.length s_cur /\
      is_max_heap ord s_cur vsz /\
      suffix_sorted_upto ord s_cur vsz n /\
      prefix_le_suffix_upto ord s_cur vsz n /\
      permutation #a #ord s0 s_cur /\
      (forall (k:nat). n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
      Seq.length s_heapified == Seq.length (swap_seq s_cur 0 (vsz - 1)) /\
      heaps_from ord s_heapified (vsz - 1) 0 /\
      permutation #a #ord (swap_seq s_cur 0 (vsz - 1)) s_heapified /\
      (forall (k:nat). (vsz - 1) <= k /\ k < Seq.length s_heapified ==>
        Seq.index s_heapified k == Seq.index (swap_seq s_cur 0 (vsz - 1)) k))
    (ensures
      vsz - 1 > 0 /\
      vsz - 1 <= n /\
      Seq.length s_heapified == Seq.length s0 /\
      permutation #a #ord s0 s_heapified /\
      (forall (k:nat). n <= k /\ k < Seq.length s_heapified ==> Seq.index s_heapified k == Seq.index s0 k) /\
      is_max_heap ord s_heapified (vsz - 1) /\
      suffix_sorted_upto ord s_heapified (vsz - 1) n /\
      prefix_le_suffix_upto ord s_heapified (vsz - 1) n)
  = extract_extends_sorted_upto ord s_cur vsz n;
    compose_permutations #a #ord s0 s_cur (swap_seq s_cur 0 (vsz - 1));
    compose_permutations #a #ord s0 (swap_seq s_cur 0 (vsz - 1)) s_heapified;
    heaps_from_zero ord s_heapified (vsz - 1);
    perm_preserves_sorted_suffix_upto ord (swap_seq s_cur 0 (vsz - 1)) s_heapified (vsz - 1) n;
    swap_unchanged_above s_cur 0 (vsz - 1) n
#pop-options

let heap_sz_exit_eq_one (v:nat)
  : Lemma
    (requires v > 0 /\ ~(v > 1))
    (ensures v == 1)
  = ()

let heapsort_final_cost_bound (n:pos) (heap_sz:nat) (cf c0:nat)
  : Lemma
    (requires
      heap_sz == 1 /\
      cf >= c0 /\
      cf - c0 <= CB.build_cost_bound n +
                 (n - heap_sz) * CB.max_heapify_bound n 0)
    (ensures
      cf >= c0 /\
      cf - c0 <= CB.heapsort_cost_bound n)
  = assert (n - heap_sz == n - 1)

let heapsort_cost_bound_explicit (n:nat)
  : Lemma (CB.heapsort_cost_bound n ==
      (if n > 0 then
         (n / 2) * (2 * HC.log2_floor n) +
         (n - 1) * (2 * HC.log2_floor n)
       else 0))
  = if n = 0 then ()
    else CB.max_heapify_bound_root n

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
fn rec max_heapify (#a: Type0)
  (arr: A.array a) (idx: nat) (heap_size: nat) (start: Ghost.erased nat)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s: erased (Seq.seq a))
  (#c0: erased nat)
requires
  A.pts_to arr s **
  MR.pts_to ctr #1.0R c0 **
  pure (
    heap_size > 0 /\
    idx < heap_size /\
    heap_size <= Seq.length s /\
    Seq.length s == A.length arr /\
    idx >= start /\
    almost_heaps_from ord s heap_size start idx /\
    (idx > 0 /\ parent_idx idx >= start ==>
      (left_idx idx < heap_size ==>
        le_ord ord (Seq.index s (left_idx idx)) (Seq.index s (parent_idx idx))) /\
      (right_idx idx < heap_size ==>
        le_ord ord (Seq.index s (right_idx idx)) (Seq.index s (parent_idx idx))))
  )
ensures exists* s' (cf: nat).
  A.pts_to arr s' **
  MR.pts_to ctr #1.0R cf **
  pure (
    heap_size > 0 /\
    idx < heap_size /\
    Seq.length s' == Seq.length s /\
    heap_size <= Seq.length s' /\
    heaps_from ord s' heap_size start /\
    permutation #a #ord s s' /\
    (forall (k:nat). heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.max_heapify_bound heap_size idx
  )
{
  let left = left_idx idx;
  if (left >= heap_size) {
    almost_to_full ord s heap_size start idx;
    sp_permutation_refl #a #ord s;
    ()
  } else {
    let right = right_idx idx;
    let cur = arr.(SZ.uint_to_t idx);
    let lv = arr.(SZ.uint_to_t left);
    if (right < heap_size) {
      let rv = arr.(SZ.uint_to_t right);
      let cmp_lr = iord lv rv;
      if (not (O.lt cmp_lr)) {
        not_lt_ord_implies_ge ord lv rv;
        let cmp_cur_l = iord cur lv;
        CB.max_heapify_bound_left heap_size idx;
        if (O.lt cmp_cur_l) {
          lt_ord_implies_le ord cur lv;
          sift_down_swap_lemma_from ord s heap_size start idx left;
          grandparent_after_swap_from ord s heap_size start idx left;
          left_idx_inj idx left;
          let vi = arr.(SZ.uint_to_t idx);
          let vl = arr.(SZ.uint_to_t left);
          arr.(SZ.uint_to_t idx) <- vl;
          arr.(SZ.uint_to_t left) <- vi;
          swap_is_permutation #a #ord s idx left;
          swap_length s idx left;
          swap_index_i s idx left;
          max_heapify arr left heap_size start ctr #ord iord #(swap_seq s idx left)
        } else {
          not_lt_ord_implies_ge ord cur lv;
          le_ord_trans ord rv lv cur;
          almost_to_full ord s heap_size start idx;
          sp_permutation_refl #a #ord s;
          ()
        }
      } else {
        lt_ord_implies_le ord lv rv;
        let cmp_cur_r = iord cur rv;
        CB.max_heapify_bound_right heap_size idx;
        if (O.lt cmp_cur_r) {
          lt_ord_implies_le ord cur rv;
          sift_down_swap_lemma_from ord s heap_size start idx right;
          grandparent_after_swap_from ord s heap_size start idx right;
          right_idx_inj idx right;
          let vi = arr.(SZ.uint_to_t idx);
          let vr = arr.(SZ.uint_to_t right);
          arr.(SZ.uint_to_t idx) <- vr;
          arr.(SZ.uint_to_t right) <- vi;
          swap_is_permutation #a #ord s idx right;
          swap_length s idx right;
          swap_index_i s idx right;
          max_heapify arr right heap_size start ctr #ord iord #(swap_seq s idx right)
        } else {
          not_lt_ord_implies_ge ord cur rv;
          le_ord_trans ord lv rv cur;
          almost_to_full ord s heap_size start idx;
          sp_permutation_refl #a #ord s;
          ()
        }
      }
    } else {
      let _cmp_pad = iord lv lv;
      le_ord_refl ord lv;
      let cmp_cur_l = iord cur lv;
      CB.max_heapify_bound_left heap_size idx;
      if (O.lt cmp_cur_l) {
        lt_ord_implies_le ord cur lv;
        sift_down_swap_lemma_from ord s heap_size start idx left;
        grandparent_after_swap_from ord s heap_size start idx left;
        left_idx_inj idx left;
        let vi = arr.(SZ.uint_to_t idx);
        let vl = arr.(SZ.uint_to_t left);
        arr.(SZ.uint_to_t idx) <- vl;
        arr.(SZ.uint_to_t left) <- vi;
        swap_is_permutation #a #ord s idx left;
        swap_length s idx left;
        swap_index_i s idx left;
        max_heapify arr left heap_size start ctr #ord iord #(swap_seq s idx left)
      } else {
        not_lt_ord_implies_ge ord cur lv;
        almost_to_full ord s heap_size start idx;
        sp_permutation_refl #a #ord s;
        ()
      }
    }
  }
}
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
fn build_max_heap (#a: Type0)
  (arr: A.array a)
  (n: nat)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#c0: erased nat)
requires
  A.pts_to arr s0 **
  MR.pts_to ctr #1.0R c0 **
  pure (n > 0 /\ n <= A.length arr /\ Seq.length s0 == A.length arr)
ensures exists* s (cf: nat).
  A.pts_to arr s **
  MR.pts_to ctr #1.0R cf **
  pure (
    Seq.length s == Seq.length s0 /\
    n <= Seq.length s /\
    is_max_heap ord s n /\
    permutation #a #ord s0 s /\
    (forall (k:nat). n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.build_cost_bound n
  )
{
  let half : nat = n / 2;
  let mut i: nat = half;
  heaps_from_half ord s0 n;
  sp_permutation_refl #a #ord s0;

  while (!i > 0)
  invariant exists* (vi:nat) s_cur (vc: nat).
    R.pts_to i vi **
    A.pts_to arr s_cur **
    MR.pts_to ctr #1.0R vc **
    pure (
      n > 0 /\
      vi <= half /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length arr /\
      permutation #a #ord s0 s_cur /\
      (forall (k:nat). n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
      heaps_from ord s_cur n vi /\
      vc >= reveal c0 /\
      vc - reveal c0 <= (half - vi) * CB.max_heapify_bound n 0
    )
  decreases (!i)
  {
    let vi = !i;
    let idx : nat = vi - 1;
    i := idx;
    with s_cur. assert (A.pts_to arr s_cur);
    heaps_from_to_almost ord s_cur n idx idx;
    CB.max_heapify_bound_le_root n idx;
    max_heapify arr idx n idx ctr #ord iord #s_cur;
    ()
  };

  with s_built. assert (A.pts_to arr s_built);
  heaps_from_zero ord s_built n;
  ()
}
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn heapsort (#a: Type0)
  (arr: A.array a)
  (n: nat)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#c0: erased nat)
requires
  A.pts_to arr s0 **
  MR.pts_to ctr #1.0R c0 **
  pure (n <= A.length arr /\ Seq.length s0 == A.length arr)
ensures exists* s (cf: nat).
  A.pts_to arr s **
  MR.pts_to ctr #1.0R cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted_upto ord s n /\
    permutation #a #ord s0 s /\
    (forall (k:nat). n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.heapsort_cost_bound n
  )
{
  if (n = 0) {
    sp_permutation_refl #a #ord s0;
    ()
  } else {
    build_max_heap arr n ctr #ord iord;

    let mut heap_sz: nat = n;

    while (!heap_sz > 1)
    invariant exists* (vsz:nat) s_cur (vc: nat).
      R.pts_to heap_sz vsz **
      A.pts_to arr s_cur **
      MR.pts_to ctr #1.0R vc **
      pure (
        n > 0 /\
        vsz > 0 /\
        vsz <= n /\
        Seq.length s_cur == Seq.length s0 /\
        Seq.length s_cur == A.length arr /\
        permutation #a #ord s0 s_cur /\
        (forall (k:nat). n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
        is_max_heap ord s_cur vsz /\
        suffix_sorted_upto ord s_cur vsz n /\
        prefix_le_suffix_upto ord s_cur vsz n /\
        vc >= reveal c0 /\
        vc - reveal c0 <= CB.build_cost_bound n +
                         (n - vsz) * CB.max_heapify_bound n 0
      )
    decreases (!heap_sz)
    {
      let vsz = !heap_sz;
      with s_cur. assert (A.pts_to arr s_cur);

      let last : nat = vsz - 1;
      let v0 = arr.(SZ.uint_to_t 0);
      let vl = arr.(SZ.uint_to_t last);
      arr.(SZ.uint_to_t 0) <- vl;
      arr.(SZ.uint_to_t last) <- v0;

      swap_is_permutation #a #ord s_cur 0 last;
      swap_length s_cur 0 last;
      extract_extends_sorted_upto ord s_cur vsz n;

      let new_sz : nat = vsz - 1;
      extract_almost_heaps ord s_cur vsz;
      CB.max_heapify_bound_monotone new_sz n 0;
      max_heapify arr 0 new_sz 0 ctr #ord iord #(swap_seq s_cur 0 last);
      with s_heapified. assert (A.pts_to arr s_heapified);
      with vc_after. assert (MR.pts_to ctr #1.0R vc_after);
      FStar.Math.Lemmas.distributivity_add_left (n - vsz) 1 (CB.max_heapify_bound n 0);
      heaps_from_zero ord s_heapified new_sz;
      perm_preserves_sorted_suffix_upto ord (swap_seq s_cur 0 last) s_heapified new_sz n;

      heap_sz := new_sz;
    };

    with vheap_final s_final vc_final.
      assert (R.pts_to heap_sz vheap_final ** A.pts_to arr s_final ** MR.pts_to ctr #1.0R vc_final);
    heap_sz_exit_eq_one vheap_final;
    assert (pure (vheap_final == 1));
    assert (pure (suffix_sorted_upto ord s_final 1 n));
    assert (pure (prefix_le_suffix_upto ord s_final 1 n));
    sorted_upto_from_parts ord s_final n;
    heapsort_final_cost_bound n vheap_final vc_final (reveal c0);
    ()
  }
}
#pop-options

fn heapsort_sort (a: Type0)
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
  pure (SC.sorted #a #ord s' /\
        SC.permutation s0 s' /\
        ticks <= reveal i +
          (let n = Seq.length s0 in
           if n > 0 then
             (n / 2) * (2 * HC.log2_floor n) +
             (n - 1) * (2 * HC.log2_floor n)
           else 0))
{
  A.pts_to_len arr;
  heapsort arr (SZ.v len) ctr #ord iord #s0 #i;
  with s. assert (arr |-> s);
  with cf. assert (MR.pts_to ctr #1.0R cf);
  assert (pure (Seq.length s == Seq.length s0));
  assert (pure (Seq.length s == SZ.v len));
  sorted_upto_implies_sc_sorted ord s;
  permutation_to_sc #a #ord s0 s;
  heapsort_cost_bound_explicit (Seq.length s0);
  assert (pure (cf <= reveal i +
    (let n = Seq.length s0 in
     if n > 0 then
       (n / 2) * (2 * HC.log2_floor n) +
       (n - 1) * (2 * HC.log2_floor n)
     else 0)));
  ()
}
