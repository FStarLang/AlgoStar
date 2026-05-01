(*
   CLRS Chapter 9: Partial Selection Sort — Lemmas

   Merges proofs from:
   - SortedPerm.fst: sorted permutations are equal
   - Correctness.fst: partition-based selection correctness

   NO admits. NO assumes.
*)
module CLRS.Ch09.PartialSelectionSort.Lemmas

open FStar.Seq
open FStar.Classical

module Seq = FStar.Seq
open CLRS.Ch09.PartialSelectionSort.Spec

// ========== Sorted permutations are equal (from SortedPerm.fst) ==========

#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --z3refresh"
let sorted_tail (s: seq int)
  : Lemma (requires Seq.length s > 1 /\ is_sorted s)
          (ensures is_sorted (Seq.tail s))
  = let t = Seq.tail s in
    let n = Seq.length t in
    introduce forall (i: nat) (j: nat). i < n /\ j < n /\ i <= j ==> Seq.index t i <= Seq.index t j
    with introduce _ ==> _
    with _. (
        Seq.lemma_index_slice s 1 (Seq.length s) i;
        Seq.lemma_index_slice s 1 (Seq.length s) j;
        assert (Seq.index t i == Seq.index s (i + 1));
        assert (Seq.index t j == Seq.index s (j + 1));
        assert (i + 1 <= j + 1)
    )
#pop-options

let rec sorted_head_le (s: seq int) (x: int)
  : Lemma (requires Seq.length s > 0 /\ is_sorted s /\ count_occ s x > 0)
          (ensures Seq.index s 0 <= x)
          (decreases Seq.length s)
  = if Seq.index s 0 = x then ()
    else (
      count_occ_cons (Seq.index s 0) (Seq.tail s) x;
      if Seq.length s = 1 then ()
      else (
        sorted_tail s;
        sorted_head_le (Seq.tail s) x;
        Seq.lemma_index_slice s 1 (Seq.length s) 0
      )
    )

#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 0"
/// Helper: the head element has positive count (no is_sorted in scope).
let head_has_positive_count (s: seq int)
  : Lemma (requires Seq.length s > 0)
          (ensures count_occ s (Seq.index s 0) > 0)
  = count_occ_cons (Seq.index s 0) (Seq.tail s) (Seq.index s 0)
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 0"
/// Helper: if s1, s2 have the same head and are permutations, tails are permutations.
/// Proved WITHOUT is_sorted in scope, which avoids quantifier blow-up.
let perm_tails (s1 s2: seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                    Seq.index s1 0 = Seq.index s2 0 /\
                    is_permutation s1 s2)
          (ensures is_permutation (Seq.tail s1) (Seq.tail s2))
  = let min = Seq.index s1 0 in
    let t1 = Seq.tail s1 in
    let t2 = Seq.tail s2 in
    let aux (x: int) : Lemma (count_occ t1 x = count_occ t2 x)
      = count_occ_cons min t1 x;
        count_occ_cons min t2 x
    in
    Classical.forall_intro aux
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 0 --ifuel 1"
/// Helper: heads of sorted permutations are equal.
/// Uses head_has_positive_count to establish sorted_head_le preconditions
/// while keeping fuel at 0 to prevent is_sorted quantifier explosion.
let sorted_perm_heads_equal (s1 s2: seq int)
  : Lemma (requires Seq.length s1 > 0 /\ is_sorted s1 /\ is_sorted s2 /\ is_permutation s1 s2)
          (ensures Seq.index s1 0 = Seq.index s2 0)
  = head_has_positive_count s1;
    sorted_head_le s2 (Seq.index s1 0);
    head_has_positive_count s2;
    sorted_head_le s1 (Seq.index s2 0)
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
/// Helper: if heads are equal and tails are Seq.equal, the full seqs are Seq.equal.
let equal_head_tail (s1 s2: seq int)
  : Lemma (requires Seq.length s1 > 1 /\ Seq.length s2 > 1 /\
                    Seq.index s1 0 = Seq.index s2 0 /\
                    Seq.equal (Seq.tail s1) (Seq.tail s2))
          (ensures Seq.equal s1 s2)
  = Seq.lemma_eq_elim (Seq.tail s1) (Seq.tail s2);
    Seq.cons_head_tail s1;
    Seq.cons_head_tail s2
#pop-options

/// The inductive step: establishes preconditions for the recursive call and
/// invokes equal_head_tail. Separated to isolate the expensive quantifier VC.
#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
private let sorted_permutation_equal_inductive (s1 s2: seq int)
  (recurse: (s1': seq int) -> (s2': seq int) ->
       Lemma (requires is_sorted s1' /\ is_sorted s2' /\ is_permutation s1' s2' /\
                       Seq.length s1' < Seq.length s1)
             (ensures Seq.equal s1' s2'))
  : Lemma (requires Seq.length s1 > 1 /\ is_sorted s1 /\ is_sorted s2 /\ is_permutation s1 s2)
          (ensures Seq.equal s1 s2)
  = sorted_perm_heads_equal s1 s2;
    sorted_tail s1;
    sorted_tail s2;
    perm_tails s1 s2;
    recurse (Seq.tail s1) (Seq.tail s2);
    equal_head_tail s1 s2
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 0 --ifuel 1"
//SNIPPET_START: sorted_permutation_equal
let rec sorted_permutation_equal (s1 s2: seq int)
  : Lemma (requires is_sorted s1 /\ is_sorted s2 /\ is_permutation s1 s2)
          (ensures Seq.equal s1 s2)
          (decreases Seq.length s1)
//SNIPPET_END: sorted_permutation_equal
  = if Seq.length s1 = 0 then ()
    else if Seq.length s1 = 1 then
      sorted_perm_heads_equal s1 s2
    else
      sorted_permutation_equal_inductive s1 s2
        (fun s1' s2' -> sorted_permutation_equal s1' s2')
#pop-options

// ========== Correctness proofs (from Correctness.fst) ==========

#restart-solver

#push-options "--z3rlimit 5"
let partition_left_part_correct (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= k /\ k < p /\ p < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i))
          (ensures select_spec s k == select_spec s' k)
  = pure_sort_permutation s;
    pure_sort_permutation s';
    pure_sort_sorted s;
    pure_sort_sorted s';
    is_permutation_trans (pure_sort s) s s';
    is_permutation_trans (pure_sort s) s' (pure_sort s');
    sorted_permutation_equal (pure_sort s) (pure_sort s');
    ()
#pop-options

#push-options "--z3rlimit 5"
let partition_right_part_correct (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= p /\ p < k /\ k < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i))
          (ensures select_spec s k == select_spec s' k)
  = pure_sort_permutation s;
    pure_sort_permutation s';
    pure_sort_sorted s;
    pure_sort_sorted s';
    is_permutation_trans (pure_sort s) s s';
    is_permutation_trans (pure_sort s) s' (pure_sort s');
    sorted_permutation_equal (pure_sort s) (pure_sort s');
    ()
#pop-options

#push-options "--z3rlimit 5"
let partitioned_count_lt (s: seq int) (p: nat)
  : Lemma (requires p < Seq.length s /\
                    (forall (i: nat). i < p ==> Seq.index s i <= Seq.index s p) /\
                    (forall (i: nat). p < i /\ i < Seq.length s ==> Seq.index s p <= Seq.index s i))
          (ensures count_lt s (Seq.index s p) <= p /\
                   count_le s (Seq.index s p) >= p + 1)
  = let pv = Seq.index s p in
    let n = Seq.length s in
    let prefix = Seq.slice s 0 p in
    let pivot = Seq.slice s p (p+1) in
    let suffix = Seq.slice s (p+1) n in
    assert (Seq.equal s (Seq.append (Seq.append prefix pivot) suffix));
    count_lt_append (Seq.append prefix pivot) suffix pv;
    count_lt_append prefix pivot pv;
    count_lt_bounded prefix pv;
    assert (Seq.index pivot 0 == pv);
    assert (Seq.length pivot == 1);
    count_lt_suffix_upper s (p+1) n pv;
    count_le_append (Seq.append prefix pivot) suffix pv;
    count_le_append prefix pivot pv;
    count_le_prefix_lower s p pv;
    ()
#pop-options

let rec count_le_lt_monotone (s: seq int) (v w: int)
  : Lemma (requires v < w)
          (ensures count_le s v <= count_lt s w)
          (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else count_le_lt_monotone (Seq.tail s) v w

#push-options "--z3rlimit 5"
let partition_property_implies_kth (s: seq int) (k: nat) (v: int)
  : Lemma (requires k < Seq.length s /\
                    count_lt s v <= k /\
                    count_le s v >= k + 1)
          (ensures select_spec s k == v)
  = select_spec_partition_property s k;
    let result = select_spec s k in
    if v < result then
      count_le_lt_monotone s v result
    else if v > result then
      count_le_lt_monotone s result v
    else ()
#pop-options

#push-options "--z3rlimit 5"
let partition_pivot_is_kth (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= k /\ k == p /\ p < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i) /\
                    lo == 0 /\ hi == Seq.length s)
          (ensures Seq.index s' p == select_spec s k)
  = partitioned_count_lt s' p;
    let v = Seq.index s' p in
    count_lt_permutation_invariant s' s v;
    count_le_permutation_invariant s' s v;
    partition_property_implies_kth s k v
#pop-options

#push-options "--z3rlimit 5"
let pulse_correctness_hint (s0 s_final: seq int) (k: nat)
  : Lemma (requires k < Seq.length s0 /\
                    Seq.length s_final == Seq.length s0 /\
                    is_permutation s0 s_final /\
                    (forall (i: nat). i < k ==> Seq.index s_final i <= Seq.index s_final k) /\
                    (forall (i: nat). k < i /\ i < Seq.length s_final ==>
                      Seq.index s_final k <= Seq.index s_final i))
          (ensures Seq.index s_final k == select_spec s0 k)
  = partition_pivot_is_kth s0 s_final k 0 k (Seq.length s0)
#pop-options

// ========== Bridge: Seq.Properties.permutation ==> count_occ-based is_permutation ==========

let rec count_eq (s: seq int) (x: int)
  : Lemma (ensures Seq.Properties.count x s = count_occ s x)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s == Seq.index s 0);
      count_eq (Seq.tail s) x
    )

let seq_perm_implies_is_perm (s1 s2: seq int)
  : Lemma (requires Seq.Properties.permutation int s1 s2 /\
                    Seq.length s1 == Seq.length s2)
          (ensures is_permutation s1 s2)
  = let aux (x: int) : Lemma (count_occ s1 x = count_occ s2 x) =
      count_eq s1 x;
      count_eq s2 x
    in
    Classical.forall_intro aux
