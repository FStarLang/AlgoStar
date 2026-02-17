(*
   Lemma: sorted permutations are equal

   This is placed in a separate module to avoid Z3 context pollution
   that occurs when combined with the recursive definitions in Spec or
   the proofs in Correctness.
*)
module CLRS.Ch09.PartialSelectionSort.SortedPerm

open FStar.Seq
open FStar.Classical
open CLRS.Ch09.PartialSelectionSort.Spec

module Seq = FStar.Seq

// Helper: tail of a sorted sequence is sorted
#restart-solver
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --z3refresh"
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

// Helper: if count_occ s x > 0 and s is sorted, then head s <= x
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

// Key lemma: sorted permutations are equal
#restart-solver
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let rec sorted_permutation_equal (s1 s2: seq int)
  : Lemma (requires is_sorted s1 /\ is_sorted s2 /\ is_permutation s1 s2)
          (ensures Seq.equal s1 s2)
          (decreases Seq.length s1)
  = if Seq.length s1 < 2 then ()
    else begin
      let min1 = Seq.index s1 0 in
      let min2 = Seq.index s2 0 in
      count_occ_cons min1 (Seq.tail s1) min1;
      assert (count_occ s1 min1 > 0);
      sorted_head_le s2 min1;
      assert (min2 <= min1);
      count_occ_cons min2 (Seq.tail s2) min2;
      assert (count_occ s2 min2 > 0);
      sorted_head_le s1 min2;
      assert (min1 <= min2);
      // min1 = min2 follows from min2 <= min1 /\ min1 <= min2
      let t1 = Seq.tail s1 in
      let t2 = Seq.tail s2 in
      sorted_tail s1;
      sorted_tail s2;
      let aux (x: int) : Lemma (count_occ t1 x = count_occ t2 x)
        = count_occ_cons min1 t1 x;
          count_occ_cons min2 t2 x;
          Seq.lemma_head_append (Seq.create 1 min1) t1;
          Seq.lemma_tail_append (Seq.create 1 min1) t1;
          assert (Seq.cons min1 t1 == s1);
          assert (Seq.cons min2 t2 == s2);
          assert (count_occ s1 x = count_occ s2 x)
      in
      Classical.forall_intro aux;
      sorted_permutation_equal t1 t2
    end
#pop-options
