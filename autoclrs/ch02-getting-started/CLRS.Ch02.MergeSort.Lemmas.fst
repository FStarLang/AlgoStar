(*
   Merge Sort - Lemma proofs

   Proves properties of the pure seq_merge function:
   - Length preservation, count preservation, permutation
   - Sortedness preservation
   - Suffix stepping lemmas for the imperative merge loop
   - Complexity cost splitting

   NO admits. NO assumes.
*)
module CLRS.Ch02.MergeSort.Lemmas

open CLRS.Common.SortSpec
open CLRS.Ch02.MergeSort.Spec
open CLRS.Ch02.MergeSort.Complexity
open Pulse.Lib.BoundedIntegers
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical

// ================================================================
// Merge Length Lemma  
// ================================================================

let rec seq_merge_length (s1 s2: Seq.seq int)
  : Lemma (ensures Seq.length (seq_merge s1 s2) == Seq.length s1 + Seq.length s2)
          (decreases (Seq.length s1 + Seq.length s2))
          [SMTPat (Seq.length (seq_merge s1 s2))]
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <= Seq.head s2 then seq_merge_length (Seq.tail s1) s2
    else seq_merge_length s1 (Seq.tail s2)

// ================================================================
// Merge preserves count (=> permutation of append)
// ================================================================

#push-options "--z3rlimit 2 --fuel 1 --ifuel 1"

let count_empty (x: int) (s: Seq.seq int)
  : Lemma (requires Seq.length s = 0)
          (ensures SeqP.count x s == 0)
  = ()

let count_cons (x: int) (h: int) (t: Seq.seq int)
  : Lemma (ensures SeqP.count x (Seq.cons h t) == (if h = x then 1 else 0) + SeqP.count x t)
  = assert (Seq.head (Seq.cons h t) == h);
    assert (Seq.tail (Seq.cons h t) `Seq.equal` t)

let rec seq_merge_count (x: int) (s1 s2: Seq.seq int)
  : Lemma (ensures SeqP.count x (seq_merge s1 s2) == SeqP.count x s1 + SeqP.count x s2)
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
      if h1 <= h2 then (
        seq_merge_count x (Seq.tail s1) s2;
        count_cons x h1 (seq_merge (Seq.tail s1) s2)
      ) else (
        seq_merge_count x s1 (Seq.tail s2);
        count_cons x h2 (seq_merge s1 (Seq.tail s2))
      )

let seq_merge_permutation (s1 s2: Seq.seq int)
  : Lemma (ensures permutation (Seq.append s1 s2) (seq_merge s1 s2))
  = reveal_opaque (`%permutation) (permutation (Seq.append s1 s2) (seq_merge s1 s2));
    SeqP.lemma_append_count s1 s2;
    Classical.forall_intro (fun x -> seq_merge_count x s1 s2)

#pop-options

// ================================================================
// Merge preserves sortedness
// ================================================================

#push-options "--z3rlimit 2 --fuel 2 --ifuel 1 --split_queries always"

let rec seq_merge_all_ge (v: int) (s1 s2: Seq.seq int)
  : Lemma (requires all_ge v s1 /\ all_ge v s2)
          (ensures all_ge v (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <= Seq.head s2 then seq_merge_all_ge v (Seq.tail s1) s2
    else seq_merge_all_ge v s1 (Seq.tail s2)

let sorted_all_ge_head (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ sorted s)
          (ensures all_ge (Seq.head s) s)
  = ()

let sorted_tail (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ sorted s)
          (ensures sorted (Seq.tail s))
  = ()

let sorted_cons (h: int) (t: Seq.seq int)
  : Lemma (requires sorted t /\ all_ge h t)
          (ensures sorted (Seq.cons h t))
  = ()

let rec seq_merge_sorted (s1 s2: Seq.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      sorted_tail s1;
      sorted_tail s2;
      if h1 <= h2 then (
        seq_merge_sorted (Seq.tail s1) s2;
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        seq_merge_all_ge h1 (Seq.tail s1) s2;
        sorted_cons h1 (seq_merge (Seq.tail s1) s2);
        ()
      ) else (
        seq_merge_sorted s1 (Seq.tail s2);
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        seq_merge_all_ge h2 s1 (Seq.tail s2);
        sorted_cons h2 (seq_merge s1 (Seq.tail s2));
        ()
      )

#pop-options

// ================================================================
// Key lemma: relating seq_merge to head and suffix
// ================================================================

#push-options "--z3rlimit 2 --fuel 2 --ifuel 1"

let seq_merge_head_right (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 = 0 /\ Seq.length s2 > 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s2)
  = ()

let seq_merge_head_left (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 = 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s1)
  = ()

let seq_merge_take_left (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                     Seq.head s1 <= Seq.head s2)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge (Seq.tail s1) s2)
  = assert (Seq.head (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)) == Seq.head s1);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)))
                      (seq_merge (Seq.tail s1) s2))

let seq_merge_take_right (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                     ~(Seq.head s1 <= Seq.head s2))
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge s1 (Seq.tail s2))
  = assert (Seq.head (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))) == Seq.head s2);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))))
                      (seq_merge s1 (Seq.tail s2)))

let slice_cons (s: Seq.seq int) (i: nat) (len: nat)
  : Lemma (requires i < len /\ len <= Seq.length s)
          (ensures Seq.length (Seq.slice s i len) > 0 /\
                   Seq.head (Seq.slice s i len) == Seq.index s i /\
                   Seq.tail (Seq.slice s i len) == Seq.slice s (i + 1) len)
  = assert (Seq.equal (Seq.tail (Seq.slice s i len)) (Seq.slice s (i + 1) len))

let suffix_step_left (s1 s2: Seq.seq int) (i l1 j l2: nat)
  = slice_cons s1 i l1;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl2 = 0 then
      seq_merge_head_left sl1 sl2
    else (
      assert (Seq.head sl1 == Seq.index s1 i);
      assert (Seq.head sl1 <= Seq.head sl2);
      seq_merge_take_left sl1 sl2;
      assert (Seq.equal (Seq.tail sl1) (Seq.slice s1 (i+1) l1))
    )

let suffix_step_right (s1 s2: Seq.seq int) (i l1 j l2: nat)
  = slice_cons s2 j l2;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl1 = 0 then
      seq_merge_head_right sl1 sl2
    else (
      assert (Seq.head sl2 == Seq.index s2 j);
      assert (~(Seq.head sl1 <= Seq.head sl2));
      seq_merge_take_right sl1 sl2;
      assert (Seq.equal (Seq.tail sl2) (Seq.slice s2 (j+1) l2))
    )

let slice_full (s: Seq.seq int)
  : Lemma (Seq.equal (Seq.slice s 0 (Seq.length s)) s)
          [SMTPat (Seq.slice s 0 (Seq.length s))]
  = ()

let suffix_gives_index (merged: Seq.seq int) (k: nat) (suffix: Seq.seq int)
  = ()

let upd_prefix_extend (old new_s target: Seq.seq int) (k: nat) (v: int)
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
    Classical.forall_intro aux

let merge_complexity_extend_hi (cf c0 k: nat)
  : Lemma (requires merge_complexity_bounded cf c0 0 k)
           (ensures merge_complexity_bounded cf c0 0 (k + 1))
  = ()

#pop-options

let ms_cost_split (n: int{n >= 2})
  = merge_sort_ops_split n
