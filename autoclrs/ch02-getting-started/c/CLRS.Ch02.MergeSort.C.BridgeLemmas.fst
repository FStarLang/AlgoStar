(*
   MergeSort Bridge Lemmas — proofs.

   NO admits. NO assumes.
*)
module CLRS.Ch02.MergeSort.C.BridgeLemmas

open CLRS.Common.SortSpec
open CLRS.Ch02.InsertionSort.C.BridgeLemmas
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32
module Classical = FStar.Classical

// ================================================================
// subrange_sorted_implies_sorted
// ================================================================

#push-options "--z3rlimit 80"

/// Helper: transfer adjacent-pair ordering from s to its slice
private let slice_adj_helper (s: Seq.seq (option I32.t)) (lo hi: nat) (k: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s /\
      (forall (m: nat). lo <= m /\ m < hi ==> Some? (Seq.index s m)) /\
      (forall (m: nat). lo <= m /\ m + 1 < hi ==>
        I32.v (Some?.v (Seq.index s m)) <= I32.v (Some?.v (Seq.index s (m + 1)))))
    (ensures k + 1 < hi - lo ==> (
      let sl = Seq.slice s lo hi in
      I32.v (Some?.v (Seq.index sl k)) <= I32.v (Some?.v (Seq.index sl (k + 1)))))
  = if k + 1 < hi - lo then (
      Seq.lemma_index_slice s lo hi k;
      Seq.lemma_index_slice s lo hi (k + 1)
    ) else ()

let subrange_sorted_implies_sorted
  (s: Seq.seq (option I32.t)) (lo hi: nat)
  = let sl = Seq.slice s lo hi in
    let len = hi - lo in
    Classical.forall_intro (Classical.move_requires (slice_adj_helper s lo hi));
    adjacent_sorted_implies_sorted sl len

#pop-options

// ================================================================
// subrange_unchanged_implies_perm
// ================================================================

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let subrange_unchanged_implies_perm
  (s_old s_new: Seq.seq (option I32.t)) (lo hi: nat)
  = let sl_old = Seq.slice s_old lo hi in
    let sl_new = Seq.slice s_new lo hi in
    let len = hi - lo in
    assert (forall (k: nat). k < len ==> Seq.index sl_new k == Seq.index sl_old k);
    unchanged_extract_eq sl_new sl_old len

#pop-options

// ================================================================
// merge_sorted_permutation
// ================================================================

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let merge_sorted_permutation
  (s_a s_buf: Seq.seq (option I32.t))
  (lo mid hi: nat)
  = subrange_sorted_implies_sorted s_buf lo hi

#pop-options
