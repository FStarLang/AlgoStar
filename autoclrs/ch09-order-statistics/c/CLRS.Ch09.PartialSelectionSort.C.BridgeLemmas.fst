(*
   PartialSelectionSort Bridge Lemmas — proofs.

   NO admits. NO assumes.
*)
module CLRS.Ch09.PartialSelectionSort.C.BridgeLemmas

module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32
module Classical = FStar.Classical
module PSSImpl = CLRS.Ch09.PartialSelectionSort.Impl
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec
module PSSLemmas = CLRS.Ch09.PartialSelectionSort.Lemmas

// ================================================================
// extract_ints
// ================================================================

let extract_ints (s: Seq.seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: Seq.seq int{Seq.length r == len /\
    (forall (i: nat). i < len ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})
  = Seq.init len (fun (i: nat{i < len}) -> (I32.v (Some?.v (Seq.index s i)) <: int))

// ================================================================
// c_sorted_prefix_implies_sorted_prefix
// ================================================================

private let rec adj_step_prefix (s: Seq.seq int) (bound: nat) (i j: nat)
  : Lemma
    (requires bound <= Seq.length s /\
      (forall (k: nat). k > 0 /\ k < bound ==> Seq.index s (k - 1) <= Seq.index s k))
    (ensures i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)
    (decreases (j - i))
  = if i >= j || j >= bound then ()
    else adj_step_prefix s bound i (j - 1)

let c_sorted_prefix_implies_sorted_prefix
  (s: Seq.seq (option I32.t)) (n k: nat)
  = let ints = extract_ints s n in
    assert (forall (j: nat). j > 0 /\ j < k ==> Seq.index ints (j - 1) <= Seq.index ints j);
    Classical.forall_intro_2 (Classical.move_requires_2 (adj_step_prefix ints k))

// ================================================================
// c_sorted_boundary_implies_prefix_leq_suffix
// ================================================================

#push-options "--z3rlimit 20"
let c_sorted_boundary_implies_prefix_leq_suffix
  (s: Seq.seq (option I32.t)) (n k: nat)
  = let ints = extract_ints s n in
    // sorted_prefix on ints: a[i] <= a[i+1] for i < k-1
    assert (forall (j: nat). j > 0 /\ j < k ==> Seq.index ints (j - 1) <= Seq.index ints j);
    // Use adj_step_prefix to get: i < j < k ==> a[i] <= a[j]
    Classical.forall_intro_2 (Classical.move_requires_2 (adj_step_prefix ints k));
    // Now: for i < k, a[i] <= a[k-1] (from sorted_prefix transitivity)
    assert (forall (i: nat). i < k ==> Seq.index ints i <= Seq.index ints (k - 1));
    // And: for j >= k, a[k-1] <= a[j] (from boundary)
    assert (forall (j: nat). k <= j /\ j < n ==> Seq.index ints (k - 1) <= Seq.index ints j);
    // Combined: for i < k, j >= k: a[i] <= a[k-1] <= a[j]
    ()
#pop-options

// ================================================================
// swap_extract_permutation
// ================================================================

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let swap_extract_permutation
  (s: Seq.seq (option I32.t)) (len: nat) (i j: nat)
  = let s' = Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
    let ints = extract_ints s len in
    let ints' = extract_ints s' len in
    let ints_swapped = Seq.upd (Seq.upd ints i (Seq.index ints j)) j (Seq.index ints i) in
    assert (Seq.equal ints' ints_swapped);
    reveal_opaque (`%PSSImpl.permutation) (PSSImpl.permutation ints ints');
    if i = j then (
      Seq.lemma_index_upd1 ints i (Seq.index ints j);
      Seq.lemma_eq_elim (Seq.upd ints i (Seq.index ints j)) ints;
      Seq.lemma_index_upd1 (Seq.upd ints i (Seq.index ints j)) j (Seq.index ints i);
      Seq.lemma_eq_elim ints_swapped ints
    ) else (
      let sw = Seq.swap ints (if i < j then i else j) (if i < j then j else i) in
      let aux (k: nat{k < len})
        : Lemma (Seq.index ints_swapped k == Seq.index sw k) = ()
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_elim ints_swapped sw;
      if i < j then SeqP.lemma_swap_permutes ints i j
      else SeqP.lemma_swap_permutes ints j i
    )
#pop-options

// ================================================================
// unchanged_extract_eq
// ================================================================

let unchanged_extract_eq
  (s1 s2: Seq.seq (option I32.t)) (len: nat)
  = let ints1 = extract_ints s1 len in
    let ints2 = extract_ints s2 len in
    assert (forall (k: nat). k < len ==> Seq.index ints1 k == Seq.index ints2 k)

// ================================================================
// no_fabrication_extract
// ================================================================

let no_fabrication_extract
  (s_old s_new: Seq.seq (option I32.t)) (n: nat)
  = let ints_old = extract_ints s_old n in
    let ints_new = extract_ints s_new n in
    assert (forall (p: nat). p < n ==> Seq.index ints_new p == I32.v (Some?.v (Seq.index s_new p)));
    assert (forall (m: nat). m < n ==> Seq.index ints_old m == I32.v (Some?.v (Seq.index s_old m)))

// ================================================================
// select_correctness_bridge
// ================================================================

#push-options "--z3rlimit 40"
let select_correctness_bridge (s0 s_final: Seq.seq int) (k: nat)
  = let p = k - 1 in
    reveal_opaque (`%PSSImpl.permutation) (PSSImpl.permutation s0 s_final);
    PSSLemmas.seq_perm_implies_is_perm s0 s_final;
    PSSLemmas.pulse_correctness_hint s0 s_final p
#pop-options
