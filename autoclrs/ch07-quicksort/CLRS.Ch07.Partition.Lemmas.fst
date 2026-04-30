(*
   CLRS Chapter 7: Partition — Lemma Proofs

   Proves:
   - seq_swap commutativity
   - Swap preserves permutation (with SMT pattern)
   - Bounds transfer for slices (larger_than, smaller_than)

   NO admits. NO assumes.
*)
module CLRS.Ch07.Partition.Lemmas

open CLRS.Common.SortSpec
module Seq = FStar.Seq

let seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (seq_swap s i j == seq_swap s j i)
  = let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji

let permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
  = reveal_opaque (`%permutation) (permutation s (seq_swap s i j));
    if i <= j
      then (Seq.Properties.lemma_swap_permutes s i j; seq_swap_commute s i j)
      else Seq.Properties.lemma_swap_permutes s j i

// These lemmas relate forall-quantified preconditions to slice-based postconditions.
// Split queries isolate the postcondition sub-query from ground terms, preventing
// Z3 from instantiating the quantifiers. Disable split_queries here.
#push-options "--split_queries no"
let transfer_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)))
    (ensures larger_than (Seq.slice s (l - shift) (r - shift)) lb)
  = assert (forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)));
    assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (lb <= Seq.index s ((k+shift) - shift)));
    assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (lb <= Seq.index s k))

// transfer_smaller_slice and transfer_strictly_larger_slice need ifuel 2
// for deterministic Seq.slice quantifier instantiation.
#restart-solver
#push-options "--ifuel 2"
let transfer_smaller_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb))
    (ensures smaller_than (Seq.slice s (l - shift) (r - shift)) rb)
  = assert (forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb));
    assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (Seq.index s ((k+shift) - shift) <= rb));
    assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (Seq.index s k <= rb))
#pop-options

// Restart solver to clear context from transfer_smaller_slice.
#restart-solver
#push-options "--ifuel 2"
let transfer_strictly_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (lb < Seq.index s (k - shift)))
    (ensures strictly_larger_than (Seq.slice s (l - shift) (r - shift)) lb)
  = assert (forall (k: int). l <= k /\ k < r ==> (lb < Seq.index s (k - shift)));
    assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (lb < Seq.index s ((k+shift) - shift)));
    assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (lb < Seq.index s k))
#pop-options
#pop-options
