(*
   CLRS Chapter 7: Partition — Definitions and Lemma Signatures

   Shared definitions for the Lomuto partition algorithm:
   - Sequence swap, bounds predicates, partition predicate
   - Complexity predicate for exact linear cost

   Lemma signatures for correctness proofs:
   - Swap commutativity and permutation preservation
   - Bounds transfer for slices
*)
module CLRS.Ch07.Partition.Lemmas

open CLRS.Common.SortSpec
module Seq = FStar.Seq

// ========== Shared definitions ==========

let nat_smaller (n: nat) = i:nat{i < n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) : GTot _ =
  Seq.swap s j i

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let strictly_larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb < Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

// Linear bound: cf - c0 = n (exactly n operations)
let complexity_exact_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

// ========== Lemma signatures ==========

val seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (seq_swap s i j == seq_swap s j i)

val permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]

val transfer_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)))
    (ensures larger_than (Seq.slice s (l - shift) (r - shift)) lb)

val transfer_smaller_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb))
    (ensures smaller_than (Seq.slice s (l - shift) (r - shift)) rb)

val transfer_strictly_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (lb < Seq.index s (k - shift)))
    (ensures strictly_larger_than (Seq.slice s (l - shift) (r - shift)) lb)
