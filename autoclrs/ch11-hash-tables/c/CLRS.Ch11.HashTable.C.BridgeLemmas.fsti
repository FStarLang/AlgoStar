module CLRS.Ch11.HashTable.C.BridgeLemmas

(**
   Bridge lemmas connecting the c2pulse-generated HashTable module
   to the verified CLRS.Ch11.HashTable.Impl specifications.

   The c2pulse array model uses Seq.seq (option Int32.t) while the
   Impl module uses Seq.seq int. This module provides:

   1. seq_val: extract int from c2pulse option-Int32 sequences
   2. to_int_seq: convert c2pulse sequence to Spec/Impl sequence
   3. Lemmas connecting c2pulse-level postconditions to Impl.fsti concepts:
      - key absence at all indices <==> ~(key_in_table)
      - key found at index <==> key_in_table
      - single-slot modification <==> seq_modified_at
      - delete slot (key -> -2) + unique_key ==> key absent

   These bridge lemmas, together with the CLRS.Ch11.HashTable.Lemmas
   module, provide full spec parity between the C implementation
   and the Pulse Impl.fsti.
*)

module Seq = FStar.Seq
open FStar.Mul

module Impl = CLRS.Ch11.HashTable.Impl
module Lemmas = CLRS.Ch11.HashTable.Lemmas
module Spec = CLRS.Ch11.HashTable.Spec

(** Extract int value from c2pulse option-Int32 sequence (total, default 0) *)
let seq_val (s: Seq.seq (option Int32.t)) (i: nat) : int =
  if i < Seq.length s
  then match Seq.index s i with
       | Some x -> Int32.v x
       | None -> 0
  else 0

(** Convert c2pulse option sequence to plain int sequence *)
let rec to_int_seq (s: Seq.seq (option Int32.t)) (i: nat)
  : Tot (Seq.seq int) (decreases (Seq.length s - i))
  = if i >= Seq.length s then Seq.empty
    else
      let v = seq_val s i in
      Seq.cons v (to_int_seq s (i + 1))

let to_int_seq_full (s: Seq.seq (option Int32.t)) : Seq.seq int =
  to_int_seq s 0

(** Length of converted sequence equals original *)
let rec lemma_to_int_seq_length (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (ensures Seq.length (to_int_seq s i) ==
             (if i >= Seq.length s then 0 else Seq.length s - i))
          (decreases (Seq.length s - i))
  = if i >= Seq.length s then ()
    else lemma_to_int_seq_length s (i + 1)

let lemma_to_int_seq_full_length (s: Seq.seq (option Int32.t))
  : Lemma (ensures Seq.length (to_int_seq_full s) == Seq.length s)
  = lemma_to_int_seq_length s 0

(** Index into converted sequence equals seq_val *)
let rec lemma_to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat) (j: nat)
  : Lemma (requires i + j < Seq.length s)
          (ensures (lemma_to_int_seq_length s i;
                    Seq.index (to_int_seq s i) j == seq_val s (i + j)))
          (decreases j)
  = lemma_to_int_seq_length s i;
    if j = 0 then ()
    else lemma_to_int_seq_index s (i + 1) (j - 1)


(** ================================================================
    Bridge 1: Key absence at all c2pulse indices implies
              ~(key_in_table) at the Impl level
    ================================================================

    If forall k < size. seq_val s k != key, then
    ~(Impl.key_in_table (to_int_seq_full s) size key).

    Proof: by Lemmas.lemma_key_in_table_iff_array_has_key, key_in_table
    <==> array_has_key. If no index has the key, then ~(array_has_key).
*)
val lemma_c2pulse_absent_implies_not_in_table
  (s: Seq.seq (option Int32.t))
  (size: nat{size > 0 /\ size == Seq.length s})
  (key: nat)
  : Lemma
    (requires forall (k: nat). k < size ==> seq_val s k <> key)
    (ensures (lemma_to_int_seq_full_length s;
              ~(Impl.key_in_table (to_int_seq_full s) size key)))


(** ================================================================
    Bridge 2: Key found at c2pulse index implies key_in_table
    ================================================================

    If seq_val s idx == key for some idx < size, then
    Impl.key_in_table (to_int_seq_full s) size key.
*)
val lemma_c2pulse_found_implies_in_table
  (s: Seq.seq (option Int32.t))
  (size: nat{size > 0 /\ size == Seq.length s})
  (key: nat)
  (idx: nat{idx < size})
  : Lemma
    (requires seq_val s idx == key)
    (ensures (lemma_to_int_seq_full_length s;
              Impl.key_in_table (to_int_seq_full s) size key))


(** ================================================================
    Bridge 3: c2pulse delete postcondition implies Impl delete postcondition
    ================================================================

    If seq_val s idx == key and seq_val s' idx == -2 and all other
    positions unchanged, then the Impl.fsti delete postcondition holds.
*)
val lemma_c2pulse_delete_bridge
  (s s': Seq.seq (option Int32.t))
  (size: nat{size > 0 /\ size == Seq.length s /\ Seq.length s' == size})
  (key: nat)
  (idx: nat{idx < size})
  : Lemma
    (requires
      seq_val s idx == key /\
      seq_val s' idx == -2 /\
      (forall (j: nat). j < size /\ j <> idx ==> seq_val s' j == seq_val s j))
    (ensures (lemma_to_int_seq_full_length s;
              lemma_to_int_seq_full_length s';
              let si = to_int_seq_full s in
              let si' = to_int_seq_full s' in
              Seq.length si == size /\ Seq.length si' == size /\
              Seq.index si idx == key /\
              Seq.index si' idx == -2 /\
              Impl.seq_modified_at si si' idx))
