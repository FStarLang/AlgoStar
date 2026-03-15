module CLRS.Ch11.HashTable.Lemmas

(**
   Refinement bridge between the pure Spec model and the Pulse implementation.

   Proves:
   1. Linear probing covers all positions (surjectivity)
   2. key_in_table <==> array_has_key (membership equivalence)
   3. probes_not_key for all probes <==> ~(array_has_key)
   4. Array-to-model correspondence with the Spec's mem
*)

open FStar.Classical
open FStar.Mul

module Impl = CLRS.Ch11.HashTable.Impl
module Spec = CLRS.Ch11.HashTable.Spec
module Seq = FStar.Seq

(** Simple array membership: key exists at some index *)
val array_has_key (s: Seq.seq int) (k: nat) : prop

(** Build model from the full array *)
val array_to_model (s: Seq.seq int) : Spec.ht_model

(** Lemma 1: For any target position j, a probe p exists with hash_probe_nat key p size == j *)
val lemma_linear_probe_surjective
  (key: int{key >= 0}) (size: nat{size > 0}) (j: nat{j < size})
  : Lemma (exists (p: nat). p < size /\ Impl.hash_probe_nat key p size == j)

(** Lemma 2: key_in_table <==> array_has_key *)
val lemma_key_in_table_iff_array_has_key
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (Impl.key_in_table s size key <==> array_has_key s key)

(** Lemma 3: probes_not_key for all probes <==> ~(array_has_key) *)
val lemma_probes_not_key_full_iff
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (Impl.probes_not_key s size key size <==> ~(array_has_key s key))

(** Lemma 4: Spec.mem in the model <==> array_has_key *)
val lemma_array_to_model_mem_full
  (s: Seq.seq int) (k: nat)
  : Lemma (Spec.mem (array_to_model s) k <==> array_has_key s k)

(** Lemma 5: If unique_key holds and delete removes the key (one slot from key
    to -2, rest unchanged), then the key is absent from the table.
    This closes Review.md limitation 7: delete now guarantees key absence
    when uniqueness is maintained (e.g., via hash_insert_no_dup). *)
val lemma_delete_unique_guarantees_absence
  (s s': Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s})
  (key: int{key >= 0})
  (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s})
  : Lemma
    (requires
      Impl.unique_key s key /\
      Seq.index s idx == key /\
      Seq.index s' idx == -2 /\
      Impl.seq_modified_at s s' idx)
    (ensures ~(Impl.key_in_table s' size key))

(** Lemma 6: After a fresh insert (key was absent, inserted at one position),
    the key is unique in the new table. *)
val lemma_insert_fresh_unique_key
  (s s': Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s})
  (key: int{key >= 0})
  (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s})
  : Lemma
    (requires
      ~(Impl.key_in_table s size key) /\
      Seq.index s' idx == key /\
      Impl.seq_modified_at s s' idx)
    (ensures Impl.unique_key s' key)

(** Lemma 7: Spec model connection — after insert, key is present in the Spec model.
    Bridges Review.md limitation 6: connects Impl postconditions to Spec model. *)
val lemma_key_in_table_spec_mem
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: nat)
  : Lemma
    (requires Impl.key_in_table s size key)
    (ensures Spec.mem (array_to_model s) key)

(** Lemma 8: Spec model connection — key absent from table means absent from Spec model. *)
val lemma_key_absent_spec_not_mem
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: nat)
  : Lemma
    (requires ~(Impl.key_in_table s size key))
    (ensures ~(Spec.mem (array_to_model s) key))
