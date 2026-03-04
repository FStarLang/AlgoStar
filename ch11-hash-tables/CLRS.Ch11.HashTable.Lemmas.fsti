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
