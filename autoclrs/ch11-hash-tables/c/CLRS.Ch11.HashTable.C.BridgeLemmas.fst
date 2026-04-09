module CLRS.Ch11.HashTable.C.BridgeLemmas

(**
   Bridge lemma proofs connecting c2pulse representation to Impl.fsti.
*)

module Seq = FStar.Seq
open FStar.Mul

module Impl = CLRS.Ch11.HashTable.Impl
module Lemmas = CLRS.Ch11.HashTable.Lemmas
module Spec = CLRS.Ch11.HashTable.Spec


(** Extract int value from c2pulse option-Int32 sequence *)
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
    else Seq.cons (seq_val s i) (to_int_seq s (i + 1))

let to_int_seq_full (s: Seq.seq (option Int32.t)) : Seq.seq int =
  to_int_seq s 0

let rec lemma_to_int_seq_length (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (ensures Seq.length (to_int_seq s i) ==
             (if i >= Seq.length s then 0 else Seq.length s - i))
          (decreases (Seq.length s - i))
  = if i >= Seq.length s then ()
    else lemma_to_int_seq_length s (i + 1)

let lemma_to_int_seq_full_length (s: Seq.seq (option Int32.t))
  : Lemma (ensures Seq.length (to_int_seq_full s) == Seq.length s)
  = lemma_to_int_seq_length s 0

let rec lemma_to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat) (j: nat)
  : Lemma (requires i + j < Seq.length s)
          (ensures (lemma_to_int_seq_length s i;
                    Seq.index (to_int_seq s i) j == seq_val s (i + j)))
          (decreases j)
  = lemma_to_int_seq_length s i;
    if j = 0 then ()
    else lemma_to_int_seq_index s (i + 1) (j - 1)


(** ================================================================
    Bridge 1: Key absence
    ================================================================ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let lemma_c2pulse_absent_implies_not_in_table
  (s: Seq.seq (option Int32.t))
  (size: nat{size > 0 /\ size == Seq.length s})
  (key: nat)
  : Lemma
    (requires forall (k: nat). k < size ==> seq_val s k <> key)
    (ensures (lemma_to_int_seq_full_length s;
              ~(Impl.key_in_table (to_int_seq_full s) size key)))
  = lemma_to_int_seq_full_length s;
    let si = to_int_seq_full s in
    // Show: for all j < size, Seq.index si j <> key
    introduce forall (j: nat). j < size ==> Seq.index si j =!= key
    with introduce _ ==> _
    with _. (
      lemma_to_int_seq_index s 0 j;
      assert (Seq.index si j == seq_val s j);
      assert (seq_val s j <> key)
    );
    // key_in_table requires exists probe. hash_probe_nat key probe size < size /\ index == key
    // But hash_probe_nat always returns < size, and all such indices != key
    introduce forall (probe: nat). probe < size ==> Seq.index si (Impl.hash_probe_nat key probe size) =!= key
    with introduce _ ==> _
    with _. (
      Impl.lemma_hash_probe_nat_in_bounds key probe size
    )
#pop-options


(** ================================================================
    Bridge 2: Key found
    ================================================================ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let lemma_c2pulse_found_implies_in_table
  (s: Seq.seq (option Int32.t))
  (size: nat{size > 0 /\ size == Seq.length s})
  (key: nat)
  (idx: nat{idx < size})
  : Lemma
    (requires seq_val s idx == key)
    (ensures (lemma_to_int_seq_full_length s;
              Impl.key_in_table (to_int_seq_full s) size key))
  = lemma_to_int_seq_full_length s;
    let si = to_int_seq_full s in
    lemma_to_int_seq_index s 0 idx;
    assert (Seq.index si idx == key);
    // Use surjectivity: there exists a probe p s.t. hash_probe_nat key p size == idx
    Lemmas.lemma_linear_probe_surjective key size idx;
    // Now Z3 can construct the existential witness for key_in_table
    assert (Impl.key_in_table si size key)
#pop-options


(** ================================================================
    Bridge 3: Delete bridge
    ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let lemma_c2pulse_delete_bridge
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
  = lemma_to_int_seq_full_length s;
    lemma_to_int_seq_full_length s';
    let si = to_int_seq_full s in
    let si' = to_int_seq_full s' in
    // Index at idx
    lemma_to_int_seq_index s 0 idx;
    lemma_to_int_seq_index s' 0 idx;
    // All other positions unchanged
    introduce forall (j: nat).
      j < Seq.length si /\ j =!= idx ==> Seq.index si j == Seq.index si' j
    with introduce _ ==> _
    with _. (
      lemma_to_int_seq_index s 0 j;
      lemma_to_int_seq_index s' 0 j
    )
#pop-options
