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
    Bridge 0: c_valid_ht <==> valid_ht equivalence
    ================================================================ *)

let c_valid_ht (s: Seq.seq (option Int32.t)) (sz: nat) : prop =
  sz > 0 /\ sz == Seq.length s /\
  (forall (k: nat) (probe: nat). {:pattern (seq_val s (Impl.hash_probe_nat k probe sz))}
    probe < sz /\ seq_val s (Impl.hash_probe_nat k probe sz) == k ==>
    (forall (p: nat). {:pattern (Impl.hash_probe_nat k p sz)}
      p < probe ==> seq_val s (Impl.hash_probe_nat k p sz) =!= -1))

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let lemma_c_valid_ht_iff_valid_ht
  (s: Seq.seq (option Int32.t))
  (sz: nat)
  : Lemma
    (requires sz > 0 /\ sz == Seq.length s)
    (ensures (lemma_to_int_seq_full_length s;
              c_valid_ht s sz <==> Impl.valid_ht (to_int_seq_full s) sz))
  = lemma_to_int_seq_full_length s;
    let si = to_int_seq_full s in
    // Show: seq_val s i == Seq.index si i for all i < sz
    introduce forall (i: nat). i < sz ==> seq_val s i == Seq.index si i
    with introduce _ ==> _
    with _. lemma_to_int_seq_index s 0 i;
    // Forward direction: c_valid_ht ==> valid_ht
    // Since seq_val s (hp k p sz) == Seq.index si (hp k p sz),
    // the quantified conditions transfer directly.
    // Backward direction: valid_ht ==> c_valid_ht
    // Same reasoning in reverse.
    // Note: valid_ht quantifies over k: int with k >= 0,
    // while c_valid_ht quantifies over k: nat. These are equivalent.
    assert (c_valid_ht s sz <==> Impl.valid_ht si sz) by (FStar.Tactics.V2.smt ())
#pop-options


(** ================================================================
    Bridge 0b: c_valid_ht preserved by insert
    ================================================================ *)

// Helper: seq_val commutes with Seq.upd
private let lemma_seq_val_upd_same
  (s: Seq.seq (option Int32.t)) (idx: nat{idx < Seq.length s}) (v: Int32.t)
  : Lemma (seq_val (Seq.upd s idx (Some v)) idx == Int32.v v)
  = ()

private let lemma_seq_val_upd_other
  (s: Seq.seq (option Int32.t)) (idx: nat{idx < Seq.length s}) (v: Int32.t) (j: nat)
  : Lemma (requires j <> idx)
          (ensures seq_val (Seq.upd s idx (Some v)) j == seq_val s j)
  = if j < Seq.length s then () else ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let lemma_c_valid_ht_insert
  (s: Seq.seq (option Int32.t)) (sz: nat)
  (key_v: Int32.t) (probe_i: nat{probe_i < sz})
  : Lemma
    (requires c_valid_ht s sz /\
              Int32.v key_v >= 0 /\
              (seq_val s (Impl.hash_probe_nat (Int32.v key_v) probe_i sz) == -1 \/
               seq_val s (Impl.hash_probe_nat (Int32.v key_v) probe_i sz) == -2) /\
              (forall (q: nat). q < probe_i ==>
                seq_val s (Impl.hash_probe_nat (Int32.v key_v) q sz) =!= -1 /\
                seq_val s (Impl.hash_probe_nat (Int32.v key_v) q sz) =!= -2))
    (ensures c_valid_ht (Seq.upd s (Impl.hash_probe_nat (Int32.v key_v) probe_i sz) (Some key_v)) sz)
  = let key = Int32.v key_v in
    let idx = Impl.hash_probe_nat key probe_i sz in
    let s' = Seq.upd s idx (Some key_v) in
    // Need: forall k probe. probe < sz /\ seq_val s' (hp k probe sz) == k ==>
    //   forall p. p < probe ==> seq_val s' (hp k p sz) =!= -1
    introduce forall (k: nat) (probe: nat).
      probe < sz /\ seq_val s' (Impl.hash_probe_nat k probe sz) == k ==>
      (forall (p: nat). p < probe ==> seq_val s' (Impl.hash_probe_nat k p sz) =!= -1)
    with introduce _ ==> _
    with _. (
      introduce forall (p: nat). p < probe ==> seq_val s' (Impl.hash_probe_nat k p sz) =!= -1
      with introduce _ ==> _
      with _. (
        let hp_kp = Impl.hash_probe_nat k p sz in
        if hp_kp = idx then (
          // This probe position is the newly-written slot: seq_val s' idx == key >= 0 =!= -1
          lemma_seq_val_upd_same s idx key_v
        ) else (
          // This probe position was not modified: seq_val s' hp_kp == seq_val s hp_kp
          lemma_seq_val_upd_other s idx key_v hp_kp;
          // Now use original c_valid_ht or the fact that slot wasn't -1
          let hp_kprobe = Impl.hash_probe_nat k probe sz in
          if hp_kprobe = idx then (
            // seq_val s' idx == key, so k == key
            lemma_seq_val_upd_same s idx key_v;
            // Since k == key and p < probe, hp_kp is an earlier probe for key
            // We need: seq_val s hp_kp =!= -1
            // Since the original slot at hp_kp was either:
            //  a) an earlier probe of key before probe_i: occupied (not -1, not -2, so not -1)
            //  b) something else: by original c_valid_ht
            ()
          ) else (
            // seq_val s' hp_kprobe == seq_val s hp_kprobe == k (from hypothesis)
            lemma_seq_val_upd_other s idx key_v hp_kprobe;
            // By original c_valid_ht: seq_val s hp_kp =!= -1
            ()
          )
        )
      )
    )
#pop-options


(** ================================================================
    Bridge 0c: c_valid_ht preserved by delete
    ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let lemma_c_valid_ht_delete
  (s: Seq.seq (option Int32.t)) (sz: nat)
  (idx: nat{idx < sz})
  : Lemma
    (requires c_valid_ht s sz /\ seq_val s idx >= 0)
    (ensures c_valid_ht (Seq.upd s idx (Some (Int32.int_to_t (-2))) ) sz)
  = let s' = Seq.upd s idx (Some (Int32.int_to_t (-2))) in
    introduce forall (k: nat) (probe: nat).
      probe < sz /\ seq_val s' (Impl.hash_probe_nat k probe sz) == k ==>
      (forall (p: nat). p < probe ==> seq_val s' (Impl.hash_probe_nat k p sz) =!= -1)
    with introduce _ ==> _
    with _. (
      introduce forall (p: nat). p < probe ==> seq_val s' (Impl.hash_probe_nat k p sz) =!= -1
      with introduce _ ==> _
      with _. (
        let hp_kp = Impl.hash_probe_nat k p sz in
        if hp_kp = idx then
          // This position now has -2, which is =!= -1
          lemma_seq_val_upd_same s idx (Int32.int_to_t (-2))
        else (
          lemma_seq_val_upd_other s idx (Int32.int_to_t (-2)) hp_kp;
          let hp_kprobe = Impl.hash_probe_nat k probe sz in
          if hp_kprobe = idx then (
            // seq_val s' idx == -2, but k >= 0 (since k: nat), so k =!= -2
            // Contradiction: seq_val s' idx == k requires k == -2, but k: nat
            lemma_seq_val_upd_same s idx (Int32.int_to_t (-2))
          ) else (
            lemma_seq_val_upd_other s idx (Int32.int_to_t (-2)) hp_kprobe
          )
        )
      )
    )
#pop-options


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


(** ================================================================
    Bridge 4: Probe-based absence → ~(c_key_in_table)
    ================================================================

    If ∀p < sz. seq_val s (hp key p sz) ≠ key, then ~(c_key_in_table).
    Proof: for any idx < sz, surjectivity gives a probe p with hp key p sz == idx,
    so seq_val s idx == seq_val s (hp key p sz) ≠ key.
*)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let lemma_probe_absent_not_in_table
  (s: Seq.seq (option Int32.t))
  (sz: nat{sz > 0 /\ sz == Seq.length s})
  (key: int{key >= 0})
  : Lemma
    (requires forall (p: nat). p < sz ==> seq_val s (Impl.hash_probe_nat key p sz) =!= key)
    (ensures ~(c_key_in_table s sz key))
  = introduce forall (idx: nat). idx < sz ==> seq_val s idx =!= key
    with introduce _ ==> _
    with _. (
      Lemmas.lemma_linear_probe_surjective key sz idx
      // Now ∃p < sz. hp key p sz == idx, so seq_val s idx == seq_val s (hp key p sz) ≠ key
    )
#pop-options


(** ================================================================
    Bridge 5: c_valid_ht + c_key_in_table → c_key_findable
    ================================================================

    If c_valid_ht and key exists at some index, then key is findable.
    Proof: surjectivity gives a probe for the index, and c_valid_ht
    guarantees no -1 appears before that probe.
*)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let lemma_valid_key_findable
  (s: Seq.seq (option Int32.t))
  (sz: nat{sz > 0 /\ sz == Seq.length s})
  (key: int{key >= 0})
  : Lemma
    (requires c_valid_ht s sz /\ c_key_in_table s sz key)
    (ensures c_key_findable s sz key)
  = // c_key_in_table: ∃idx < sz. seq_val s idx == key
    // For each such idx, surjectivity gives a probe
    introduce forall (idx: nat). idx < sz /\ seq_val s idx == key ==>
      (exists (probe: nat). probe < sz /\
        seq_val s (Impl.hash_probe_nat key probe sz) == key /\
        (forall (p: nat). {:pattern (Impl.hash_probe_nat key p sz)}
          p < probe ==> seq_val s (Impl.hash_probe_nat key p sz) =!= -1))
    with introduce _ ==> _
    with _. (
      Lemmas.lemma_linear_probe_surjective key sz idx
      // ∃p < sz. hp key p sz == idx
      // seq_val s (hp key p sz) == seq_val s idx == key
      // By c_valid_ht with k=key, probe=p:
      //   ∀q < p. seq_val s (hp key q sz) ≠ -1
    )
#pop-options
