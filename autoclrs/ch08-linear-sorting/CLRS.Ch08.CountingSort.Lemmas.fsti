(*
   Interface for Counting Sort lemmas.
   Definitions are transparent (let); lemma proofs are abstract (val).
*)

module CLRS.Ch08.CountingSort.Lemmas

open FStar.Seq
open CLRS.Ch08.CountingSort.Spec
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Spec = CLRS.Ch08.CountingSort.Spec

// ========== Proof helper definitions (transparent) ==========

let counts_match_prefix (c:Seq.seq int) (input:Seq.seq nat) (k:nat) (prefix_len:nat) : prop =
  Seq.length c == k + 1 /\
  prefix_len <= Seq.length input /\
  (forall (v:nat). v <= k ==> Seq.index c v == SeqP.count v (Seq.slice input 0 prefix_len))

let counts_match (c:Seq.seq int) (input:Seq.seq nat) (k:nat) : prop =
  counts_match_prefix c input k (Seq.length input)

let phase2_inv (sa s0:Seq.seq nat) (pos:nat) (cur_v:nat) (k:nat) : prop =
  Seq.length sa == Seq.length s0 /\
  pos <= Seq.length sa /\
  sorted_prefix sa pos /\
  (pos > 0 ==> Seq.index sa (pos - 1) < cur_v) /\
  (forall (w:nat). w < cur_v ==> 
    SeqP.count w (Seq.slice sa 0 pos) == SeqP.count w s0) /\
  (forall (w:nat). w >= cur_v ==>
    SeqP.count w (Seq.slice sa 0 pos) == 0)

let seq_remove (#a:eqtype) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Seq.seq a
  = Seq.append (Seq.slice s 0 i) (Seq.slice s (i+1) (Seq.length s))

// ========== Lemma signatures ==========

val permutation_same_length (s1 s2 : Seq.seq nat)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]

val equal_counts_perm (s1 s2:Seq.seq nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    (forall (v:nat). SeqP.count v s1 == SeqP.count v s2))
          (ensures permutation s1 s2)

val empty_sorted_perm (s1 s2: Seq.seq nat)
  : Lemma (requires Seq.length s1 == 0 /\ Seq.length s2 == 0)
          (ensures sorted s1 /\ permutation s1 s2)

val count_bounded (s:Seq.seq nat) (v:nat)
  : Lemma (ensures SeqP.count v s <= Seq.length s)

val count_extend (s:Seq.seq nat) (j:nat{j < Seq.length s}) (v:nat)
  : Lemma (ensures SeqP.count v (Seq.slice s 0 (j+1)) ==
                   SeqP.count v (Seq.slice s 0 j) + (if Seq.index s j = v then 1 else 0))

val count_phase_step (s0:Seq.seq nat) (sc sc':Seq.seq int) 
  (j:nat) (k:nat) (val_j:nat)
  : Lemma (requires j < Seq.length s0 /\
                    Seq.length sc == k + 1 /\
                    Seq.length sc' == k + 1 /\
                    val_j == Seq.index s0 j /\
                    val_j <= k /\
                    (forall (v:nat). v <= k ==> Seq.index sc v == SeqP.count v (Seq.slice s0 0 j)) /\
                    (forall (v:nat). v <= k ==> 
                      Seq.index sc' v == (if v = val_j then Seq.index sc v + 1 else Seq.index sc v)))
          (ensures forall (v:nat). v <= k ==> Seq.index sc' v == SeqP.count v (Seq.slice s0 0 (j + 1)))

val seq_remove_length (#a:eqtype) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures Seq.length (seq_remove s i) == Seq.length s - 1)

val seq_remove_count (#a:eqtype) (s:Seq.seq a) (i:nat{i < Seq.length s}) (w:a)
  : Lemma (ensures SeqP.count w (seq_remove s i) == 
                   SeqP.count w s - (if w = Seq.index s i then 1 else 0))

val count_create (n:nat) (x:nat) (w:nat)
  : Lemma (ensures SeqP.count w (Seq.create n x) == (if w = x then n else 0))

val count_le_length_le (s1 s2: Seq.seq nat)
  : Lemma (requires forall (w:nat). SeqP.count w s1 <= SeqP.count w s2)
          (ensures Seq.length s1 <= Seq.length s2)

val phase2_pos_bound (sa s0:Seq.seq nat) (pos:nat) (cur_v:nat) (k:nat)
  : Lemma (requires phase2_inv sa s0 pos cur_v k /\ in_range s0 k /\ cur_v <= k)
          (ensures pos + SeqP.count cur_v s0 <= Seq.length s0)

val write_extend_sorted (s s':Seq.seq nat) (pos:nat) (val_w:nat)
  : Lemma (requires Seq.length s == Seq.length s' /\
                    pos < Seq.length s /\
                    Seq.index s' pos == val_w /\
                    (forall (i:nat). i < pos ==> Seq.index s' i == Seq.index s i) /\
                    sorted_prefix s pos /\
                    (pos > 0 ==> Seq.index s (pos - 1) <= val_w))
          (ensures sorted_prefix s' (pos + 1))

val write_block_sorted (s:Seq.seq nat) (pos:nat) (cnt:nat) (val_w:nat)
  : Lemma (requires pos + cnt <= Seq.length s /\
                    (forall (i:nat). pos <= i /\ i < pos + cnt ==> Seq.index s i == val_w) /\
                    sorted_prefix s pos /\
                    (pos > 0 ==> Seq.index s (pos - 1) <= val_w))
          (ensures sorted_prefix s (pos + cnt) /\
                  (pos + cnt > 0 ==> Seq.index s (pos + cnt - 1) <= val_w))

val block_count (s:Seq.seq nat) (pos:nat) (cnt:nat) (val_w:nat) (v:nat)
  : Lemma (requires pos + cnt <= Seq.length s /\
                    (forall (i:nat). pos <= i /\ i < pos + cnt ==> Seq.index s i == val_w))
          (ensures SeqP.count v (Seq.slice s 0 (pos + cnt)) ==
                   SeqP.count v (Seq.slice s 0 pos) + (if v = val_w then cnt else 0))

val final_perm (s0 sa:Seq.seq nat) (k:nat) (pos:nat)
  : Lemma (requires Seq.length sa >= Seq.length s0 /\
                    in_range s0 k /\
                    phase2_inv sa s0 pos (k + 1) k)
          (ensures pos == Seq.length s0 /\
                   permutation s0 (Seq.slice sa 0 pos) /\
                   sorted (Seq.slice sa 0 pos))

val phase2_step (sa_before sa_after s0:Seq.seq nat) (pos:nat) (cnt:nat) (cur_v:nat) (k:nat)
  : Lemma (requires phase2_inv sa_before s0 pos cur_v k /\
                    Seq.length sa_after == Seq.length s0 /\
                    pos + cnt <= Seq.length sa_after /\
                    cnt == SeqP.count cur_v s0 /\
                    cur_v <= k /\
                    (forall (i:nat). pos <= i /\ i < pos + cnt ==> Seq.index sa_after i == cur_v) /\
                    (forall (i:nat). i < pos ==> Seq.index sa_after i == Seq.index sa_before i) /\
                    (forall (i:nat). pos + cnt <= i /\ i < Seq.length sa_after ==>
                      Seq.index sa_after i == Seq.index sa_before i))
          (ensures phase2_inv sa_after s0 (pos + cnt) (cur_v + 1) k)
