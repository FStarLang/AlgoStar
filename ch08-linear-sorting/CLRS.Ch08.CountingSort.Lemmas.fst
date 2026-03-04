(*
   Pure F* lemmas for Counting Sort verification.
   Definitions are in CountingSort.Spec; this module proves lemmas about them.
   Separated from the Pulse code to avoid #lang-pulse integer literal overloading.
*)

module CLRS.Ch08.CountingSort.Lemmas

open FStar.Seq
open CLRS.Ch08.CountingSort.Spec
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical
module Spec = CLRS.Ch08.CountingSort.Spec

// Definitions (counts_match_prefix, counts_match, phase2_inv, seq_remove) are in Lemmas.fsti

// ========== Permutation lemmas ==========

let permutation_same_length (s1 s2 : Seq.seq nat)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%Spec.permutation) (Spec.permutation s1 s2);
    SeqP.perm_len s1 s2

let equal_counts_perm (s1 s2:Seq.seq nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    (forall (v:nat). SeqP.count v s1 == SeqP.count v s2))
          (ensures permutation s1 s2)
  = reveal_opaque (`%Spec.permutation) (Spec.permutation s1 s2)

// ========== Count lemmas ==========

/// Count of any element is bounded by sequence length
let rec count_bounded (s:Seq.seq nat) (v:nat)
  : Lemma (ensures SeqP.count v s <= Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_bounded (Seq.tail s) v

#push-options "--z3rlimit 10"
let count_extend (s:Seq.seq nat) (j:nat{j < Seq.length s}) (v:nat)
  : Lemma (ensures SeqP.count v (Seq.slice s 0 (j+1)) ==
                   SeqP.count v (Seq.slice s 0 j) + (if Seq.index s j = v then 1 else 0))
  = let sl1 = Seq.slice s 0 j in
    let sl2 = Seq.slice s 0 (j+1) in
    let elt = Seq.slice s j (j+1) in
    assert (Seq.equal sl2 (Seq.append sl1 elt));
    SeqP.lemma_append_count sl1 elt
#pop-options

let count_phase_step (s0:Seq.seq nat) (sc sc':Seq.seq int) 
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
  = let aux (v:nat{v <= k})
      : Lemma (Seq.index sc' v == SeqP.count v (Seq.slice s0 0 (j + 1)))
      = count_extend s0 j v
    in
    Classical.forall_intro (Classical.move_requires aux)

let seq_remove_length (#a:eqtype) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures Seq.length (seq_remove s i) == Seq.length s - 1)
  = ()

let seq_remove_count (#a:eqtype) (s:Seq.seq a) (i:nat{i < Seq.length s}) (w:a)
  : Lemma (ensures SeqP.count w (seq_remove s i) == 
                   SeqP.count w s - (if w = Seq.index s i then 1 else 0))
  = let lo = Seq.slice s 0 i in
    let hi = Seq.slice s (i+1) (Seq.length s) in
    let mid = Seq.slice s i (i+1) in
    assert (Seq.equal (Seq.append lo (Seq.append mid hi)) s);
    SeqP.lemma_append_count_aux w lo (Seq.append mid hi);
    SeqP.lemma_append_count_aux w mid hi;
    SeqP.lemma_append_count_aux w lo hi

/// Count of elements in Seq.create
let rec count_create (n:nat) (x:nat) (w:nat)
  : Lemma (ensures SeqP.count w (Seq.create n x) == (if w = x then n else 0))
          (decreases n)
  = if n = 0 then (
      assert (Seq.length (Seq.create 0 x) == 0);
      assert (Seq.equal (Seq.create 0 x) Seq.empty)
    )
    else (
      assert (Seq.head (Seq.create n x) == x);
      assert (Seq.equal (Seq.tail (Seq.create n x)) (Seq.create (n-1) x));
      count_create (n-1) x w
    )

/// If for every element, count in s1 <= count in s2, then length s1 <= length s2
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let rec count_le_length_le (s1 s2: Seq.seq nat)
  : Lemma (requires forall (w:nat). SeqP.count w s1 <= SeqP.count w s2)
          (ensures Seq.length s1 <= Seq.length s2)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else (
      let x = Seq.head s1 in
      let t1 = Seq.tail s1 in
      assert (SeqP.count x s1 >= 1);
      assert (SeqP.count x s2 >= 1);
      assert (SeqP.mem x s2);
      let i = SeqP.index_mem x s2 in
      let s2' = seq_remove s2 i in
      assert (Seq.index s2 i == x);
      let aux (w:nat) : Lemma (SeqP.count w t1 <= SeqP.count w s2') =
        seq_remove_count s2 i w
      in
      Classical.forall_intro aux;
      count_le_length_le t1 s2'
    )
#pop-options

/// Given phase2_inv, the next block fits: pos + count(cur_v, s0) <= length s0
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let phase2_pos_bound (sa s0:Seq.seq nat) (pos:nat) (cur_v:nat) (k:nat)
  : Lemma (requires phase2_inv sa s0 pos cur_v k /\ in_range s0 k /\ cur_v <= k)
          (ensures pos + SeqP.count cur_v s0 <= Seq.length s0)
  = let prefix = Seq.slice sa 0 pos in
    let cnt = SeqP.count cur_v s0 in
    let block = Seq.create cnt cur_v in
    let extended = Seq.append prefix block in
    Seq.lemma_len_append prefix block;
    SeqP.lemma_mem_count s0 (fun x -> x <= k);
    let aux (w:nat) : Lemma (SeqP.count w extended <= SeqP.count w s0) =
      SeqP.lemma_append_count_aux w prefix block;
      count_create cnt cur_v w
    in
    Classical.forall_intro aux;
    count_le_length_le extended s0
#pop-options

/// Extending a sorted prefix by one element of value >= all existing elements
#push-options "--z3rlimit 40"
let write_extend_sorted (s s':Seq.seq nat) (pos:nat) (val_w:nat)
  : Lemma (requires Seq.length s == Seq.length s' /\
                    pos < Seq.length s /\
                    Seq.index s' pos == val_w /\
                    (forall (i:nat). i < pos ==> Seq.index s' i == Seq.index s i) /\
                    sorted_prefix s pos /\
                    (pos > 0 ==> Seq.index s (pos - 1) <= val_w))
          (ensures sorted_prefix s' (pos + 1))
  = assert (forall (i:nat). i < pos ==> Seq.index s' i <= val_w);
    assert (sorted_prefix s' pos);
    assert (forall (i j:nat). i <= j /\ j < pos + 1 ==> Seq.index s' i <= Seq.index s' j)
#pop-options

/// After writing cnt copies of val_w at positions [pos, pos+cnt), sorted_prefix and counts
#push-options "--z3rlimit 30"
let write_block_sorted (s:Seq.seq nat) (pos:nat) (cnt:nat) (val_w:nat)
  : Lemma (requires pos + cnt <= Seq.length s /\
                    (forall (i:nat). pos <= i /\ i < pos + cnt ==> Seq.index s i == val_w) /\
                    sorted_prefix s pos /\
                    (pos > 0 ==> Seq.index s (pos - 1) <= val_w))
          (ensures sorted_prefix s (pos + cnt) /\
                  (pos + cnt > 0 ==> Seq.index s (pos + cnt - 1) <= val_w))
  = assert (forall (i:nat). i < pos ==> Seq.index s i <= val_w)
#pop-options

/// Count of a block: cnt copies of val_w contribute cnt to count of val_w, 0 to others
let rec block_count (s:Seq.seq nat) (pos:nat) (cnt:nat) (val_w:nat) (v:nat)
  : Lemma (requires pos + cnt <= Seq.length s /\
                    (forall (i:nat). pos <= i /\ i < pos + cnt ==> Seq.index s i == val_w))
          (ensures SeqP.count v (Seq.slice s 0 (pos + cnt)) ==
                   SeqP.count v (Seq.slice s 0 pos) + (if v = val_w then cnt else 0))
          (decreases cnt)
  = if cnt = 0 then ()
    else (
      block_count s pos (cnt - 1) val_w v;
      count_extend s (pos + cnt - 1) v
    )

/// Final lemma: after all values 0..k are written with correct counts,
/// the output has same counts as input => permutation
let final_perm (s0 sa:Seq.seq nat) (k:nat) (pos:nat)
  : Lemma (requires Seq.length sa >= Seq.length s0 /\
                    in_range s0 k /\
                    phase2_inv sa s0 pos (k + 1) k)
          (ensures pos == Seq.length s0 /\
                   permutation s0 (Seq.slice sa 0 pos) /\
                   sorted (Seq.slice sa 0 pos))
  = let prefix = Seq.slice sa 0 pos in
    SeqP.lemma_mem_count s0 (fun x -> x <= k);
    let aux (v:nat) : Lemma (SeqP.count v prefix == SeqP.count v s0) =
      if v <= k then (
        assert (v < k + 1)
      ) else (
        assert (SeqP.count v prefix == 0);
        assert (SeqP.count v s0 == 0)
      )
    in
    Classical.forall_intro aux;
    count_le_length_le prefix s0;
    count_le_length_le s0 prefix;
    equal_counts_perm s0 prefix

/// Combined phase 2 step: after writing cnt copies of cur_v at [pos, pos+cnt)
/// Phase 2 invariant holds for cur_v+1
#push-options "--z3rlimit 100"
let phase2_step (sa_before sa_after s0:Seq.seq nat) (pos:nat) (cnt:nat) (cur_v:nat) (k:nat)
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
  = write_block_sorted sa_after pos cnt cur_v;
    assert (Seq.equal (Seq.slice sa_after 0 pos) (Seq.slice sa_before 0 pos));
    let aux_count (v:nat)
      : Lemma (SeqP.count v (Seq.slice sa_after 0 (pos + cnt)) ==
               SeqP.count v (Seq.slice sa_before 0 pos) + (if v = cur_v then cnt else 0))
      = block_count sa_after pos cnt cur_v v
    in
    Classical.forall_intro aux_count;
    let aux_match (w:nat)
      : Lemma (requires w < cur_v + 1)
              (ensures SeqP.count w (Seq.slice sa_after 0 (pos + cnt)) == SeqP.count w s0)
      = block_count sa_after pos cnt cur_v w;
        if w < cur_v then (
          assert (SeqP.count w (Seq.slice sa_before 0 pos) == SeqP.count w s0)
        ) else (
          assert (SeqP.count w (Seq.slice sa_before 0 pos) == 0);
          assert (cnt == SeqP.count cur_v s0)
        )
    in
    Classical.forall_intro (Classical.move_requires aux_match);
    let aux_zero (w:nat)
      : Lemma (requires w >= cur_v + 1)
              (ensures SeqP.count w (Seq.slice sa_after 0 (pos + cnt)) == 0)
      = block_count sa_after pos cnt cur_v w;
        assert (SeqP.count w (Seq.slice sa_before 0 pos) == 0)
    in
    Classical.forall_intro (Classical.move_requires aux_zero)
#pop-options
