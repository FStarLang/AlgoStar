(*
   CLRS Chapter 9.2: Quickselect — Lemmas

   Key result: if s1 is a permutation of s_pre, and they agree outside [lo, hi),
   then a bound on all values in s_pre[lo..hi) also holds for s1[lo..hi).

   This enables propagating ordering invariants through partition calls.

   NO admits. NO assumes.
*)
module CLRS.Ch09.Quickselect.Lemmas

open FStar.Seq
open FStar.Classical

module Seq = FStar.Seq

// ========== Slice equality from pointwise equality ==========

let slice_eq_from_pointwise (s1 s2: Seq.seq int) (a b: nat)
  : Lemma (requires a <= b /\ b <= Seq.length s1 /\ Seq.length s1 == Seq.length s2 /\
                    (forall (i: nat). a <= i /\ i < b ==> Seq.index s1 i == Seq.index s2 i))
          (ensures Seq.equal (Seq.slice s1 a b) (Seq.slice s2 a b))
  = ()

// ========== Count in range is permutation-invariant when outside is unchanged ==========

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let count_range_eq (s_pre s1: Seq.seq int) (lo hi: nat) (x: int)
  : Lemma (requires lo <= hi /\ hi <= Seq.length s_pre /\
                    Seq.length s_pre == Seq.length s1 /\
                    Seq.Properties.permutation int s_pre s1 /\
                    (forall (idx: nat). idx < Seq.length s1 ==>
                      (idx < lo \/ hi <= idx) ==>
                      Seq.index s1 idx == Seq.index s_pre idx))
          (ensures Seq.Properties.count x (Seq.slice s_pre lo hi) ==
                   Seq.Properties.count x (Seq.slice s1 lo hi))
  = let n = Seq.length s_pre in
    slice_eq_from_pointwise s_pre s1 0 lo;
    Seq.lemma_eq_elim (Seq.slice s_pre 0 lo) (Seq.slice s1 0 lo);
    slice_eq_from_pointwise s_pre s1 hi n;
    Seq.lemma_eq_elim (Seq.slice s_pre hi n) (Seq.slice s1 hi n);
    let pre_l = Seq.slice s_pre 0 lo in
    let pre_m = Seq.slice s_pre lo hi in
    let pre_r = Seq.slice s_pre hi n in
    let s1_m = Seq.slice s1 lo hi in
    Seq.lemma_eq_elim s_pre (Seq.append pre_l (Seq.append pre_m pre_r));
    Seq.lemma_eq_elim s1 (Seq.append pre_l (Seq.append s1_m pre_r));
    Seq.Properties.lemma_append_count_aux x pre_l (Seq.append pre_m pre_r);
    Seq.Properties.lemma_append_count_aux x pre_m pre_r;
    Seq.Properties.lemma_append_count_aux x pre_l (Seq.append s1_m pre_r);
    Seq.Properties.lemma_append_count_aux x s1_m pre_r;
    ()
#pop-options

// ========== If s[j] exists, count(s[j], s) >= 1 ==========

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec index_has_positive_count (s: Seq.seq int) (j: nat)
  : Lemma (requires j < Seq.length s)
          (ensures Seq.Properties.count (Seq.index s j) s >= 1)
          (decreases Seq.length s)
  = if j = 0 then ()
    else index_has_positive_count (Seq.tail s) (j - 1)
#pop-options

// ========== If count(x, s) >= 1, x appears somewhere in s ==========

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec count_pos_has_index (s: Seq.seq int) (x: int)
  : Lemma (requires Seq.Properties.count x s > 0)
          (ensures exists (i: nat). i < Seq.length s /\ Seq.index s i == x)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if Seq.head s = x then ()
    else count_pos_has_index (Seq.tail s) x
#pop-options

// ========== Main lemma: lower bound preservation ==========

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1 --split_queries always"
let perm_unchanged_lower_bound
  (s_pre s1: Seq.seq int) (lo hi: nat) (v: int) (j: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              lo <= j /\ j < hi /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx) /\
              (forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m))
    (ensures v <= Seq.index s1 j)
  = let x = Seq.index s1 j in
    let s1_slice = Seq.slice s1 lo hi in
    let pre_slice = Seq.slice s_pre lo hi in
    assert (Seq.index s1_slice (j - lo) == x);
    index_has_positive_count s1_slice (j - lo);
    count_range_eq s_pre s1 lo hi x;
    count_pos_has_index pre_slice x;
    ()
#pop-options

// ========== Symmetric: upper bound preservation ==========

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1 --split_queries always"
let perm_unchanged_upper_bound
  (s_pre s1: Seq.seq int) (lo hi: nat) (v: int) (j: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              lo <= j /\ j < hi /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx) /\
              (forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v))
    (ensures Seq.index s1 j <= v)
  = let x = Seq.index s1 j in
    let s1_slice = Seq.slice s1 lo hi in
    let pre_slice = Seq.slice s_pre lo hi in
    assert (Seq.index s1_slice (j - lo) == x);
    index_has_positive_count s1_slice (j - lo);
    count_range_eq s_pre s1 lo hi x;
    count_pos_has_index pre_slice x;
    ()
#pop-options

// ========== Universally-quantified versions ==========

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let perm_unchanged_lower_bound_forall
  (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m) ==>
              v <= Seq.index s1 j)
  = let n = Seq.length s1 in
    let aux (j: nat{j < n}) : Lemma
      (requires lo <= j /\ j < hi)
      (ensures forall (v: int).
        (forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m) ==>
        v <= Seq.index s1 j)
    = let aux2 (v: int) : Lemma
        (requires forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m)
        (ensures v <= Seq.index s1 j)
      = perm_unchanged_lower_bound s_pre s1 lo hi v j
      in
      Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let perm_unchanged_upper_bound_forall
  (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v) ==>
              Seq.index s1 j <= v)
  = let n = Seq.length s1 in
    let aux (j: nat{j < n}) : Lemma
      (requires lo <= j /\ j < hi)
      (ensures forall (v: int).
        (forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v) ==>
        Seq.index s1 j <= v)
    = let aux2 (v: int) : Lemma
        (requires forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v)
        (ensures Seq.index s1 j <= v)
      = perm_unchanged_upper_bound s_pre s1 lo hi v j
      in
      Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// ========== Bridge: Seq.Properties.permutation <==> count_occ-based is_permutation ==========

module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec

let rec count_eq (s: Seq.seq int) (x: int)
  : Lemma (ensures Seq.Properties.count x s = PSSSpec.count_occ s x)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s == Seq.index s 0);
      count_eq (Seq.tail s) x
    )

let seq_perm_implies_is_perm (s1 s2: Seq.seq int)
  : Lemma (requires Seq.Properties.permutation int s1 s2 /\
                    Seq.length s1 == Seq.length s2)
          (ensures PSSSpec.is_permutation s1 s2)
  = let aux (x: int) : Lemma (PSSSpec.count_occ s1 x = PSSSpec.count_occ s2 x) =
      count_eq s1 x;
      count_eq s2 x
    in
    Classical.forall_intro aux
