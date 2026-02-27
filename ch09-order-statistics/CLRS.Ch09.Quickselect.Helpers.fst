(*
   Helper lemmas for strengthening quickselect's postcondition.

   Key result: if s1 is a permutation of s_pre, and they agree outside [lo, hi),
   then a bound on all values in s_pre[lo..hi) also holds for s1[lo..hi).

   This enables propagating ordering invariants through partition calls.
*)

module CLRS.Ch09.Quickselect.Helpers

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

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
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
    // Outside slices are propositionally equal
    slice_eq_from_pointwise s_pre s1 0 lo;
    Seq.lemma_eq_elim (Seq.slice s_pre 0 lo) (Seq.slice s1 0 lo);
    slice_eq_from_pointwise s_pre s1 hi n;
    Seq.lemma_eq_elim (Seq.slice s_pre hi n) (Seq.slice s1 hi n);
    let pre_l = Seq.slice s_pre 0 lo in
    let pre_m = Seq.slice s_pre lo hi in
    let pre_r = Seq.slice s_pre hi n in
    let s1_m = Seq.slice s1 lo hi in
    // Establish three-way decomposition via propositional equality
    Seq.lemma_eq_elim s_pre (Seq.append pre_l (Seq.append pre_m pre_r));
    Seq.lemma_eq_elim s1 (Seq.append pre_l (Seq.append s1_m pre_r));
    // Split counts using lemma_append_count_aux for specific x
    Seq.Properties.lemma_append_count_aux x pre_l (Seq.append pre_m pre_r);
    Seq.Properties.lemma_append_count_aux x pre_m pre_r;
    Seq.Properties.lemma_append_count_aux x pre_l (Seq.append s1_m pre_r);
    Seq.Properties.lemma_append_count_aux x s1_m pre_r;
    // count x s_pre = count x pre_l + count x pre_m + count x pre_r
    // count x s1   = count x pre_l + count x s1_m  + count x pre_r
    // permutation: count x s_pre = count x s1
    // Therefore: count x pre_m = count x s1_m
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
// If all values in s_pre[lo..hi) are >= v, and s1 is a permutation of s_pre
// with elements outside [lo,hi) unchanged, then all values in s1[lo..hi) are >= v.

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
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
    // s1[j] = s1_slice[j - lo], so count(x, s1_slice) >= 1
    assert (Seq.index s1_slice (j - lo) == x);
    index_has_positive_count s1_slice (j - lo);
    // count(x, s1_slice) = count(x, pre_slice)
    count_range_eq s_pre s1 lo hi x;
    // count(x, pre_slice) >= 1, so x appears somewhere in pre_slice
    count_pos_has_index pre_slice x;
    // There exists i' < hi-lo with pre_slice[i'] = x, i.e., s_pre[lo+i'] = x
    // By premise, v <= s_pre[lo+i'] = x = s1[j]
    ()
#pop-options

// ========== Symmetric: upper bound preservation ==========

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
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
// These produce forall-quantified conclusions for use with SMT

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
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

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
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

module Spec = CLRS.Ch09.PartialSelectionSort.Spec

// Seq.Properties.count and Spec.count_occ are equivalent
let rec count_eq (s: Seq.seq int) (x: int)
  : Lemma (ensures Seq.Properties.count x s = Spec.count_occ s x)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (Seq.head s == Seq.index s 0);
      count_eq (Seq.tail s) x
    )

// Bridge: Seq.Properties.permutation ==> Spec.is_permutation (given equal lengths)
let seq_perm_implies_is_perm (s1 s2: Seq.seq int)
  : Lemma (requires Seq.Properties.permutation int s1 s2 /\
                    Seq.length s1 == Seq.length s2)
          (ensures Spec.is_permutation s1 s2)
  = let aux (x: int) : Lemma (Spec.count_occ s1 x = Spec.count_occ s2 x) =
      count_eq s1 x;
      count_eq s2 x
    in
    Classical.forall_intro aux
