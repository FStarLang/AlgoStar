(**
 * ISMM: Counting non-zero entries in SZ.t sequences.
 *
 * Adapted from CLRS.Common.CountOnes. Used to prove stack overflow
 * bounds: dfs_top <= count_nonzero(tag, n), so when we discover an
 * UNMARKED (tag=0) node, count_nonzero < n, hence dfs_top < n.
 *)
module ISMM.Count

open FStar.Mul
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Count entries with SZ.v != 0 in s[0..n)
let rec count_nonzero (s: Seq.seq SZ.t) (n: nat) : Tot nat (decreases n) =
  if n = 0 || n > Seq.length s then 0
  else (if SZ.v (Seq.index s (n - 1)) <> 0 then 1 else 0) + count_nonzero s (n - 1)

/// Upper bound: count_nonzero <= n
let rec count_nonzero_bound (s: Seq.seq SZ.t) (n: nat)
  : Lemma (requires n <= Seq.length s)
          (ensures count_nonzero s n <= n) (decreases n)
  = if n > 0 then count_nonzero_bound s (n - 1)

/// Update above n doesn't affect count
let rec count_nonzero_upd_above (s: Seq.seq SZ.t) (n u: nat) (v: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u >= n /\ u < Seq.length s)
          (ensures count_nonzero (Seq.upd s u v) n == count_nonzero s n)
          (decreases n)
  = if n > 0 then count_nonzero_upd_above s (n - 1) u v

/// Marking a zero entry as non-zero increases count by 1
let rec count_nonzero_mark (s: Seq.seq SZ.t) (n u: nat) (v: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) == 0 /\ SZ.v v <> 0)
          (ensures count_nonzero (Seq.upd s u v) n == count_nonzero s n + 1)
          (decreases n)
  = if n - 1 > u then
      count_nonzero_mark s (n - 1) u v
    else if n - 1 = u then
      count_nonzero_upd_above s (n - 1) u v
    else ()

/// Updating a non-zero entry to another non-zero preserves count
let rec count_nonzero_upd_nonzero (s: Seq.seq SZ.t) (n u: nat) (v: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) <> 0 /\ SZ.v v <> 0)
          (ensures count_nonzero (Seq.upd s u v) n == count_nonzero s n)
          (decreases n)
  = if n - 1 > u then
      count_nonzero_upd_nonzero s (n - 1) u v
    else if n - 1 = u then
      count_nonzero_upd_above s (n - 1) u v
    else ()

/// Updating a non-zero entry to zero decreases count by 1
let rec count_nonzero_unmark (s: Seq.seq SZ.t) (n u: nat) (v: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) <> 0 /\ SZ.v v == 0)
          (ensures count_nonzero (Seq.upd s u v) n == count_nonzero s n - 1)
          (decreases n)
  = if n - 1 > u then
      count_nonzero_unmark s (n - 1) u v
    else if n - 1 = u then
      count_nonzero_upd_above s (n - 1) u v
    else ()

/// If some entry is zero, count_nonzero < n
let rec count_nonzero_gap (s: Seq.seq SZ.t) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) == 0)
          (ensures count_nonzero s n < n) (decreases n)
  = if n > 0 then begin
      if n - 1 = u then
        count_nonzero_bound s (n - 1)
      else
        count_nonzero_gap s (n - 1) u
    end

/// If all entries are zero, count is 0
let rec count_nonzero_all_zero (s: Seq.seq SZ.t) (n: nat)
  : Lemma (requires n <= Seq.length s /\
           (forall (j:nat). j < n ==> SZ.v (Seq.index s j) == 0))
          (ensures count_nonzero s n == 0) (decreases n)
  = if n > 0 then count_nonzero_all_zero s (n - 1)


(*** Parametric count: entries with a specific value ***)

/// Count entries with SZ.v == v in s[0..n)
let rec count_eq (s: Seq.seq SZ.t) (v: nat) (n: nat) : Tot nat (decreases n) =
  if n = 0 || n > Seq.length s then 0
  else (if SZ.v (Seq.index s (n - 1)) = v then 1 else 0) + count_eq s v (n - 1)

/// Upper bound: count_eq <= n
let rec count_eq_bound (s: Seq.seq SZ.t) (v: nat) (n: nat)
  : Lemma (requires n <= Seq.length s)
          (ensures count_eq s v n <= n) (decreases n)
  = if n > 0 then count_eq_bound s v (n - 1)

/// Update above n doesn't affect count
let rec count_eq_upd_above (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u >= n /\ u < Seq.length s)
          (ensures count_eq (Seq.upd s u w) v n == count_eq s v n)
          (decreases n)
  = if n > 0 then count_eq_upd_above s v (n - 1) u w

/// Changing a non-matching entry to matching increases count by 1
let rec count_eq_mark (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) <> v /\ SZ.v w == v)
          (ensures count_eq (Seq.upd s u w) v n == count_eq s v n + 1)
          (decreases n)
  = if n - 1 > u then
      count_eq_mark s v (n - 1) u w
    else if n - 1 = u then
      count_eq_upd_above s v (n - 1) u w
    else ()

/// Changing a matching entry to non-matching decreases count by 1
let rec count_eq_unmark (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) == v /\ SZ.v w <> v)
          (ensures count_eq (Seq.upd s u w) v n == count_eq s v n - 1)
          (decreases n)
  = if n - 1 > u then
      count_eq_unmark s v (n - 1) u w
    else if n - 1 = u then
      count_eq_upd_above s v (n - 1) u w
    else ()

/// Changing entry to same value or non-matching to non-matching preserves count
let rec count_eq_preserve (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           (SZ.v (Seq.index s u) == v ==> SZ.v w == v) /\
           (SZ.v (Seq.index s u) <> v ==> SZ.v w <> v))
          (ensures count_eq (Seq.upd s u w) v n == count_eq s v n)
          (decreases n)
  = if n - 1 > u then
      count_eq_preserve s v (n - 1) u w
    else if n - 1 = u then
      count_eq_upd_above s v (n - 1) u w
    else ()

/// If some entry != v, count_eq < n
let rec count_eq_gap (s: Seq.seq SZ.t) (v: nat) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) <> v)
          (ensures count_eq s v n < n) (decreases n)
  = if n > 0 then begin
      if n - 1 = u then
        count_eq_bound s v (n - 1)
      else
        count_eq_gap s v (n - 1) u
    end

/// If some entry == v, count_eq >= 1
let rec count_eq_pos (s: Seq.seq SZ.t) (v: nat) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) == v)
          (ensures count_eq s v n >= 1) (decreases n)
  = if n > 0 then begin
      if n - 1 = u then ()
      else count_eq_pos s v (n - 1) u
    end

/// If count_eq == 0, then no entry matches v
let rec count_eq_zero_implies_none (s: Seq.seq SZ.t) (v: nat) (n: nat)
  : Lemma (requires n <= Seq.length s /\ count_eq s v n == 0)
          (ensures forall (i:nat). i < n ==> SZ.v (Seq.index s i) <> v)
          (decreases n)
  = if n > 0 then count_eq_zero_implies_none s v (n - 1)

/// Unmark: changing entry at index u from matching v to non-matching decreases count by 1
/// (Same as count_eq_unmark but asserting the result is non-negative)
let count_eq_unmark_sub (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\
           SZ.v (Seq.index s u) == v /\ SZ.v w <> v /\
           count_eq s v n >= 1)
          (ensures count_eq (Seq.upd s u w) v n == count_eq s v n - 1 /\
                   count_eq (Seq.upd s u w) v n + 1 == count_eq s v n)
  = count_eq_unmark s v (n) u w;
    count_eq_pos s v n u

/// If no entry matches v, count_eq == 0 (converse of count_eq_zero_implies_none)
let rec count_eq_zero_from_all_ne (s: Seq.seq SZ.t) (v: nat) (n: nat)
  : Lemma (requires n <= Seq.length s /\ (forall (i:nat). i < n ==> SZ.v (Seq.index s i) <> v))
          (ensures count_eq s v n == 0)
          (decreases n)
  = if n > 0 then count_eq_zero_from_all_ne s v (n - 1)

/// After update with new value != v, count_eq for v is non-increasing
let count_eq_nonincreasing_on_update (s: Seq.seq SZ.t) (v: nat) (n u: nat) (w: SZ.t)
  : Lemma (requires n <= Seq.length s /\ u < n /\ SZ.v w <> v)
          (ensures count_eq (Seq.upd s u w) v n <= count_eq s v n)
  = if SZ.v (Seq.index s u) = v then count_eq_unmark s v n u w
    else count_eq_preserve s v n u w
