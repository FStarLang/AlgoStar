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
