module CLRS.Common.CountOnes

/// General-purpose lemmas about counting entries equal to 1 in integer sequences.
/// Used by Dijkstra's algorithm to track visited vertex count.

module Seq = FStar.Seq

/// Count of entries equal to 1 in s[0..n)
let rec count_ones (s: Seq.seq int) (n: nat) : Tot nat (decreases n) =
  if n = 0 || n > Seq.length s then 0
  else (if Seq.index s (n-1) = 1 then 1 else 0) + count_ones s (n-1)

let rec count_ones_all_zero (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ (forall (j:nat). j < n ==> Seq.index s j = 0))
          (ensures count_ones s n == 0) (decreases n)
  = if n > 0 then count_ones_all_zero s (n-1)

let rec count_ones_all_one (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ (forall (j:nat). j < n ==> Seq.index s j = 1))
          (ensures count_ones s n == n) (decreases n)
  = if n > 0 then count_ones_all_one s (n-1)

let rec count_ones_bound (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures count_ones s n <= n) (decreases n)
  = if n > 0 then count_ones_bound s (n-1)

let rec count_ones_upd_above (s: Seq.seq int) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u >= n /\ u < Seq.length s)
          (ensures count_ones (Seq.upd s u 1) n == count_ones s n) (decreases n)
  = if n > 0 then count_ones_upd_above s (n-1) u

let rec count_ones_mark (s: Seq.seq int) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u < n /\ Seq.index s u = 0 /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures count_ones (Seq.upd s u 1) n == count_ones s n + 1) (decreases n)
  = if n - 1 > u then
      count_ones_mark s (n-1) u
    else if n - 1 = u then
      count_ones_upd_above s (n-1) u
    else () // n-1 < u, impossible since u < n

let rec count_ones_full (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ count_ones s n >= n /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures forall (j:nat). j < n ==> Seq.index s j = 1) (decreases n)
  = if n > 0 then begin
      count_ones_bound s (n-1);
      count_ones_full s (n-1)
    end

/// count_ones < n implies not all visited
let count_ones_not_all_visited (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ count_ones s n < n /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures ~(forall (j:nat). j < n ==> Seq.index s j = 1))
  = Classical.move_requires (count_ones_all_one s) n
