(*
   Pure F* lemmas for the CLRS 4-phase stable counting sort.
   Separated from the main Lemmas module to avoid SMT context pollution.
*)

module CLRS.Ch08.CountingSort.StableLemmas

open FStar.Seq
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical
module L = CLRS.Ch08.CountingSort.Lemmas

// ========== count_le: count elements in [0, v] ==========

let rec count_le (s: Seq.seq nat) (v: int)
  : Tot nat (decreases (Seq.length s))
  = if Seq.length s = 0 then 0
    else if Seq.head s <= v then 1 + count_le (Seq.tail s) v
    else count_le (Seq.tail s) v

let rec count_le_bounded (s: Seq.seq nat) (v: int)
  : Lemma (ensures count_le s v <= Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_le_bounded (Seq.tail s) v

let rec count_le_negative (s: Seq.seq nat) (v: int)
  : Lemma (requires v < 0)
          (ensures count_le s v == 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_le_negative (Seq.tail s) v

// Key: count_le s v = count_le s (v-1) + count v s  (for v >= 0)
let rec count_le_step (s: Seq.seq nat) (v: int)
  : Lemma (requires v >= 0)
          (ensures count_le s v == count_le s (v - 1) + SeqP.count v s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_le_step (Seq.tail s) v

// Specialized: count_le s 0 == count of 0s in s
let count_le_zero_eq (s: Seq.seq nat)
  : Lemma (ensures count_le s 0 == SeqP.count 0 s)
  = count_le_step s 0;
    count_le_negative s (-1)

let rec count_le_monotone (s: Seq.seq nat) (v1 v2: int)
  : Lemma (requires v1 <= v2)
          (ensures count_le s v1 <= count_le s v2)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_le_monotone (Seq.tail s) v1 v2

let rec count_le_full (s: Seq.seq nat) (k: nat)
  : Lemma (requires L.in_range s k)
          (ensures count_le s k == Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_le_full (Seq.tail s) k

// ========== Prefix sum invariant for phase 3 ==========

let prefix_sum_inv (sc: Seq.seq int) (sa: Seq.seq nat) (k: nat) (progress: nat) : prop =
  Seq.length sc == k + 1 /\
  progress >= 1 /\ progress <= k + 1 /\
  L.in_range sa k /\
  (forall (v: nat). v < progress /\ v <= k ==> Seq.index sc v == count_le sa v) /\
  (forall (v: nat). v >= progress /\ v <= k ==> Seq.index sc v == SeqP.count v sa)

let prefix_sum_inv_init (sc: Seq.seq int) (sa: Seq.seq nat) (k: nat)
  : Lemma (requires L.counts_match sc sa k /\ L.in_range sa k /\ k >= 0)
          (ensures prefix_sum_inv sc sa k 1)
  = count_le_step sa 0;
    count_le_negative sa (-1)

#push-options "--z3rlimit 30"
let prefix_sum_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (k: nat) (i: nat)
  : Lemma (requires prefix_sum_inv sc sa k i /\
                    i >= 1 /\ i <= k /\
                    Seq.length sc' == k + 1 /\
                    (forall (v: nat). v <= k /\ v <> i ==> Seq.index sc' v == Seq.index sc v) /\
                    Seq.index sc' i == Seq.index sc i + Seq.index sc (i - 1))
          (ensures prefix_sum_inv sc' sa k (i + 1))
  = count_le_step sa i
#pop-options

let prefix_sum_complete (sc: Seq.seq int) (sa: Seq.seq nat) (k: nat)
  : Lemma (requires prefix_sum_inv sc sa k (k + 1))
          (ensures (forall (v: nat). v <= k ==> Seq.index sc v == count_le sa v) /\
                   Seq.index sc k == Seq.length sa)
  = count_le_full sa k

// ========== Phase 4 position bounds ==========

// After phase 3, c[v] = count_le sa v for all v in [0,k].
// In the backward pass, we track:
//   c[v] = c_init[v] - count(v, processed_suffix)
// where c_init[v] = count_le sa v.

// Position bound: when processing sa[j] with key = sa[j],
// pos = c[key] satisfies 1 <= pos <= n.
// This requires: c_init[key] > count(key, already_processed_suffix)
// Which holds because sa[j] = key is NOT in the already-processed suffix.

// Helper: if sa[i] = v and i is in slice(sa, 0, remaining), count >= 1
let count_in_prefix (sa: Seq.seq nat) (remaining: nat) (v: nat)
  : Lemma (requires remaining > 0 /\ remaining <= Seq.length sa /\
                    Seq.index sa (remaining - 1) == v)
          (ensures SeqP.count v (Seq.slice sa 0 remaining) >= 1)
  = let prefix = Seq.slice sa 0 remaining in
    SeqP.lemma_count_slice prefix (remaining - 1)
    // count(v, prefix) = count(v, prefix[0..r-1]) + count(v, prefix[r-1..r])
    // prefix[r-1..r] = [v], so count(v, [v]) >= 1

// Position bounds from tracking invariant
#push-options "--z3rlimit 50"
let phase4_pos_bounds
  (sc_init: Seq.seq int) (sa: Seq.seq nat) (k: nat) (remaining: nat)
  (sc_key: int) (key: nat)
  : Lemma (requires
      Seq.length sa > 0 /\
      L.in_range sa k /\
      remaining > 0 /\ remaining <= Seq.length sa /\
      key <= k /\
      key == Seq.index sa (remaining - 1) /\
      // sc_key = c_init[key] - count(key, processed_suffix)
      // where processed_suffix = slice(sa, remaining, n)
      sc_key == count_le sa key - SeqP.count key (Seq.slice sa remaining (Seq.length sa)))
    (ensures sc_key >= 1 /\ sc_key <= Seq.length sa)
  = let n = Seq.length sa in
    let suffix = Seq.slice sa remaining n in
    let prefix = Seq.slice sa 0 remaining in
    // count_le sa key <= n
    count_le_bounded sa key;
    // count(key, sa) = count(key, prefix) + count(key, suffix)
    assert (Seq.equal sa (Seq.append prefix suffix));
    SeqP.lemma_append_count_aux key prefix suffix;
    // count(key, prefix) >= 1 since sa[remaining-1] = key
    count_in_prefix sa remaining key;
    // sc_key = count_le sa key - count(key, suffix)
    //        = count_le sa key - (count(key, sa) - count(key, prefix))
    //        = count_le sa key - count(key, sa) + count(key, prefix)
    //        = count_le sa (key-1) + count(key, prefix)   [by count_le_step]
    //        >= 0 + 1 = 1
    count_le_step sa key;
    // Also sc_key <= count_le sa key <= n
    ()
#pop-options

// ========== Phase 4 disjoint ranges ==========

// The write position sc[key]-1 is NOT in any other key's range.
// For v < key: sc_init[v] = count_le sa v <= count_le sa (key-1) <= sc[key]-1
//   so sc[key]-1 >= sc_init[v], hence NOT in [sc[v], sc_init[v])
// For v > key: sc[v] >= count_le sa (v-1) >= count_le sa key = sc_init[key] >= sc[key] > sc[key]-1
//   so sc[key]-1 < sc[v], hence NOT in [sc[v], sc_init[v])

#push-options "--z3rlimit 50"
let write_pos_not_in_smaller_range
  (sa: Seq.seq nat) (k: nat) (remaining: nat) (key v: nat) (pos: int)
  : Lemma (requires
      L.in_range sa k /\ remaining > 0 /\ remaining <= Seq.length sa /\
      key <= k /\ v <= k /\ v < key /\
      key == Seq.index sa (remaining - 1) /\
      pos == count_le sa key - SeqP.count key (Seq.slice sa remaining (Seq.length sa)) /\
      pos >= 1)
    (ensures pos - 1 >= count_le sa v)
  = count_le_step sa key;
    let n = Seq.length sa in
    let suffix = Seq.slice sa remaining n in
    let prefix = Seq.slice sa 0 remaining in
    assert (Seq.equal sa (Seq.append prefix suffix));
    SeqP.lemma_append_count_aux key prefix suffix;
    count_in_prefix sa remaining key;
    // pos = count_le sa (key-1) + count(key, prefix) >= count_le sa (key-1) + 1
    // count_le sa v <= count_le sa (key-1) since v <= key-1
    count_le_monotone sa v (key - 1)
    // pos - 1 >= count_le sa (key-1) >= count_le sa v
#pop-options

#push-options "--z3rlimit 50"
let write_pos_not_in_larger_range
  (sc_init: Seq.seq int) (sa: Seq.seq nat) (k: nat) (remaining: nat) (key v: nat)
  (pos sc_v: int)
  : Lemma (requires
      L.in_range sa k /\ remaining > 0 /\ remaining <= Seq.length sa /\
      Seq.length sc_init == k + 1 /\
      key <= k /\ v <= k /\ v > key /\
      key == Seq.index sa (remaining - 1) /\
      pos == count_le sa key - SeqP.count key (Seq.slice sa remaining (Seq.length sa)) /\
      pos >= 1 /\
      sc_v == count_le sa v - SeqP.count v (Seq.slice sa remaining (Seq.length sa)) /\
      sc_v >= 0)
    (ensures pos - 1 < sc_v)
  = let n = Seq.length sa in
    let suffix = Seq.slice sa remaining n in
    let prefix = Seq.slice sa 0 remaining in
    assert (Seq.equal sa (Seq.append prefix suffix));
    // sc_v = count_le sa v - count(v, suffix) = count_le sa (v-1) + count(v, prefix)
    count_le_step sa v;
    SeqP.lemma_append_count_aux v prefix suffix;
    // sc_v >= count_le sa (v-1) >= count_le sa key (monotone, v-1 >= key since v > key)
    count_le_monotone sa key (v - 1);
    // count_le sa key >= pos (since pos = count_le sa key - count(key, suffix) <= count_le sa key)
    // So pos - 1 < pos <= count_le sa key <= count_le sa (v-1) <= sc_v
    ()
#pop-options

// ========== Final sorted and permutation ==========

// After phase 4 (remaining = 0):
// For each key v in [0,k]:
//   c_final[v] = count_le sa v - count(v, sa) = count_le sa (v-1)
//   c_init[v] = count_le sa v
//   Positions [c_final[v], c_init[v]) all contain value v.
// These ranges partition [0, n) since:
//   c_final[0] = count_le sa (-1) = 0
//   c_init[v] = count_le sa v = c_final[v+1] (contiguous)
//   c_init[k] = n
// => sorted and permutation

// Find which key range a position belongs to
let rec find_key (sa: Seq.seq nat) (k: nat) (p: nat) (lo: nat)
  : Pure nat
    (requires L.in_range sa k /\ p < count_le sa k /\ lo <= k + 1 /\
              (lo = 0 \/ p >= count_le sa (lo - 1)))
    (ensures fun v -> v <= k /\
                 (v = 0 \/ count_le sa (v - 1) <= p) /\
                 p < count_le sa v)
    (decreases k + 1 - lo)
  = if lo > k then (
      count_le_full sa k;
      lo // unreachable but needed for termination
    )
    else if p < count_le sa lo then lo
    else find_key sa k p (lo + 1)

// Sorted: for all i <= j < n, B[i] <= B[j]
// Given: for each v, positions [count_le sa (v-1), count_le sa v) contain v
// And these ranges partition [0, n)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let final_sorted_aux (sa sb: Seq.seq nat) (k: nat) (i j: nat)
  : Lemma (requires
      L.in_range sa k /\ Seq.length sb == Seq.length sa /\
      i <= j /\ j < Seq.length sa /\
      count_le sa k == Seq.length sa /\
      // All ranges are filled correctly
      (forall (v: nat). v <= k ==>
        (forall (p: nat). (v = 0 \/ count_le sa (v - 1) <= p) /\ p < count_le sa v ==>
          p < Seq.length sb /\ Seq.index sb p == v)))
    (ensures Seq.index sb i <= Seq.index sb j)
  = let vi = find_key sa k i 0 in
    let vj = find_key sa k j 0 in
    // sb[i] = vi, sb[j] = vj
    // If vi > vj: count_le sa (vi - 1) >= count_le sa vj (monotone, vi-1 >= vj since vi > vj)
    // So i >= count_le sa (vi - 1) >= count_le sa vj > j. Contradiction with i <= j.
    if vi > vj then (
      count_le_monotone sa vj (vi - 1)
    ) else ()
#pop-options

// Permutation: count(v, sb) = count(v, sa) for all v
// For v in [0,k]: range [count_le sa (v-1), count_le sa v) has count_le sa v - count_le sa (v-1) = count(v, sa) positions
// All with value v. For v not in [0,k]: no positions have that value, and no input elements have that value.

// Helper: count of value v in a block where all elements equal v
let rec count_of_constant_block (sb: Seq.seq nat) (lo hi: nat) (v: nat) (w: nat)
  : Lemma (requires hi <= Seq.length sb /\ lo <= hi /\
                    (forall (p: nat). lo <= p /\ p < hi ==> Seq.index sb p == v))
          (ensures SeqP.count w (Seq.slice sb lo hi) == (if w = v then hi - lo else 0))
          (decreases hi - lo)
  = if lo = hi then (
      assert (Seq.equal (Seq.slice sb lo hi) Seq.empty)
    ) else (
      count_of_constant_block sb (lo + 1) hi v w;
      let s = Seq.slice sb lo hi in
      let s' = Seq.slice sb (lo + 1) hi in
      assert (Seq.head s == Seq.index sb lo);
      assert (Seq.index sb lo == v);
      assert (Seq.equal (Seq.tail s) s')
    )

// Sorted output from range structure
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let final_sorted (sa sb: Seq.seq nat) (k: nat)
  : Lemma (requires
      L.in_range sa k /\ Seq.length sb == Seq.length sa /\
      Seq.length sa > 0 /\
      count_le sa k == Seq.length sa /\
      (forall (v: nat). v <= k ==>
        (forall (p: nat). (v = 0 \/ count_le sa (v - 1) <= p) /\ p < count_le sa v ==>
          p < Seq.length sb /\ Seq.index sb p == v)))
    (ensures L.sorted sb)
  = let n = Seq.length sa in
    count_le_full sa k;
    count_le_negative sa (-1);
    let rec prove_sorted (v: nat)
      : Lemma (requires v <= k /\
                        count_le sa k == n /\ L.in_range sa k /\ Seq.length sb == n /\
                        (forall (w: nat). w <= k ==>
                          (forall (p: nat). (w = 0 \/ count_le sa (w - 1) <= p) /\ p < count_le sa w ==>
                            p < n /\ Seq.index sb p == w)))
              (ensures count_le sa v <= n /\
                       L.sorted_prefix sb (count_le sa v) /\
                       (count_le sa v > 0 ==> Seq.index sb (count_le sa v - 1) <= v))
              (decreases v)
      = count_le_bounded sa v;
        count_le_step sa v;
        if v = 0 then (
          count_le_negative sa (-1);
          L.write_block_sorted sb 0 (count_le sa 0) 0
        ) else (
          prove_sorted (v - 1);
          count_le_bounded sa (v - 1);
          count_le_monotone sa (v - 1) v;
          let pos = count_le sa (v - 1) in
          let cnt = count_le sa v - pos in
          L.write_block_sorted sb pos cnt v
        )
    in
    prove_sorted k
#pop-options

// Permutation helper: count elements in block-structured output
#push-options "--z3rlimit 200"
let rec perm_count_blocks (sa sb: Seq.seq nat) (k: nat) (v: nat) (w: nat)
  : Lemma (requires v <= k /\
                    count_le sa k == Seq.length sa /\ L.in_range sa k /\
                    Seq.length sb == Seq.length sa /\
                    count_le sa (-1) == 0 /\
                    (forall (u: nat). u <= k ==>
                      (forall (p: nat). (u = 0 \/ count_le sa (u - 1) <= p) /\ p < count_le sa u ==>
                        p < Seq.length sb /\ Seq.index sb p == u)))
          (ensures count_le sa v <= Seq.length sa /\
                   SeqP.count w (Seq.slice sb 0 (count_le sa v)) ==
                     (if w <= v then SeqP.count w sa else 0))
          (decreases v)
  = count_le_bounded sa v;
    if v = 0 then (
      count_le_zero_eq sa;
      assert (forall (i:nat). i < count_le sa 0 ==> Seq.index sb i == 0);
      L.block_count sb 0 (count_le sa 0) 0 w
    ) else (
      count_le_step sa v;
      perm_count_blocks sa sb k (v - 1) w;
      count_le_bounded sa (v - 1);
      count_le_monotone sa (v - 1) v;
      let lo = count_le sa (v - 1) in
      let cnt = count_le sa v - lo in
      assert (forall (i:nat). lo <= i /\ i < lo + cnt ==> Seq.index sb i == v);
      L.block_count sb lo cnt v w
    )
#pop-options

// Permutation from range structure
#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let final_perm (sa sb: Seq.seq nat) (k: nat)
  : Lemma (requires
      L.in_range sa k /\ Seq.length sb == Seq.length sa /\
      Seq.length sa > 0 /\
      count_le sa k == Seq.length sa /\
      count_le sa (-1) == 0 /\
      (forall (v: nat). v <= k ==>
        (forall (p: nat). (v = 0 \/ count_le sa (v - 1) <= p) /\ p < count_le sa v ==>
          p < Seq.length sb /\ Seq.index sb p == v)))
    (ensures L.permutation sb sa)
  = let n = Seq.length sa in
    count_le_full sa k;
    count_le_negative sa (-1);
    let aux (w: nat) : Lemma (SeqP.count w sb == SeqP.count w sa) =
      perm_count_blocks sa sb k k w;
      assert (Seq.equal sb (Seq.slice sb 0 n));
      if w <= k then ()
      else begin
        assert (forall (i:nat). i < Seq.length sa ==> Seq.index sa i <= k);
        SeqP.lemma_mem_count sa (fun x -> x <= k)
      end
    in
    Classical.forall_intro aux;
    L.equal_counts_perm sb sa
#pop-options

// ========== Phase 4 loop invariant (split into C tracking and B filling) ==========

// C tracking: count array values match expected
[@@"opaque_to_smt"]
let phase4_c_inv (sc: Seq.seq int) (sa: Seq.seq nat) (k n remaining: nat) : prop =
  Seq.length sc == k + 1 /\ Seq.length sa == n /\ n > 0 /\
  remaining <= n /\ L.in_range sa k /\
  (forall (v: nat). v <= k ==>
    Seq.index sc v == count_le sa v - SeqP.count v (Seq.slice sa remaining n))

// B filling: output positions filled correctly
[@@"opaque_to_smt"]
let phase4_b_inv (sc: Seq.seq int) (sa sb_curr: Seq.seq nat) (k n: nat) : prop =
  Seq.length sc == k + 1 /\ Seq.length sa == n /\ Seq.length sb_curr == n /\
  L.in_range sa k /\
  (forall (v: nat). v <= k ==>
    (forall (p: nat). Seq.index sc v <= p /\ p < count_le sa v ==>
      p < n /\ Seq.index sb_curr p == v))

// Helper: extending suffix count
let count_extend_suffix (sa: Seq.seq nat) (remaining: nat) (v: nat)
  : Lemma (requires remaining > 0 /\ remaining <= Seq.length sa)
          (ensures SeqP.count v (Seq.slice sa (remaining - 1) (Seq.length sa)) ==
                   (if v = Seq.index sa (remaining - 1) then 1 else 0) +
                   SeqP.count v (Seq.slice sa remaining (Seq.length sa)))
  = let n = Seq.length sa in
    let full = Seq.slice sa (remaining - 1) n in
    let left = Seq.slice sa (remaining - 1) remaining in
    let right = Seq.slice sa remaining n in
    assert (Seq.equal full (Seq.append left right));
    SeqP.lemma_append_count_aux v left right;
    assert (Seq.length left == 1);
    assert (Seq.index left 0 == Seq.index sa (remaining - 1))

// Initialize C tracking
#push-options "--z3rlimit 50"
let phase4_c_inv_init (sc: Seq.seq int) (sa: Seq.seq nat) (k: nat)
  : Lemma (requires
      Seq.length sc == k + 1 /\ L.in_range sa k /\ Seq.length sa > 0 /\
      (forall (v: nat). v <= k ==> Seq.index sc v == count_le sa v))
    (ensures phase4_c_inv sc sa k (Seq.length sa) (Seq.length sa))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k (Seq.length sa) (Seq.length sa));
    assert (Seq.equal (Seq.slice sa (Seq.length sa) (Seq.length sa)) Seq.empty)
#pop-options

// Initialize B filling (empty at start)
let phase4_b_inv_init (sc: Seq.seq int) (sa sb_curr: Seq.seq nat) (k: nat)
  : Lemma (requires
      Seq.length sc == k + 1 /\ L.in_range sa k /\ Seq.length sa > 0 /\
      Seq.length sb_curr == Seq.length sa /\
      (forall (v: nat). v <= k ==> Seq.index sc v == count_le sa v))
    (ensures phase4_b_inv sc sa sb_curr k (Seq.length sa))
  = reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb_curr k (Seq.length sa));
    count_le_full sa k;
    // sc[v] = count_le sa v, so range [sc[v], count_le sa v) is empty for all v
    ()

// Position bounds from C tracking
#push-options "--z3rlimit 50"
let phase4_c_pos_bounds (sc: Seq.seq int) (sa: Seq.seq nat) (k n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa k n remaining /\
      Seq.length sc == k + 1 /\ Seq.length sa == n /\ n > 0 /\ remaining <= n /\
      remaining > 0 /\ key <= k /\
      key == Seq.index sa (remaining - 1))
    (ensures Seq.index sc key >= 1 /\ Seq.index sc key <= n)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n remaining);
    phase4_pos_bounds (Seq.create 0 0) sa k remaining (Seq.index sc key) key
#pop-options

// Step C tracking
#push-options "--z3rlimit 50"
let phase4_c_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (k n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa k n remaining /\
      Seq.length sa == n /\ n > 0 /\ remaining <= n /\ L.in_range sa k /\
      remaining > 0 /\ key <= k /\
      key == Seq.index sa (remaining - 1) /\
      Seq.length sc == k + 1 /\ Seq.length sc' == k + 1 /\
      (forall (v: nat). v <= k /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1)
    (ensures phase4_c_inv sc' sa k n (remaining - 1))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n remaining);
    reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc' sa k n (remaining - 1));
    // Give SMT the count extension facts
    let aux (v: nat)
      : Lemma (requires v <= k)
              (ensures SeqP.count v (Seq.slice sa (remaining - 1) n) ==
                       (if v = Seq.index sa (remaining - 1) then 1 else 0) +
                       SeqP.count v (Seq.slice sa remaining n))
      = count_extend_suffix sa remaining v
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// Helper: sc[v] >= 0 from phase4_c_inv
#push-options "--z3rlimit 50"
let phase4_sc_nonneg (sc: Seq.seq int) (sa: Seq.seq nat) (k n remaining: nat) (v: nat)
  : Lemma (requires phase4_c_inv sc sa k n remaining /\
                    Seq.length sc == k + 1 /\ Seq.length sa == n /\ remaining <= n /\
                    v <= k)
          (ensures Seq.index sc v >= 0)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n remaining);
    // count_le sa v = count_le sa (v-1) + count(v, sa) >= count(v, sa)
    count_le_step sa v;
    // count(v, sa) = count(v, prefix) + count(v, suffix) >= count(v, suffix)
    SeqP.lemma_count_slice sa remaining
    // So sc[v] = count_le sa v - count(v, suffix) >= 0
#pop-options

// Step B filling
#push-options "--z3rlimit 100"
let phase4_b_step (sc sc': Seq.seq int) (sa sb_curr sb_curr': Seq.seq nat) (k n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa k n remaining /\
      phase4_b_inv sc sa sb_curr k n /\
      Seq.length sa == n /\ n > 0 /\ remaining <= n /\ L.in_range sa k /\
      remaining > 0 /\ key <= k /\
      Seq.length sc == k + 1 /\ Seq.length sb_curr == n /\
      key == Seq.index sa (remaining - 1) /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      Seq.length sc' == k + 1 /\
      (forall (v: nat). v <= k /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.length sb_curr' == n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb_curr' p == Seq.index sb_curr p) /\
      Seq.index sb_curr' (Seq.index sc key - 1) == key)
    (ensures phase4_b_inv sc' sa sb_curr' k n)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n remaining);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb_curr k n);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc' sa sb_curr' k n);
    let pos = Seq.index sc key in
    count_le_bounded sa key;
    // Per-case proof for each v
    let target (v: (v:nat{v < Seq.length sc'}))
      : Lemma (requires v <= k)
              (ensures (forall (p: nat). Seq.index sc' v <= p /\ p < count_le sa v ==>
                          p < n /\ Seq.index sb_curr' p == v))
      = if v < key then (
          // pos-1 >= count_le sa v, so all p in [sc'[v], count_le sa v) satisfy p < count_le sa v <= pos-1
          // hence p != pos-1, sb_curr'[p] = sb_curr[p] = v (old b_inv, sc'[v]=sc[v])
          write_pos_not_in_smaller_range sa k remaining key v pos
        ) else if v > key then (
          // pos-1 < sc[v] = sc'[v], so all p >= sc'[v] satisfy p > pos-1
          // hence p != pos-1, sb_curr'[p] = sb_curr[p] = v (old b_inv, sc'[v]=sc[v])
          phase4_sc_nonneg sc sa k n remaining v;
          count_le_step sa v;
          write_pos_not_in_larger_range sc sa k remaining key v pos (Seq.index sc v)
        ) else (
          // v = key: sc'[key] = pos-1
          // p = pos-1: sb_curr'[pos-1] = key = v
          // p > pos-1: p >= pos = sc[key], old b_inv: sb_curr[p] = key, p != pos-1: sb_curr'[p] = key = v
          ()
        )
    in
    Classical.forall_intro (Classical.move_requires target)
#pop-options

// At remaining=0: extract sorted
#push-options "--z3rlimit 50"
let phase4_final_sorted (sc: Seq.seq int) (sa sb_curr: Seq.seq nat) (k n: nat)
  : Lemma (requires phase4_c_inv sc sa k n 0 /\ phase4_b_inv sc sa sb_curr k n /\
                    Seq.length sc == k + 1 /\ Seq.length sa == n /\ n > 0 /\ Seq.length sb_curr == n /\ L.in_range sa k)
          (ensures L.sorted sb_curr)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n 0);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb_curr k n);
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    let aux (v: (v:nat{v < Seq.length sc}))
      : Lemma (requires v <= k)
              (ensures Seq.index sc v == (if v = 0 then 0 else count_le sa (v - 1)))
      = count_le_step sa v;
        if v = 0 then count_le_negative sa (-1)
    in
    Classical.forall_intro (Classical.move_requires aux);
    count_le_full sa k;
    count_le_negative sa (-1);
    final_sorted sa sb_curr k
#pop-options

// At remaining=0: extract permutation
#push-options "--z3rlimit 50"
let phase4_final_perm (sc: Seq.seq int) (sa sb_curr: Seq.seq nat) (k n: nat)
  : Lemma (requires phase4_c_inv sc sa k n 0 /\ phase4_b_inv sc sa sb_curr k n /\
                    Seq.length sc == k + 1 /\ Seq.length sa == n /\ n > 0 /\ Seq.length sb_curr == n /\ L.in_range sa k)
          (ensures L.permutation sb_curr sa)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa k n 0);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb_curr k n);
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    let aux (v: (v:nat{v < Seq.length sc}))
      : Lemma (requires v <= k)
              (ensures Seq.index sc v == (if v = 0 then 0 else count_le sa (v - 1)))
      = count_le_step sa v;
        if v = 0 then count_le_negative sa (-1)
    in
    Classical.forall_intro (Classical.move_requires aux);
    count_le_full sa k;
    count_le_negative sa (-1);
    final_perm sa sb_curr k
#pop-options
