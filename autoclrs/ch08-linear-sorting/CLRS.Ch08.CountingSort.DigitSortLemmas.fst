(*
   Lemmas for digit-based counting sort (used by multi-digit RadixSort).
   
   Adapts StableLemmas for digit-keyed sorting where the key for element x
   is digit(x, d, base) rather than x itself.
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.CountingSort.DigitSortLemmas

open FStar.Seq
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical
module B = CLRS.Ch08.RadixSort.Base
module Stab = CLRS.Ch08.RadixSort.Stability

(* ========== digit_count_le: count elements with digit(elem, d, base) <= v ========== *)

let rec digit_count_le (s: Seq.seq nat) (v: int) (d: nat) (base: nat)
  : Tot nat (decreases (Seq.length s))
  = if Seq.length s = 0 then 0
    else if B.digit (Seq.head s) d base <= v
         then 1 + digit_count_le (Seq.tail s) v d base
         else digit_count_le (Seq.tail s) v d base

let rec digit_count_le_bounded (s: Seq.seq nat) (v: int) (d base: nat)
  : Lemma (ensures digit_count_le s v d base <= Seq.length s) (decreases Seq.length s)
  = if Seq.length s = 0 then () else digit_count_le_bounded (Seq.tail s) v d base

let rec digit_count_le_negative (s: Seq.seq nat) (v: int) (d base: nat)
  : Lemma (requires v < 0) (ensures digit_count_le s v d base == 0) (decreases Seq.length s)
  = if Seq.length s = 0 then () else digit_count_le_negative (Seq.tail s) v d base

/// Count of elements with digit == v (direct recursive)
let rec digit_count (s: Seq.seq nat) (v: nat) (d base: nat)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if B.digit (Seq.head s) d base = v then 1 else 0) + digit_count (Seq.tail s) v d base

/// digit_count_le s v = digit_count_le s (v-1) + digit_count s v
let rec digit_count_le_step (s: Seq.seq nat) (v: int) (d base: nat)
  : Lemma (requires v >= 0 /\ base > 0)
          (ensures digit_count_le s v d base ==
                   digit_count_le s (v - 1) d base + digit_count s v d base)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else digit_count_le_step (Seq.tail s) v d base

let rec digit_count_le_monotone (s: Seq.seq nat) (v1 v2: int) (d base: nat)
  : Lemma (requires v1 <= v2) (ensures digit_count_le s v1 d base <= digit_count_le s v2 d base)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else digit_count_le_monotone (Seq.tail s) v1 v2 d base

let rec digit_count_le_full (s: Seq.seq nat) (d base: nat)
  : Lemma (requires base > 0)
          (ensures digit_count_le s (base - 1) d base == Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      B.digit_bound (Seq.head s) d base;
      digit_count_le_full (Seq.tail s) d base
    end

/// digit_count distributes over append
let rec digit_count_append (s1 s2: Seq.seq nat) (v d base: nat)
  : Lemma (ensures digit_count (Seq.append s1 s2) v d base ==
                   digit_count s1 v d base + digit_count s2 v d base)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then
      assert (Seq.equal (Seq.append s1 s2) s2)
    else begin
      assert (Seq.equal (Seq.tail (Seq.append s1 s2)) (Seq.append (Seq.tail s1) s2));
      assert (Seq.head (Seq.append s1 s2) == Seq.head s1);
      digit_count_append (Seq.tail s1) s2 v d base
    end

(* ========== Phase 2: digit counting ========== *)

let digit_counts_match_prefix (sc: Seq.seq int) (sa: Seq.seq nat)
                               (d base: nat) (progress: nat) : prop =
  Seq.length sc == base /\ base > 0 /\
  progress <= Seq.length sa /\
  (forall (v: nat). v < base ==>
    Seq.index sc v == digit_count (Seq.slice sa 0 progress) v d base)

let digit_counts_match (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat) : prop =
  digit_counts_match_prefix sc sa d base (Seq.length sa)

/// When all counts are zero, digit_counts_match_prefix holds at progress 0
let digit_counts_match_prefix_zero (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\
      Seq.length sa > 0 /\
      (forall (v: nat). v < base ==> Seq.index sc v == 0))
    (ensures digit_counts_match_prefix sc sa d base 0)
  = assert (Seq.equal (Seq.slice sa 0 0) Seq.empty)

/// Phase 2 step: increment count for digit of sa[j]
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let digit_count_phase_step
  (sa: Seq.seq nat) (sc sc': Seq.seq int) (j: nat) (d base: nat) (key: nat)
  : Lemma (requires
      digit_counts_match_prefix sc sa d base j /\
      j < Seq.length sa /\ base > 0 /\
      key == B.digit (Seq.index sa j) d base /\ key < base /\
      Seq.length sc' == base /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key + 1)
    (ensures digit_counts_match_prefix sc' sa d base (j + 1))
  = let s1 = Seq.slice sa 0 j in
    let s2 = Seq.slice sa j (j + 1) in
    assert (Seq.equal (Seq.slice sa 0 (j + 1)) (Seq.append s1 s2));
    let aux (v: nat{v < base}) : Lemma
      (digit_count (Seq.slice sa 0 (j + 1)) v d base ==
       digit_count s1 v d base + (if v = key then 1 else 0))
      = digit_count_append s1 s2 v d base;
        assert (Seq.length s2 == 1);
        assert (Seq.head s2 == Seq.index sa j)
    in
    Classical.forall_intro (fun (v: nat{v < base}) -> aux v)
#pop-options

(* ========== Phase 3: prefix sums for digit counts ========== *)

let digit_prefix_sum_inv (sc: Seq.seq int) (sa: Seq.seq nat)
                          (d base: nat) (progress: nat) : prop =
  Seq.length sc == base /\ base > 0 /\
  progress >= 1 /\ progress <= base /\
  (forall (v: nat). v < progress ==> Seq.index sc v == digit_count_le sa v d base) /\
  (forall (v: nat). v >= progress /\ v < base ==>
    Seq.index sc v == digit_count (Seq.slice sa 0 (Seq.length sa)) v d base)

let digit_prefix_sum_init (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires digit_counts_match sc sa d base /\ base > 0)
          (ensures digit_prefix_sum_inv sc sa d base 1)
  = digit_count_le_step sa 0 d base;
    digit_count_le_negative sa (-1) d base;
    assert (Seq.equal (Seq.slice sa 0 (Seq.length sa)) sa)

#push-options "--z3rlimit 30"
let digit_prefix_sum_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (d base: nat) (i: nat)
  : Lemma (requires digit_prefix_sum_inv sc sa d base i /\
                    i >= 1 /\ i < base /\
                    Seq.length sc' == base /\
                    (forall (v: nat). v < base /\ v <> i ==> Seq.index sc' v == Seq.index sc v) /\
                    Seq.index sc' i == Seq.index sc i + Seq.index sc (i - 1))
          (ensures digit_prefix_sum_inv sc' sa d base (i + 1))
  = assert (Seq.equal (Seq.slice sa 0 (Seq.length sa)) sa);
    digit_count_le_step sa i d base
#pop-options

let digit_prefix_sum_complete (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires digit_prefix_sum_inv sc sa d base base)
          (ensures (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base) /\
                   Seq.index sc (base - 1) == Seq.length sa)
  = digit_count_le_full sa d base

(* ========== Phase 4 tracking invariants ========== *)

/// C-tracking: count array matches expected
[@@"opaque_to_smt"]
let phase4_c_inv (sc: Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) : prop =
  Seq.length sc == base /\ Seq.length sa == n /\ n > 0 /\ base > 0 /\
  remaining <= n /\
  (forall (v: nat). v < base ==>
    Seq.index sc v == digit_count_le sa v d base -
      digit_count (Seq.slice sa remaining n) v d base)

/// B-filling: filled positions have correct digit values
[@@"opaque_to_smt"]
let phase4_b_inv (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat) : prop =
  Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ base > 0 /\
  (forall (v: nat). v < base ==>
    (forall (p: nat). Seq.index sc v <= p /\ p < digit_count_le sa v d base ==>
      p < n /\ B.digit (Seq.index sb p) d base == v))

/// Content tracking: per-group multiset (for permutation)
[@@"opaque_to_smt"]
let phase4_content_inv_multiset (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) : prop =
  Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ base > 0 /\
  remaining <= n /\
  (forall (v: nat). v < base ==>
    (let lo = Seq.index sc v in
     let hi = digit_count_le sa v d base in
     lo >= 0 /\ hi <= n /\ lo <= hi /\
     (forall (x: nat).
       SeqP.count x (Seq.slice sb lo hi) ==
         (if B.digit x d base = v
          then SeqP.count x (Seq.slice sa remaining n)
          else 0))))

/// Content tracking: per-group order (for stability)
[@@"opaque_to_smt"]
let phase4_content_inv_order (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) : prop =
  Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ base > 0 /\
  remaining <= n /\
  (forall (v: nat). v < base ==>
    (let lo = Seq.index sc v in
     let hi = digit_count_le sa v d base in
     lo >= 0 /\ hi <= n /\ lo <= hi /\
     (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
       Seq.index sb p1 <> Seq.index sb p2 ==>
       (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
         Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2))))

/// Combined content invariant
[@@"opaque_to_smt"]
let phase4_content_inv (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) : prop =
  phase4_content_inv_multiset sc sa sb d base n remaining /\
  phase4_content_inv_order sc sa sb d base n remaining

(* ========== Phase 4 init ========== *)

#push-options "--z3rlimit 50"
let phase4_c_inv_init (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_c_inv sc sa d base (Seq.length sa) (Seq.length sa))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base (Seq.length sa) (Seq.length sa));
    assert (Seq.equal (Seq.slice sa (Seq.length sa) (Seq.length sa)) Seq.empty)
#pop-options

let phase4_b_inv_init (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      Seq.length sb == Seq.length sa /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_b_inv sc sa sb d base (Seq.length sa))
  = reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb d base (Seq.length sa));
    digit_count_le_full sa d base

#push-options "--z3rlimit 100 --split_queries always"
let phase4_content_inv_init (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      Seq.length sb == Seq.length sa /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_content_inv sc sa sb d base (Seq.length sa) (Seq.length sa))
  = reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base (Seq.length sa) (Seq.length sa));
    reveal_opaque (`%phase4_content_inv_multiset) (phase4_content_inv_multiset sc sa sb d base (Seq.length sa) (Seq.length sa));
    reveal_opaque (`%phase4_content_inv_order) (phase4_content_inv_order sc sa sb d base (Seq.length sa) (Seq.length sa));
    let n = Seq.length sa in
    digit_count_le_full sa d base;
    assert (Seq.equal (Seq.slice sa n n) Seq.empty);
    // For each v: lo = digit_count_le(v) = hi, empty slice
    let aux_v (v: nat) : Lemma
      (requires v < base)
      (ensures (digit_count_le sa v d base <= n))
      = digit_count_le_bounded sa v d base
    in
    Classical.forall_intro (Classical.move_requires aux_v)
#pop-options

(* ========== Suffix extension helper ========== *)

let digit_count_extend_suffix (sa: Seq.seq nat) (remaining: nat) (v d base: nat)
  : Lemma (requires remaining > 0 /\ remaining <= Seq.length sa /\ base > 0)
          (ensures (let n = Seq.length sa in
                   digit_count (Seq.slice sa (remaining - 1) n) v d base ==
                   (if v = B.digit (Seq.index sa (remaining - 1)) d base then 1 else 0) +
                   digit_count (Seq.slice sa remaining n) v d base))
  = let n = Seq.length sa in
    let full = Seq.slice sa (remaining - 1) n in
    let left = Seq.slice sa (remaining - 1) remaining in
    let right = Seq.slice sa remaining n in
    assert (Seq.equal full (Seq.append left right));
    digit_count_append left right v d base;
    assert (Seq.length left == 1);
    assert (Seq.head left == Seq.index sa (remaining - 1))

(* ========== Helper: witness from positive count ========== *)

/// If SeqP.count x s > 0, then x appears at some index in s
let rec count_positive_find (s: Seq.seq nat) (x: nat)
  : Pure nat (requires SeqP.count x s > 0)
             (ensures fun i -> i < Seq.length s /\ Seq.index s i == x)
             (decreases Seq.length s)
  = if Seq.head s = x then 0
    else 1 + count_positive_find (Seq.tail s) x

/// Bridge: B.count s x == SeqP.count x s
let rec b_count_eq_seqp_count (s: Seq.seq nat) (x: nat)
  : Lemma (ensures B.count s x == SeqP.count x s) (decreases Seq.length s)
  = B.count_unfold s x;
    if Seq.length s = 0 then ()
    else b_count_eq_seqp_count (Seq.tail s) x

/// Slice split: count over [a, c) = count over [a, b) + count over [b, c)
let slice_count_split (s: Seq.seq nat) (a b c: nat) (x: nat)
  : Lemma (requires a <= b /\ b <= c /\ c <= Seq.length s)
          (ensures SeqP.count x (Seq.slice s a c) ==
                   SeqP.count x (Seq.slice s a b) + SeqP.count x (Seq.slice s b c))
  = let mid = Seq.slice s a c in
    let left = Seq.slice s a b in
    let right = Seq.slice s b c in
    Seq.lemma_eq_intro mid (Seq.append left right);
    SeqP.lemma_append_count_aux x left right

/// Count is preserved when sequences are pointwise equal
let rec count_pointwise_eq (s1 s2: Seq.seq nat) (x: nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    (forall (i:nat). i < Seq.length s1 ==> Seq.index s1 i == Seq.index s2 i))
          (ensures SeqP.count x s1 == SeqP.count x s2)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else begin
      assert (Seq.head s1 == Seq.head s2);
      let t1 = Seq.tail s1 in
      let t2 = Seq.tail s2 in
      assert (Seq.length t1 == Seq.length t2);
      let aux (i:nat{i < Seq.length t1}) : Lemma
        (Seq.index t1 i == Seq.index t2 i)
        = assert (Seq.index s1 (i+1) == Seq.index s2 (i+1))
      in
      Classical.forall_intro aux;
      count_pointwise_eq t1 t2 x
    end

/// Count on a length-1 slice: avoids forall precondition that breaks under split queries
let count_singleton (s: Seq.seq nat) (lo hi: nat) (x: nat)
  : Lemma (requires lo < hi /\ hi <= Seq.length s /\ hi - lo == 1)
          (ensures SeqP.count x (Seq.slice s lo hi) == (if Seq.index s lo = x then 1 else 0))
  = Seq.lemma_index_slice s lo hi 0

/// If s has element x at index i, then count x s > 0
let rec count_index_positive (s: Seq.seq nat) (i: nat) (x: nat)
  : Lemma (requires i < Seq.length s /\ Seq.index s i == x)
          (ensures SeqP.count x s > 0)
          (decreases Seq.length s)
  = if i = 0 then ()
    else count_index_positive (Seq.tail s) (i - 1) x

(* ========== Phase 4 position bounds ========== *)

#push-options "--z3rlimit 80 --z3refresh --split_queries always"
let phase4_pos_bounds (sc: Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base)
    (ensures Seq.index sc key >= 1 /\ Seq.index sc key <= n)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    let suffix = Seq.slice sa remaining n in
    digit_count_le_bounded sa key d base;
    // key is the digit of sa[remaining-1] which is NOT in suffix
    // So digit_count(sa, key) = digit_count(prefix, key) + digit_count(suffix, key) >= 1 + digit_count(suffix, key)
    let prefix = Seq.slice sa 0 remaining in
    assert (Seq.equal sa (Seq.append prefix suffix));
    digit_count_append prefix suffix key d base;
    // digit_count(prefix, key) >= 1 since prefix contains sa[remaining-1] with digit key
    let pre1 = Seq.slice sa 0 (remaining - 1) in
    let mid = Seq.slice sa (remaining - 1) remaining in
    assert (Seq.equal prefix (Seq.append pre1 mid));
    digit_count_append pre1 mid key d base;
    assert (Seq.length mid == 1);
    assert (Seq.head mid == Seq.index sa (remaining - 1));
    // sc[key] = digit_count_le(key) - digit_count(suffix, key)
    digit_count_le_step sa key d base
#pop-options

(* ========== Phase 4 step: C tracking ========== *)

#push-options "--z3rlimit 60"
let phase4_c_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1)
    (ensures phase4_c_inv sc' sa d base n (remaining - 1))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc' sa d base n (remaining - 1));
    let aux (v: nat{v < base}) : Lemma
      (digit_count (Seq.slice sa (remaining - 1) n) v d base ==
       (if v = key then 1 else 0) + digit_count (Seq.slice sa remaining n) v d base)
      = digit_count_extend_suffix sa remaining v d base
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ========== Phase 4 step: B filling ========== *)

/// Write position is outside smaller blocks
#push-options "--z3rlimit 60"
let write_pos_outside_smaller (sa: Seq.seq nat) (d base: nat) (remaining: nat)
                               (key v: nat) (pos: int)
  : Lemma (requires
      base > 0 /\ remaining > 0 /\ remaining <= Seq.length sa /\
      key < base /\ v < base /\ v < key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == digit_count_le sa key d base -
        digit_count (Seq.slice sa remaining (Seq.length sa)) key d base /\
      pos >= 1)
    (ensures pos - 1 >= digit_count_le sa v d base)
  = digit_count_le_step sa key d base;
    let n = Seq.length sa in
    let suffix = Seq.slice sa remaining n in
    let prefix = Seq.slice sa 0 remaining in
    assert (Seq.equal sa (Seq.append prefix suffix));
    digit_count_append prefix suffix key d base;
    let pre1 = Seq.slice sa 0 (remaining - 1) in
    let mid = Seq.slice sa (remaining - 1) remaining in
    assert (Seq.equal prefix (Seq.append pre1 mid));
    digit_count_append pre1 mid key d base;
    digit_count_le_monotone sa v (key - 1) d base
#pop-options

/// Write position is below larger blocks
#push-options "--z3rlimit 60"
let write_pos_outside_larger (sa: Seq.seq nat) (d base: nat) (remaining: nat)
                              (key v: nat) (pos sc_v: int)
  : Lemma (requires
      base > 0 /\ remaining > 0 /\ remaining <= Seq.length sa /\
      key < base /\ v < base /\ v > key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == digit_count_le sa key d base -
        digit_count (Seq.slice sa remaining (Seq.length sa)) key d base /\
      pos >= 1 /\
      sc_v == digit_count_le sa v d base -
        digit_count (Seq.slice sa remaining (Seq.length sa)) v d base)
    (ensures pos - 1 < sc_v)
  = let n = Seq.length sa in
    digit_count_le_step sa v d base;
    let suffix = Seq.slice sa remaining n in
    let prefix = Seq.slice sa 0 remaining in
    assert (Seq.equal sa (Seq.append prefix suffix));
    digit_count_append prefix suffix v d base;
    digit_count_le_monotone sa key (v - 1) d base
#pop-options

/// Sub-lemma for phase4_b_step: does NOT reveal opaque defs.
/// Takes the needed facts from the old b-invariant explicitly.
#push-options "--z3rlimit 40 --z3refresh --fuel 2 --ifuel 2"
let phase4_b_step_core
  (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sc == base /\ Seq.length sb == n /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      base > 0 /\ remaining > 0 /\ remaining <= n /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      // sc encodes: sc[v] = digit_count_le(sa, v) - digit_count(suffix, v)
      (forall (v: nat). v < base ==>
        Seq.index sc v == digit_count_le sa v d base -
          digit_count (Seq.slice sa remaining n) v d base) /\
      // Old b-inv: filled positions have correct digits
      (forall (v: nat). v < base ==>
        (forall (p: nat). Seq.index sc v <= p /\ p < digit_count_le sa v d base ==>
          p < n /\ B.digit (Seq.index sb p) d base == v)) /\
      // sc' update
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      // sb' update
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures
      (forall (v: nat). v < base ==>
        (forall (p: nat). Seq.index sc' v <= p /\ p < digit_count_le sa v d base ==>
          p < n /\ B.digit (Seq.index sb' p) d base == v)))
  = let pos = Seq.index sc key in
    digit_count_le_bounded sa key d base;
    let target (v: nat{v < base}) : Lemma
      (forall (p: nat). Seq.index sc' v <= p /\ p < digit_count_le sa v d base ==>
        p < n /\ B.digit (Seq.index sb' p) d base == v)
      = if v < key then
          write_pos_outside_smaller sa d base remaining key v pos
        else if v > key then
          write_pos_outside_larger sa d base remaining key v pos (Seq.index sc v)
        else begin
          // v == key: the newly written position has the right digit,
          // and all old positions are preserved by the sb' update.
          assert (Seq.index sc' key == pos - 1);
          assert (B.digit (Seq.index sb' (pos - 1)) d base == key);
          let aux (p: nat) : Lemma
            (requires pos - 1 <= p /\ p < digit_count_le sa key d base)
            (ensures p < n /\ B.digit (Seq.index sb' p) d base == key)
            = if p = pos - 1 then ()
              else begin
                assert (p >= pos);
                assert (Seq.index sb' p == Seq.index sb p)
              end
          in
          Classical.forall_intro (Classical.move_requires aux)
        end
    in
    Classical.forall_intro (Classical.move_requires target)
#pop-options

/// Wrapper that reveals opaque defs and calls the core
#push-options "--z3rlimit 40 --z3refresh"
let phase4_b_step (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_b_inv sc sa sb d base n /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures phase4_b_inv sc' sa sb' d base n)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb d base n);
    phase4_b_step_core sc sc' sa sb sb' d base n remaining key;
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc' sa sb' d base n)
#pop-options

(* ========== Phase 4 step: content tracking ========== *)

/// pos is not in block v when v <> key
#push-options "--z3rlimit 40"
let pos_not_in_other_block (sc: Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) (key v: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      remaining > 0 /\ key < base /\ v < base /\ v <> key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.index sc key >= 1)
    (ensures (let pos = Seq.index sc key - 1 in
             pos < Seq.index sc v \/ pos >= digit_count_le sa v d base))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    let suffix = Seq.slice sa remaining n in
    assert (Seq.index sc key == digit_count_le sa key d base - digit_count suffix key d base);
    assert (Seq.index sc v == digit_count_le sa v d base - digit_count suffix v d base);
    if v < key then
      write_pos_outside_smaller sa d base remaining key v (Seq.index sc key)
    else
      write_pos_outside_larger sa d base remaining key v (Seq.index sc key) (Seq.index sc v)
#pop-options

/// Sub-lemma: v <> key, multiset part
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1 --z3refresh --split_queries always"
let content_step_other_multiset
  (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key v: nat)
  (lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\ v < base /\ v <> key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      lo >= 0 /\ hi <= n /\ lo <= hi /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = v
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)) /\
      (forall (p:nat). lo <= p /\ p < hi ==> Seq.index sb' p == Seq.index sb p))
    (ensures
      (forall (x: nat).
        SeqP.count x (Seq.slice sb' lo hi) ==
          (if B.digit x d base = v
           then SeqP.count x (Seq.slice sa (remaining - 1) n)
           else 0)))
  = let elem = Seq.index sa (remaining - 1) in
    let count_ext (x: nat) : Lemma
      (SeqP.count x (Seq.slice sb' lo hi) ==
        (if B.digit x d base = v
         then SeqP.count x (Seq.slice sa (remaining - 1) n)
         else 0))
      = count_pointwise_eq (Seq.slice sb' lo hi) (Seq.slice sb lo hi) x;
        slice_count_split sa (remaining - 1) remaining n x
    in
    Classical.forall_intro count_ext
#pop-options

/// Sub-lemma: v <> key, order preservation part  
#push-options "--z3rlimit 20"
let content_step_other_order
  (sa sb sb': Seq.seq nat) (d base n: nat)
  (lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      lo >= 0 /\ hi <= n /\ lo <= hi /\
      (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb p1 <> Seq.index sb p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2)) /\
      (forall (p:nat). lo <= p /\ p < hi ==> Seq.index sb' p == Seq.index sb p))
    (ensures
      (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb' p1 <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)))
  = ()
#pop-options

/// Sub-lemma for phase4_content_step: v == key multiset proof
/// Does NOT reveal opaque invariants; takes needed facts as preconditions
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1 --z3refresh --split_queries always"
let content_step_key_multiset
  (sa sb sb': Seq.seq nat)
  (d base n remaining: nat) (key: nat)
  (pos lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == lo - 1 /\ hi == digit_count_le sa key d base /\
      lo >= 1 /\ hi <= n /\ lo <= hi /\
      // Old invariant facts for block key (at lo..hi):
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)) /\
      // sb' agrees with sb except at pos
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' pos == Seq.index sa (remaining - 1))
    (ensures
      pos >= 0 /\ hi <= n /\ pos <= hi /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb' pos hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa (remaining - 1) n)
           else 0)))
  = let elem = Seq.index sa (remaining - 1) in
    digit_count_le_bounded sa key d base;
    let count_ext (x: nat) : Lemma
      (SeqP.count x (Seq.slice sb' pos hi) ==
        (if B.digit x d base = key
         then SeqP.count x (Seq.slice sa (remaining - 1) n) else 0))
      = // Split count on sb' side: [pos..hi) = [pos..lo) ++ [lo..hi)
        slice_count_split sb' pos lo hi x;
        // [lo..hi) unchanged: sb'[lo..hi) == sb[lo..hi)
        count_pointwise_eq (Seq.slice sb' lo hi) (Seq.slice sb lo hi) x;
        // Split count on sa side: [remaining-1..n) = [remaining-1..remaining) ++ [remaining..n)
        slice_count_split sa (remaining - 1) remaining n x;
        // Both single-element slices contain elem, so counts match
        count_singleton sb' pos lo x;
        count_singleton sa (remaining - 1) remaining x
    in
    Classical.forall_intro count_ext
#pop-options

/// Helper: given sb[lo..hi) has element y at position p2 (lo <= p2 < hi),
/// find a witness j2 in sa[remaining..n) such that sa[remaining + j2] == y.
/// Returns the offset j2 within the suffix sa[remaining..n).
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --z3refresh"
let key_order_find_witness
  (sa sb: Seq.seq nat) (d base n remaining: nat) (key: nat)
  (lo hi p2: nat) (y: nat)
  : Pure nat
    (requires
      Seq.length sa == n /\ Seq.length sb == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\
      lo >= 0 /\ hi <= n /\ lo <= hi /\
      lo <= p2 /\ p2 < hi /\
      Seq.index sb p2 == y /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)))
    (ensures fun j2 ->
      j2 < n - remaining /\
      Seq.index sa (remaining + j2) == y)
  = Seq.lemma_index_slice sb lo hi (p2 - lo);
    count_index_positive (Seq.slice sb lo hi) (p2 - lo) y;
    let right = Seq.slice sa remaining n in
    assert (SeqP.count y right > 0);
    let j2 = count_positive_find right y in
    Seq.lemma_index_slice sa remaining n j2;
    j2
#pop-options

/// Sub-sub-lemma: introduces the existential witness explicitly when p1 = pos
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --z3refresh"
let key_order_new_elem_witness
  (sa sb sb': Seq.seq nat)
  (d base n remaining: nat) (key: nat)
  (pos lo hi p2: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == lo - 1 /\ hi == digit_count_le sa key d base /\
      lo >= 1 /\ hi <= n /\ lo <= hi /\
      pos < p2 /\ p2 < hi /\
      Seq.index sb' pos <> Seq.index sb' p2 /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)) /\
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' pos == Seq.index sa (remaining - 1))
    (ensures exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
        Seq.index sa j1 == Seq.index sb' pos /\ Seq.index sa j2 == Seq.index sb' p2)
  = let y = Seq.index sb p2 in
    let j2_off = key_order_find_witness sa sb d base n remaining key lo hi p2 y in
    let j1 : nat = remaining - 1 in
    let j2 : nat = remaining + j2_off in
    assert (Seq.index sa j1 == Seq.index sb' pos);
    assert (Seq.index sa j2 == y)
#pop-options

/// Sub-lemma for content_step_key_order: p1 = pos case (new element)
/// This is trivial given key_order_new_elem_witness
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --z3refresh"
let key_order_case_new
  (sa sb sb': Seq.seq nat)
  (d base n remaining: nat) (key: nat)
  (pos lo hi: nat) (p2: (p2:nat{p2 < n}))
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == lo - 1 /\ hi == digit_count_le sa key d base /\
      lo >= 1 /\ hi <= n /\ lo <= hi /\
      pos < p2 /\ p2 < hi /\
      Seq.index sb' pos <> Seq.index sb' p2 /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)) /\
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' pos == Seq.index sa (remaining - 1))
    (ensures exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
        Seq.index sa j1 == Seq.index sb' pos /\ Seq.index sa j2 == Seq.index sb' p2)
  = key_order_new_elem_witness sa sb sb' d base n remaining key pos lo hi p2
#pop-options

/// Sub-lemma for content_step_key_order: p1 > pos case (old element)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --z3refresh"
let key_order_case_old
  (sa sb sb': Seq.seq nat)
  (n: nat) (pos lo hi p1 p2: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      lo >= 1 /\ hi <= n /\ lo <= hi /\
      pos == lo - 1 /\
      pos < p1 /\ p1 < p2 /\ p2 < hi /\
      Seq.index sb' p1 <> Seq.index sb' p2 /\
      (forall (q1 q2: nat). lo <= q1 /\ q1 < q2 /\ q2 < hi /\
        Seq.index sb q1 <> Seq.index sb q2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb q1 /\ Seq.index sa j2 == Seq.index sb q2)) /\
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p))
    (ensures exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
        Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)
  = ()
#pop-options

/// Sub-lemma for phase4_content_step: v == key, NEW element order (p1=pos)
/// Uses bounded types to avoid Seq.index subtyping issues under split queries
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --z3refresh --split_queries always"
let content_step_key_order
  (sa sb sb': Seq.seq nat)
  (d base n remaining: nat) (key: nat)
  (pos lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      remaining > 0 /\ remaining <= n /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      pos == lo - 1 /\ hi == digit_count_le sa key d base /\
      lo >= 1 /\ hi <= n /\ lo <= hi /\
      (forall (x: nat).
        SeqP.count x (Seq.slice sb lo hi) ==
          (if B.digit x d base = key
           then SeqP.count x (Seq.slice sa remaining n)
           else 0)) /\
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' pos == Seq.index sa (remaining - 1))
    (ensures
      (forall (p2: (p2:nat{p2 < n})). pos < p2 /\ p2 < hi /\
        Seq.index sb' pos <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' pos /\ Seq.index sa j2 == Seq.index sb' p2)))
  = Classical.forall_intro (Classical.move_requires
      (key_order_case_new sa sb sb' d base n remaining key pos lo hi))
#pop-options

/// Main content step: reveals invariants, dispatches to sub-lemmas
#push-options "--z3rlimit 160 --fuel 0 --ifuel 0 --z3refresh --split_queries always"
let phase4_content_step_multiset (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv_multiset sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures phase4_content_inv_multiset sc' sa sb' d base n (remaining - 1))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    reveal_opaque (`%phase4_content_inv_multiset) (phase4_content_inv_multiset sc sa sb d base n remaining);
    reveal_opaque (`%phase4_content_inv_multiset) (phase4_content_inv_multiset sc' sa sb' d base n (remaining - 1));
    let pos = Seq.index sc key - 1 in
    let prove_v (v: nat{v < base}) : Lemma
      (let lo' = Seq.index sc' v in
       let hi = digit_count_le sa v d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (x: nat).
         SeqP.count x (Seq.slice sb' lo' hi) ==
           (if B.digit x d base = v
            then SeqP.count x (Seq.slice sa (remaining - 1) n)
            else 0)))
      = let lo = Seq.index sc v in
        let hi = digit_count_le sa v d base in
        digit_count_le_bounded sa v d base;
        if v <> key then begin
          pos_not_in_other_block sc sa d base n remaining key v;
          content_step_other_multiset sa sb sb' d base n remaining key v lo hi
        end else begin
          assert (v == key);
          assert (lo == Seq.index sc key);
          assert (pos == lo - 1);
          assert (lo >= 1);
          assert (hi <= n);
          assert (lo <= hi);
          assert (forall (x: nat).
            SeqP.count x (Seq.slice sb lo hi) ==
              (if B.digit x d base = key
               then SeqP.count x (Seq.slice sa remaining n)
               else 0));
          assert (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p);
          assert (Seq.index sb' pos == Seq.index sa (remaining - 1));
          content_step_key_multiset sa sb sb' d base n remaining key pos lo hi
        end
    in
    Classical.forall_intro (Classical.move_requires prove_v)
#pop-options

/// Extract multiset invariant from combined content invariant (avoids exposing order's exists)
let content_inv_extract_multiset (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat)
  : Lemma (requires phase4_content_inv sc sa sb d base n remaining)
    (ensures phase4_content_inv_multiset sc sa sb d base n remaining)
  = reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n remaining)

/// Extract order invariant from combined content invariant
let content_inv_extract_order (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat)
  : Lemma (requires phase4_content_inv sc sa sb d base n remaining)
    (ensures phase4_content_inv_order sc sa sb d base n remaining)
  = reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n remaining)

/// Extract b_inv for a specific position p: p is in block v with digit v
let b_inv_at (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat) (v: nat) (p: nat)
  : Lemma (requires phase4_b_inv sc sa sb d base n /\ v < base /\
      Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\
      Seq.index sc v <= p /\ p < digit_count_le sa v d base)
    (ensures p < n /\ B.digit (Seq.index sb p) d base == v)
  = reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb d base n)

/// Extract sc[v] = dcl(v-1) from opaque c_inv at remaining=0
let c_inv_sc_eq (sc: Seq.seq int) (sa: Seq.seq nat) (d base n: nat) (v: nat)
  : Lemma (requires phase4_c_inv sc sa d base n 0 /\ Seq.length sc == base /\ v < base /\ base > 0)
    (ensures Seq.index sc v == digit_count_le sa (v - 1) d base)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n 0);
    digit_count_le_step sa v d base

/// Find which block a position p belongs to: returns w such that dcl(w-1) <= p < dcl(w)
let rec find_block (sa: Seq.seq nat) (d base n: nat) (p: nat) (w: nat)
  : Pure nat
    (requires Seq.length sa == n /\ base > 0 /\ w <= base /\ p < n /\
      digit_count_le sa (w - 1) d base <= p)
    (ensures fun v -> w <= v /\ v < base /\
      digit_count_le sa (v - 1) d base <= p /\ p < digit_count_le sa v d base)
    (decreases base - w)
  = if w >= base then (
      // dcl(w-1) >= dcl(base-1) = n > p, contradiction with requires
      digit_count_le_monotone sa (base - 1) (w - 1) d base;
      digit_count_le_full sa d base;
      // unreachable, but need to return something
      w - 1
    ) else if p < digit_count_le sa w d base then
      w
    else
      find_block sa d base n p (w + 1)

/// Reverse direction: if digit(sb[p]) == v at remaining=0, then p is in block v
/// Uses find_block (pure) + b_inv_at (reveals b_inv for one pair) + c_inv_sc_eq (reveals c_inv for one v)
let in_block_of_digit (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat) (p: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_b_inv sc sa sb d base n /\
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sc == base /\ base > 0 /\ p < n)
    (ensures (let v = B.digit (Seq.index sb p) d base in
      v < base /\
      Seq.index sc v <= p /\ p < digit_count_le sa v d base))
  = let v = B.digit (Seq.index sb p) d base in
    B.digit_bound (Seq.index sb p) d base;
    digit_count_le_negative sa (-1) d base;
    // Find which block p belongs to
    let w = find_block sa d base n p 0 in
    // b_inv_at: digit(sb[p]) == w for block w
    c_inv_sc_eq sc sa d base n w;
    b_inv_at sc sa sb d base n w p;
    // digit(sb[p]) == w, but digit(sb[p]) == v, so w == v
    c_inv_sc_eq sc sa d base n v

/// Extract per-v multiset block count from opaque multiset invariant (avoids revealing full forall v. forall x)
let multiset_block_count (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) (v: nat) (x: nat)
  : Lemma (requires phase4_content_inv_multiset sc sa sb d base n remaining /\
      Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ v < base /\ base > 0 /\
      remaining <= n)
    (ensures (let lo = Seq.index sc v in
       let hi = digit_count_le sa v d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       SeqP.count x (Seq.slice sb lo hi) ==
         (if B.digit x d base = v then SeqP.count x (Seq.slice sa remaining n) else 0)))
  = reveal_opaque (`%phase4_content_inv_multiset) (phase4_content_inv_multiset sc sa sb d base n remaining)

/// Extract order property for a specific v from the opaque order invariant.
/// This reveals the invariant only within this small lemma, keeping it hidden from callers.
#push-options "--z3rlimit 20"
let order_inv_extract (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) (v: nat)
  : Lemma (requires
      phase4_content_inv_order sc sa sb d base n remaining /\ v < base /\
      Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n)
    (ensures
      (let lo = Seq.index sc v in
       let hi = digit_count_le sa v d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb p1 <> Seq.index sb p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2))))
  = reveal_opaque (`%phase4_content_inv_order) (phase4_content_inv_order sc sa sb d base n remaining)
#pop-options

/// Extract order witness for a SPECIFIC pair (p1, p2) — no forall in postcondition
let order_inv_extract_pair (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) (v: nat) (p1 p2: nat)
  : Lemma (requires
      phase4_content_inv_order sc sa sb d base n remaining /\ v < base /\
      Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\
      Seq.index sc v <= p1 /\ p1 < p2 /\ p2 < digit_count_le sa v d base /\
      p2 < n /\ Seq.index sb p1 <> Seq.index sb p2)
    (ensures exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
      Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2)
  = reveal_opaque (`%phase4_content_inv_order) (phase4_content_inv_order sc sa sb d base n remaining)

/// Pack per-v order properties back into the opaque order invariant.
/// Takes a proof FUNCTION to avoid QI explosion from having all per-v exists in scope.
#push-options "--z3rlimit 40"
let order_inv_pack (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat)
  (proof: (v:nat{v < base}) -> Lemma
    (requires Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n)
    (ensures
      (let lo = Seq.index sc v in
       let hi = digit_count_le sa v d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb p1 <> Seq.index sb p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2)))))
  : Lemma (requires
      Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ base > 0 /\
      remaining <= n)
    (ensures phase4_content_inv_order sc sa sb d base n remaining)
  = let aux (v:nat{v < base}) : Lemma
      (let lo = Seq.index sc v in
       let hi = digit_count_le sa v d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb p1 <> Seq.index sb p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2)))
      = proof v
    in
    Classical.forall_intro aux;
    reveal_opaque (`%phase4_content_inv_order) (phase4_content_inv_order sc sa sb d base n remaining)
#pop-options

/// Combine key order: merge new-element (p1=pos) and old-element (p1>=lo) results
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let combine_key_order
  (sa sb': Seq.seq nat) (n pos lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb' == n /\
      pos >= 0 /\ pos == lo - 1 /\ lo >= 1 /\ hi <= n /\ lo <= hi /\
      // New element: p1 = pos pairs
      (forall (p2: nat). p2 < n /\ pos < p2 /\ p2 < hi /\
        Seq.index sb' pos <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' pos /\ Seq.index sa j2 == Seq.index sb' p2)) /\
      // Old elements: p1 >= lo pairs
      (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb' p1 <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)))
    (ensures
      (forall (p1 p2: nat). pos <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb' p1 <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)))
  = ()
#pop-options

/// Old-element order for key block: bridge from indirect to direct sb' agreement
#push-options "--z3rlimit 20"
let key_block_old_order
  (sa sb sb': Seq.seq nat) (n pos lo hi: nat)
  : Lemma (requires
      Seq.length sa == n /\ Seq.length sb == n /\ Seq.length sb' == n /\
      pos >= 0 /\ lo >= 1 /\ hi <= n /\ lo <= hi /\ pos == lo - 1 /\
      // Old order for [lo, hi) in sb
      (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb p1 <> Seq.index sb p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2)) /\
      // Direct agreement: sb' == sb on [lo, hi)
      (forall (p:nat). lo <= p /\ p < hi ==> Seq.index sb' p == Seq.index sb p))
    (ensures
      (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
        Seq.index sb' p1 <> Seq.index sb' p2 ==>
        (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
          Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)))
  = ()
#pop-options

/// Bridge from indirect sb' agreement (p <> pos) to direct (lo <= p < hi)
#push-options "--z3rlimit 20"
let bridge_agreement (sb sb': Seq.seq nat) (n pos lo hi: nat)
  : Lemma (requires
      Seq.length sb == n /\ Seq.length sb' == n /\
      hi <= n /\
      (pos < lo \/ pos >= hi) /\
      (forall (p:nat). p < n /\ p <> pos ==> Seq.index sb' p == Seq.index sb p))
    (ensures
      (forall (p:nat). lo <= p /\ p < hi ==> Seq.index sb' p == Seq.index sb p))
  = ()
#pop-options

/// Per-v order step for v <> key case
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --z3refresh --split_queries always"
let phase4_content_step_order_for_v_neq
  (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat) (v: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      Seq.length sb == n /\ remaining > 0 /\ key < base /\ v < base /\ v <> key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (w: nat). w < base /\ w <> key ==> Seq.index sc' w == Seq.index sc w) /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      // Old order for this v
      (let lo = Seq.index sc v in
       let hi = digit_count_le sa v d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb p1 <> Seq.index sb p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2))))
    (ensures
      (let lo' = Seq.index sc' v in
       let hi = digit_count_le sa v d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb' p1 <> Seq.index sb' p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2))))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    let pos = Seq.index sc key - 1 in
    let lo = Seq.index sc v in
    let hi = digit_count_le sa v d base in
    digit_count_le_bounded sa v d base;
    pos_not_in_other_block sc sa d base n remaining key v;
    // Bridge: pos not in [lo, hi) => sb' agrees with sb on [lo, hi)
    bridge_agreement sb sb' n pos lo hi;
    content_step_other_order sa sb sb' d base n lo hi
#pop-options

/// Per-v order step for v == key case: uses isolated sub-lemma calls
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --z3refresh --split_queries always"
let phase4_content_step_order_for_v_eq
  (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      Seq.length sb == n /\ remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1) /\
      // Old order for key block
      (let lo = Seq.index sc key in
       let hi = digit_count_le sa key d base in
       lo >= 0 /\ hi <= n /\ lo <= hi /\
       (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb p1 <> Seq.index sb p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2))) /\
      // Count facts for key block
      (let lo_key = Seq.index sc key in
       let hi_key = digit_count_le sa key d base in
       (forall (x: nat).
         SeqP.count x (Seq.slice sb lo_key hi_key) ==
           (if B.digit x d base = key
            then SeqP.count x (Seq.slice sa remaining n)
            else 0))))
    (ensures
      (let lo' = Seq.index sc' key in
       let hi = digit_count_le sa key d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb' p1 <> Seq.index sb' p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2))))
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    let pos = Seq.index sc key - 1 in
    let lo = Seq.index sc key in
    let hi = digit_count_le sa key d base in
    digit_count_le_bounded sa key d base;
    // Step 1: New element order (p1 = pos, p2 > pos)
    content_step_key_order sa sb sb' d base n remaining key pos lo hi;
    // Step 2: Bridge indirect to direct agreement
    bridge_agreement sb sb' n pos lo hi;
    // Step 3: Old element order (p1 >= lo, p2 > p1)
    key_block_old_order sa sb sb' n pos lo hi;
    // Step 4: Combine
    combine_key_order sa sb' n pos lo hi
#pop-options

/// Combined extract+step for v <> key (hides intermediate exists from caller)
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let order_step_v_neq
  (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat) (v: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv_order sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\ v < base /\ v <> key /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v': nat). v' < base /\ v' <> key ==> Seq.index sc' v' == Seq.index sc v') /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures
      (let lo' = Seq.index sc' v in
       let hi = digit_count_le sa v d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb' p1 <> Seq.index sb' p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2))))
  = order_inv_extract sc sa sb d base n remaining v;
    phase4_content_step_order_for_v_neq sc sc' sa sb sb' d base n remaining key v
#pop-options

/// Combined extract+step for v == key (hides intermediate exists from caller)
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let order_step_v_eq
  (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv_order sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v': nat). v' < base /\ v' <> key ==> Seq.index sc' v' == Seq.index sc v') /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1) /\
      (let lo_key = Seq.index sc key in
       let hi_key = digit_count_le sa key d base in
       lo_key >= 0 /\ hi_key <= n /\ lo_key <= hi_key /\
       (forall (x: nat).
         SeqP.count x (Seq.slice sb lo_key hi_key) ==
           (if B.digit x d base = key
            then SeqP.count x (Seq.slice sa remaining n)
            else 0))))
    (ensures
      (let lo' = Seq.index sc' key in
       let hi = digit_count_le sa key d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb' p1 <> Seq.index sb' p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2))))
  = order_inv_extract sc sa sb d base n remaining key;
    phase4_content_step_order_for_v_eq sc sc' sa sb sb' d base n remaining key
#pop-options

/// Orchestrator: proves order step using extract/pack to avoid QI explosion.
/// Never reveals the full order invariant in a single query.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --z3refresh --split_queries always"
let phase4_content_step_order (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv_order sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1) /\
      // Explicit count facts for key block (from multiset invariant, passed by caller)
      (let lo_key = Seq.index sc key in
       let hi_key = digit_count_le sa key d base in
       lo_key >= 0 /\ hi_key <= n /\ lo_key <= hi_key /\
       (forall (x: nat).
         SeqP.count x (Seq.slice sb lo_key hi_key) ==
           (if B.digit x d base = key
            then SeqP.count x (Seq.slice sa remaining n)
            else 0))))
    (ensures phase4_content_inv_order sc' sa sb' d base n (remaining - 1))
  = // Build proof function for each v — calls opaque wrappers to avoid intermediate exists in context
    let prove_v (v: nat{v < base}) : Lemma
      (requires Seq.length sc' == base /\ Seq.length sa == n /\ Seq.length sb' == n)
      (ensures
        (let lo' = Seq.index sc' v in
         let hi = digit_count_le sa v d base in
         lo' >= 0 /\ hi <= n /\ lo' <= hi /\
         (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
           Seq.index sb' p1 <> Seq.index sb' p2 ==>
           (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
             Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2))))
      = if v <> key then
          order_step_v_neq sc sc' sa sb sb' d base n remaining key v
        else
          order_step_v_eq sc sc' sa sb sb' d base n remaining key
    in
    // Pack using proof function — avoids QI by not materializing all per-v results at once
    order_inv_pack sc' sa sb' d base n (remaining - 1) prove_v
#pop-options

/// Combined content step
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --z3refresh"
let phase4_content_step (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures phase4_content_inv sc' sa sb' d base n (remaining - 1))
  = reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n remaining);
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc' sa sb' d base n (remaining - 1));
    // Extract multiset count facts for key block before calling sub-steps
    reveal_opaque (`%phase4_content_inv_multiset) (phase4_content_inv_multiset sc sa sb d base n remaining);
    reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    digit_count_le_bounded sa key d base;
    phase4_content_step_multiset sc sc' sa sb sb' d base n remaining key;
    phase4_content_step_order sc sc' sa sb sb' d base n remaining key
#pop-options

(* ========== Phase 4 final: extract results ========== *)

/// sorted_on_digit from block structure  
#push-options "--z3rlimit 120 --z3refresh --split_queries always"
let phase4_final_sorted_on_digit (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\ phase4_b_inv sc sa sb d base n /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base > 0 /\ Seq.length sc == base)
    (ensures B.sorted_on_digit sb d base)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n 0);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb d base n);
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    // At remaining=0: sc[v] = digit_count_le(v) - digit_count(sa, v) = digit_count_le(v-1)
    // b_inv: positions [digit_count_le(v-1), digit_count_le(v)) have digit v
    // This gives sorted_on_digit
    // sc[v] = dcl(v) - digit_count(sa, v) = dcl(v-1) at remaining=0
    let sc_eq (v:nat{v < base}) : Lemma
      (Seq.index sc v == digit_count_le sa (v - 1) d base) =
      digit_count_le_step sa v d base
    in
    // For any p < n, find its block and establish digit(sb[p])
    let digit_at (p:nat{p < n}) : Lemma
      (exists (v:nat). v < base /\
        digit_count_le sa (v - 1) d base <= p /\
        p < digit_count_le sa v d base /\
        B.digit (Seq.index sb p) d base == v) =
      digit_count_le_full sa d base;
      digit_count_le_negative sa (-1) d base;
      let rec find_v (v:nat)
        : Pure nat (requires v <= base /\
                    digit_count_le sa (v - 1) d base <= p)
                   (ensures fun r -> r < base /\
                      digit_count_le sa (r - 1) d base <= p /\
                      p < digit_count_le sa r d base)
                   (decreases (base - v))
        = if p < digit_count_le sa v d base then v
          else begin
            digit_count_le_monotone sa v (base - 1) d base;
            find_v (v + 1)
          end
      in
      let v = find_v 0 in
      sc_eq v;
      assert (B.digit (Seq.index sb p) d base == v)
    in
    // Prove sorted_on_digit by induction
    let rec prove_sorted (k:nat) : Lemma
      (requires k <= n)
      (ensures B.sorted_on_digit (Seq.slice sb k n) d base)
      (decreases (n - k))
      = if n - k <= 1 then ()
        else begin
          digit_at k;
          digit_at (k + 1);
          // k is in block vk with dcl(vk-1) <= k, k+1 is in block vk1 with dcl(vk1-1) <= k+1
          // If vk > vk1 then dcl(vk-1) >= dcl(vk1) > k+1 > k >= dcl(vk-1), contradiction
          // So digit(sb[k]) = vk <= vk1 = digit(sb[k+1])
          let vk = B.digit (Seq.index sb k) d base in
          let vk1 = B.digit (Seq.index sb (k + 1)) d base in
          if vk > vk1 then begin
            // vk - 1 >= vk1, so dcl(vk-1) >= dcl(vk1) by monotonicity
            digit_count_le_monotone sa vk1 (vk - 1) d base;
            // dcl(vk1) > k+1 (from digit_at(k+1)) and dcl(vk-1) <= k (from digit_at(k))
            // So k >= dcl(vk-1) >= dcl(vk1) > k+1, contradiction
            assert false
          end;
          prove_sorted (k + 1);
          assert (Seq.equal (Seq.tail (Seq.slice sb k n)) (Seq.slice sb (k + 1) n))
        end
    in
    prove_sorted 0;
    assert (Seq.equal (Seq.slice sb 0 n) sb)
#pop-options

/// B.permutation from content invariant
#push-options "--z3rlimit 200 --z3refresh"
let phase4_final_perm (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_content_inv sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base > 0 /\ Seq.length sc == base)
    (ensures B.permutation sa sb)
  = // Extract multiset only (no order invariant in context)
    content_inv_extract_multiset sc sa sb d base n 0;
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    digit_count_le_full sa d base;
    digit_count_le_negative sa (-1) d base;
    // Count(x, sb[0..hi]) telescopes over blocks where hi = dcl(v-1) for v > 0
    let rec count_prefix (x:nat) (v:nat) (hi:nat) : Lemma
      (requires v <= base /\ hi <= n /\
        hi == (if v = 0 then 0 else digit_count_le sa (v - 1) d base))
      (ensures SeqP.count x (Seq.slice sb 0 hi) ==
                  (if B.digit x d base < v then SeqP.count x sa else 0))
      (decreases v)
      = if v = 0 then
          assert (Seq.equal (Seq.slice sb 0 0) Seq.empty)
        else begin
          // Extract sc[v-1] value and use as lo
          c_inv_sc_eq sc sa d base n (v - 1);
          let lo_sc = Seq.index sc (v - 1) in
          // lo_sc == dcl(v-2) from c_inv_sc_eq
          let lo = if v - 1 = 0 then 0 else digit_count_le sa (v - 2) d base in
          if v >= 2 then digit_count_le_bounded sa (v - 2) d base;
          if v = 1 then digit_count_le_negative sa (-1) d base;
          assert (lo == lo_sc);
          count_prefix x (v - 1) lo;
          digit_count_le_bounded sa (v - 1) d base;
          if v >= 2 then digit_count_le_monotone sa (v - 2) (v - 1) d base;
          slice_count_split sb 0 lo hi x;
          multiset_block_count sc sa sb d base n 0 (v - 1) x;
          ()
        end
    in
    let perm_x (x:nat) : Lemma (B.count sa x == B.count sb x) =
      b_count_eq_seqp_count sa x;
      b_count_eq_seqp_count sb x;
      B.digit_bound x d base;
      count_prefix x base n;
      assert (Seq.equal (Seq.slice sb 0 n) sb)
    in
    Classical.forall_intro perm_x
#pop-options

/// Extract stability witness for a specific pair (j1, j2) from opaque invariants.
/// Uses extraction helpers to avoid revealing full invariants in one context.
#push-options "--z3rlimit 80 --z3refresh"
let stability_witness (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat) (j1 j2: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_b_inv sc sa sb d base n /\
      phase4_content_inv_order sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base >= 2 /\ Seq.length sc == base /\
      j1 < j2 /\ j2 < n /\
      B.digit (Seq.index sb j1) d base == B.digit (Seq.index sb j2) d base /\
      Seq.index sb j1 <> Seq.index sb j2)
    (ensures exists (i1 i2: nat). i1 < i2 /\ i2 < n /\
      Seq.index sa i1 == Seq.index sb j1 /\ Seq.index sa i2 == Seq.index sb j2)
  = let v = B.digit (Seq.index sb j1) d base in
    // Establish j1, j2 are in block v
    in_block_of_digit sc sa sb d base n j1;
    in_block_of_digit sc sa sb d base n j2;
    // Use pair-specific extraction (no forall in postcondition)
    order_inv_extract_pair sc sa sb d base n 0 v j1 j2
#pop-options

/// Wrap all three into is_stable_sort_on_digit
#push-options "--z3rlimit 40 --z3refresh"
let phase4_final_is_stable (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_b_inv sc sa sb d base n /\
      phase4_content_inv sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base >= 2 /\ Seq.length sc == base)
    (ensures Stab.is_stable_sort_on_digit sa sb d base)
  = phase4_final_sorted_on_digit sc sa sb d base n;
    phase4_final_perm sc sa sb d base n;
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n 0);
    Stab.pack_is_stable sa sb d base
      (fun j1 j2 -> stability_witness sc sa sb d base n j1 j2)
#pop-options

/// For empty sequences, is_stable_sort_on_digit holds trivially
let empty_is_stable_on_digit (s1 s2: Seq.seq nat) (d base: nat)
  : Lemma (requires Seq.length s1 == 0 /\ Seq.length s2 == 0 /\ base >= 2)
          (ensures Stab.is_stable_sort_on_digit s1 s2 d base)
  = // Prove permutation s1 s2 by revealing count for empty sequences
    let aux (x: nat) : Lemma (B.count s1 x == B.count s2 x) =
      B.count_unfold s1 x;
      B.count_unfold s2 x
    in
    Classical.forall_intro aux;
    reveal_opaque (`%Stab.is_stable_sort_on_digit) (Stab.is_stable_sort_on_digit s1 s2 d base)
