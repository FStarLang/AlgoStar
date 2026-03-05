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

/// Content tracking: per-group multiset + order (for permutation + stability)
[@@"opaque_to_smt"]
let phase4_content_inv (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) : prop =
  Seq.length sc == base /\ Seq.length sa == n /\ Seq.length sb == n /\ base > 0 /\
  remaining <= n /\
  (forall (v: nat). v < base ==>
    (let lo = Seq.index sc v in
     let hi = digit_count_le sa v d base in
     lo >= 0 /\ hi <= n /\ lo <= hi /\
     // Multiset: for each x, count of x in filled block =
     //   count of x in processed suffix where digit(x) == v
     (forall (x: nat).
       SeqP.count x (Seq.slice sb lo hi) ==
         (if B.digit x d base = v
          then SeqP.count x (Seq.slice sa remaining n)
          else 0)))) /\
  // Order preservation (stability)
  (forall (v: nat). v < base ==>
    (let lo = Seq.index sc v in
     let hi = digit_count_le sa v d base in
     (forall (p1 p2: nat). lo <= p1 /\ p1 < p2 /\ p2 < hi /\
       Seq.index sb p1 <> Seq.index sb p2 ==>
       (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
         Seq.index sa j1 == Seq.index sb p1 /\ Seq.index sa j2 == Seq.index sb p2))))

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

#push-options "--z3rlimit 100"
let phase4_content_inv_init (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      Seq.length sb == Seq.length sa /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_content_inv sc sa sb d base (Seq.length sa) (Seq.length sa))
  = reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base (Seq.length sa) (Seq.length sa));
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
  = if Seq.length s = 0 then ()
    else b_count_eq_seqp_count (Seq.tail s) x

/// Slice split: count over [a, c) = count over [a, b) + count over [b, c)
let slice_count_split (s: Seq.seq nat) (a b c: nat) (x: nat)
  : Lemma (requires a <= b /\ b <= c /\ c <= Seq.length s)
          (ensures SeqP.count x (Seq.slice s a c) ==
                   SeqP.count x (Seq.slice s a b) + SeqP.count x (Seq.slice s b c))
  = let mid = Seq.slice s a c in
    let left = Seq.slice s a b in
    let right = Seq.slice s b c in
    assert (Seq.equal mid (Seq.append left right));
    SeqP.lemma_append_count_aux x left right

(* ========== Phase 4 position bounds ========== *)

#push-options "--z3rlimit 80"
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

#push-options "--z3rlimit 120"
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
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc' sa sb' d base n);
    let pos = Seq.index sc key in
    digit_count_le_bounded sa key d base;
    let target (v: nat{v < base}) : Lemma
      (forall (p: nat). Seq.index sc' v <= p /\ p < digit_count_le sa v d base ==>
        p < n /\ B.digit (Seq.index sb' p) d base == v)
      = if v < key then
          write_pos_outside_smaller sa d base remaining key v pos
        else if v > key then
          write_pos_outside_larger sa d base remaining key v pos (Seq.index sc v)
        else ()
    in
    Classical.forall_intro (Classical.move_requires target)
#pop-options

(* ========== Phase 4 step: content tracking ========== *)

/// pos is not in block v when v <> key
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
    if v < key then
      write_pos_outside_smaller sa d base remaining key v (Seq.index sc key)
    else
      write_pos_outside_larger sa d base remaining key v (Seq.index sc key) (Seq.index sc v)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
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
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n remaining);
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n remaining);
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc' sa sb' d base n (remaining - 1));
    let pos = Seq.index sc key - 1 in
    let elem = Seq.index sa (remaining - 1) in
    // For v != key: block unchanged (pos not in this block)
    // For v == key: block expands by one element (elem)
    let prove_v (v: nat{v < base}) : Lemma
      (let lo' = Seq.index sc' v in
       let hi = digit_count_le sa v d base in
       lo' >= 0 /\ hi <= n /\ lo' <= hi /\
       (forall (x: nat).
         SeqP.count x (Seq.slice sb' lo' hi) ==
           (if B.digit x d base = v
            then SeqP.count x (Seq.slice sa (remaining - 1) n)
            else 0)) /\
       (forall (p1 p2: nat). lo' <= p1 /\ p1 < p2 /\ p2 < hi /\
         Seq.index sb' p1 <> Seq.index sb' p2 ==>
         (exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
           Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)))
      = let lo = Seq.index sc v in
        let lo' = Seq.index sc' v in
        let hi = digit_count_le sa v d base in
        digit_count_le_bounded sa v d base;
        if v <> key then begin
          // Block unchanged: pos is outside [lo, hi)
          pos_not_in_other_block sc sa d base n remaining key v;
          assert (lo' == lo);
          // sb' and sb agree on [lo, hi)
          assert (forall (p:nat). lo <= p /\ p < hi ==> Seq.index sb' p == Seq.index sb p);
          assert (Seq.equal (Seq.slice sb' lo hi) (Seq.slice sb lo hi));
          // Suffix: digit(elem) = key != v, so if digit(x) = v then x != elem
          // count(x, sa[remaining-1..n-1]) = count(x, sa[remaining..n-1]) + (if x = elem then 1 else 0)
          // Since digit(x) = v != key = digit(elem), x != elem
          // So count(x, sa[remaining-1..n-1]) = count(x, sa[remaining..n-1])
          let full = Seq.slice sa (remaining - 1) n in
          let mid = Seq.slice sa (remaining - 1) remaining in
          let right = Seq.slice sa remaining n in
          assert (Seq.equal full (Seq.append mid right));
          let count_ext (x: nat) : Lemma
            (requires B.digit x d base = v)
            (ensures SeqP.count x full == SeqP.count x right)
            = SeqP.lemma_append_count_aux x mid right;
              assert (Seq.length mid == 1 /\ Seq.index mid 0 == elem);
              // digit(x) = v != key = digit(elem), so x != elem
              // count(x, mid) = 0
              ()
          in
          Classical.forall_intro (Classical.move_requires count_ext)
        end else begin
          // v == key: block expands from [lo, hi) to [lo-1, hi) = [pos, hi)
          assert (lo' == pos);
          let new_slice = Seq.slice sb' pos hi in
          let old_slice = Seq.slice sb lo hi in
          let one_elem = Seq.create 1 elem in
          assert (Seq.equal new_slice (Seq.append one_elem old_slice));
          let full = Seq.slice sa (remaining - 1) n in
          let mid = Seq.slice sa (remaining - 1) remaining in
          let right = Seq.slice sa remaining n in
          assert (Seq.equal full (Seq.append mid right));
          // Multiset proof
          let count_ext (x: nat) : Lemma
            (SeqP.count x new_slice ==
              (if B.digit x d base = key
               then SeqP.count x full else 0))
            = SeqP.lemma_append_count_aux x one_elem old_slice;
              SeqP.lemma_append_count_aux x mid right;
              assert (Seq.length mid == 1 /\ Seq.index mid 0 == elem)
          in
          Classical.forall_intro count_ext;
          // Order preservation proof
          let order_proof (p1 p2: nat) : Lemma
            (requires pos <= p1 /\ p1 < p2 /\ p2 < hi /\
              Seq.index sb' p1 <> Seq.index sb' p2)
            (ensures exists (j1 j2: nat). j1 < j2 /\ j2 < n /\
              Seq.index sa j1 == Seq.index sb' p1 /\ Seq.index sa j2 == Seq.index sb' p2)
            = if p1 = pos then begin
                assert (Seq.index sb' p2 == Seq.index sb p2);
                let y = Seq.index sb p2 in
                assert (Seq.index old_slice (p2 - lo) == y);
                assert (SeqP.count y old_slice > 0);
                assert (SeqP.count y right > 0);
                let j2_local = count_positive_find right y in
                assert (Seq.index sa (remaining + j2_local) == y);
                assert (remaining - 1 < remaining + j2_local)
              end else begin
                assert (Seq.index sb' p1 == Seq.index sb p1);
                assert (Seq.index sb' p2 == Seq.index sb p2)
              end
          in
          Classical.forall_intro (fun (p1:nat) ->
            Classical.forall_intro (Classical.move_requires (order_proof p1)))
        end
    in
    Classical.forall_intro (Classical.move_requires prove_v)
#pop-options

(* ========== Phase 4 final: extract results ========== *)

/// sorted_on_digit from block structure  
#push-options "--z3rlimit 80"
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
          assert (B.digit (Seq.index sb k) d base <= B.digit (Seq.index sb (k + 1)) d base) by (
            FStar.Tactics.norm [];
            FStar.Tactics.smt ()
          );
          prove_sorted (k + 1);
          assert (Seq.equal (Seq.tail (Seq.slice sb k n)) (Seq.slice sb (k + 1) n))
        end
    in
    prove_sorted 0;
    assert (Seq.equal (Seq.slice sb 0 n) sb)
#pop-options

/// B.permutation from content invariant
#push-options "--z3rlimit 80"
let phase4_final_perm (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_content_inv sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base > 0 /\ Seq.length sc == base)
    (ensures B.permutation sa sb)
  = reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n 0);
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n 0);
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    // At remaining=0: blocks cover [0, n), each x counted once
    // count(x, sb) = count(x, block_digit(x)) = count(x, sa)
    // sc[v] = dcl(v-1) at remaining=0
    let sc_eq (v:nat{v < base}) : Lemma
      (Seq.index sc v == digit_count_le sa (v - 1) d base) =
      digit_count_le_step sa v d base
    in
    digit_count_le_full sa d base;
    digit_count_le_negative sa (-1) d base;
    // Count(x, sb[0..dcl(v)]) telescopes over blocks
    let rec count_prefix (x:nat) (v:nat) : Lemma
      (requires v <= base)
      (ensures (let hi = if v = 0 then 0 else digit_count_le sa (v - 1) d base in
                SeqP.count x (Seq.slice sb 0 hi) ==
                  (if B.digit x d base < v then SeqP.count x sa else 0)))
      (decreases v)
      = if v = 0 then
          assert (Seq.equal (Seq.slice sb 0 0) Seq.empty)
        else begin
          count_prefix x (v - 1);
          let lo = if v - 1 = 0 then 0 else digit_count_le sa (v - 2) d base in
          let hi = digit_count_le sa (v - 1) d base in
          if v >= 2 then digit_count_le_bounded sa (v - 2) d base;
          digit_count_le_bounded sa (v - 1) d base;
          slice_count_split sb 0 lo hi x;
          sc_eq (v - 1);
          ()
        end
    in
    let perm_x (x:nat) : Lemma (B.count sa x == B.count sb x) =
      b_count_eq_seqp_count sa x;
      b_count_eq_seqp_count sb x;
      B.digit_bound x d base;
      count_prefix x base;
      assert (Seq.equal (Seq.slice sb 0 n) sb)
    in
    Classical.forall_intro perm_x
#pop-options

/// Wrap all three into is_stable_sort_on_digit
#push-options "--z3rlimit 80"
let phase4_final_is_stable (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_b_inv sc sa sb d base n /\
      phase4_content_inv sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base >= 2 /\ Seq.length sc == base)
    (ensures Stab.is_stable_sort_on_digit sa sb d base)
  = phase4_final_sorted_on_digit sc sa sb d base n;
    phase4_final_perm sc sa sb d base n;
    // Stability from content_inv order part
    reveal_opaque (`%phase4_c_inv) (phase4_c_inv sc sa d base n 0);
    reveal_opaque (`%phase4_b_inv) (phase4_b_inv sc sa sb d base n);
    reveal_opaque (`%phase4_content_inv) (phase4_content_inv sc sa sb d base n 0);
    assert (Seq.equal (Seq.slice sa 0 n) sa);
    reveal_opaque (`%Stab.is_stable_sort_on_digit) (Stab.is_stable_sort_on_digit sa sb d base)
#pop-options
