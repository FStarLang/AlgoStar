# Radix Sort (CLRS §8.3)

## Top-Level Signatures

There is no `Impl.fsti` for Radix Sort. The signatures are defined
directly in `CLRS.Ch08.RadixSort.fst`:

### `radix_sort` (single-digit)

```fstar
fn radix_sort
  (a: A.array nat)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    S.in_range s0 (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s
  )
```

### `radix_sort_multidigit` (multi-digit)

```fstar
fn radix_sort_multidigit
  (a: A.array nat)
  (len: SZ.t)
  (base_val: SZ.t)     // Base for digit extraction (>= 2)
  (bigD: SZ.t)          // Number of digits
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    SZ.v base_val >= 2 /\
    SZ.v bigD > 0 /\
    SZ.v len > 0 /\
    (forall (i: nat). i < Seq.length s0 ==> Seq.index s0 i < B.pow (SZ.v base_val) (SZ.v bigD)) /\
    SZ.fits (SZ.v base_val + 2) /\
    SZ.fits (SZ.v len + SZ.v base_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s
  )
```

### Parameters

* `a` is a mutable array of `nat`.

* `len` is the number of elements.

* `k_val` is the maximum value (single-digit variant).

* `base_val` is the base for digit extraction (multi-digit). Must be
  ≥ 2.

* `bigD` is the number of digits. All elements must be < `base^bigD`.

### Preconditions

* `S.in_range s0 (SZ.v k_val)` — all elements ≤ `k_val` (single-digit).

* `forall i. i < length s0 ==> s0[i] < pow base bigD` — all elements
  fit in `bigD` digits (multi-digit).

* `SZ.v len > 0` — non-empty input.

* `SZ.v base_val >= 2` — meaningful base for digit extraction.

### Postcondition

Both variants ensure:

* `S.sorted s` — the output is sorted.

* `S.permutation s0 s` — the output is a permutation of the input.

Note: These use `CountingSort.Spec` definitions (`S.sorted`,
`S.permutation`) over `nat`, bridged from `RadixSort.Base` definitions
via `RadixSort.Bridge`.

## Auxiliary Definitions

### `sorted` (from `CLRS.Ch08.CountingSort.Spec`)

```fstar
let sorted (s: Seq.seq nat)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

All-pairs sorted over `nat`.

### `permutation` (from `CLRS.Ch08.CountingSort.Spec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq nat) : prop = (SeqP.permutation nat s1 s2)
```

### `digit` (from `CLRS.Ch08.RadixSort.Base`)

```fstar
let digit (k: nat) (d: nat) (base: nat) : nat =
  if base > 0 then (
    pow_positive base d;
    (k / pow base d) % base
  ) else 0
```

Extract the `d`-th digit of `k` in the given base:
`digit(k, d, base) = (k / base^d) mod base`.

### `sorted_up_to_digit` (from `CLRS.Ch08.RadixSort.Stability`)

```fstar
[@@"opaque_to_smt"]
let sorted_up_to_digit (s: seq nat) (max_d: nat) (base: nat) : prop =
  base > 0 /\
  (forall (i j: nat). {:pattern (index s i); (index s j)}
    i < j /\ j < length s ==>
    ((exists (d0: nat). d0 <= max_d /\
       digit (index s i) d0 base < digit (index s j) d0 base /\
       (forall (d': nat). d0 < d' /\ d' <= max_d ==>
         digit (index s i) d' base == digit (index s j) d' base)) \/
     (forall (d: nat). d <= max_d ==>
       digit (index s i) d base == digit (index s j) d base)))
```

Lexicographic ordering on digits 0..`max_d`. For any pair `i < j`,
either there exists a "most significant differing digit" `d0` where
`s[i]` has a smaller digit and all higher digits are equal, or all
digits are equal.

### `is_stable_sort_on_digit` (from `CLRS.Ch08.RadixSort.Stability`)

```fstar
[@@"opaque_to_smt"]
let is_stable_sort_on_digit (s_in s_out: seq nat) (d: nat) (base: nat) : prop =
  base > 0 /\
  permutation s_in s_out /\
  sorted_on_digit s_out d base /\
  (forall (j1 j2: nat). ...  (* stability condition *) )
```

Permutation + sorted on digit `d` + stability (equal-digit elements
preserve relative order).

### `pow` (from `CLRS.Ch08.RadixSort.Base`)

```fstar
let rec pow (base: nat) (exp: nat) : nat =
  if exp = 0 then 1
  else base * pow base (exp - 1)
```

## What Is Proven

1. **Single-digit variant**: Delegates to `counting_sort_inplace`.
   Trivially correct since sorting by the only digit = sorting by
   value.

2. **Multi-digit variant (CLRS RADIX-SORT)**: Full correctness of the
   `d`-pass algorithm:
   * **Loop invariant**: After pass `i`, the array is a permutation of
     the input and is `sorted_up_to_digit` on digits 0..`i`.
   * **Stability preservation**
     (`lemma_stable_pass_preserves_ordering`): If input is sorted on
     digits 0..`d-1` and we apply a stable sort on digit `d`, then
     the output is sorted on digits 0..`d` (CLRS Lemma 8.3).
   * **Full sort correctness**
     (`lemma_sorted_up_to_all_digits_implies_sorted`):
     `sorted_up_to_digit` on all `bigD` digits + all elements <
     `base^bigD` implies fully sorted by numeric value.
   * **Digit decomposition** (`digit_decomposition`): Any `k <
     base^bigD` equals the sum of its digits × powers of the base.

3. **Bridge module** (`RadixSort.Bridge`): Proves equivalence between
   `CountingSort.Spec` definitions (pairwise `sorted`, `SeqP.permutation`)
   and `RadixSort.Base` definitions (recursive `sorted`, count-based
   `permutation`).

**Zero admits, zero assumes.** All proof obligations across all files
are mechanically discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **No `Impl.fsti`.** The signatures are defined directly in the
   `.fst` file. There is no separate interface for downstream consumers.
   (A `.fsti` cannot currently be added due to a Pulse SMT limitation
   with `forall`-quantified preconditions during interface checking.)

2. **No complexity bounds.** Neither variant proves O(d·(n+k))
   complexity. No ghost counter is used.

3. ~~**`len > 0` precondition.** Both variants require non-empty input.~~
   **RESOLVED.** Both variants now accept empty arrays (`len = 0`).
   `radix_sort` delegates to `counting_sort_inplace` (which handles
   empty); `radix_sort_multidigit` returns early using Bridge lemmas.

4. **Multi-digit requires explicit bounds.** The caller must provide
   `bigD` and prove `forall i. s0[i] < pow base bigD`. The algorithm
   does not compute the required number of digits automatically.

5. **Two separate permutation/sorted definitions.** `RadixSort.Base`
   uses its own recursive `sorted` and count-based `permutation`,
   while `CountingSort.Spec` uses pairwise definitions. The `Bridge`
   module proves equivalence, but this duplication adds proof
   complexity.

6. **Single-digit variant is trivial.** `radix_sort` with `d=1` is
   just a wrapper around `counting_sort_inplace`. No radix-specific
   logic is exercised.

7. **Temporary buffer allocation.** `radix_sort_multidigit` allocates
   a temporary buffer `b` of size `len`, copies results back to `a`
   after each pass via `memcpy`, and frees `b` at the end. This
   doubles memory usage.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Time | O(d·(n+k)) expected | ❌ Not proven | N/A |

No complexity analysis is formally verified for the Pulse
implementation.

## Proof Structure

**`radix_sort_multidigit`**: Main loop from digit 0 to `bigD-1`:
1. Share `a`'s permission (half for read-only input).
2. Call `counting_sort_by_digit a b len base_val d`.
3. Gather `a`'s permission, copy `b` back to `a` via `memcpy`.
4. Maintain invariants:
   * `B.permutation s0 s_curr` (overall permutation).
   * `sorted_up_to_digit s_curr (d-1) base` (multi-digit ordering).
   * Element bounds preserved via `permutation_preserves_bounds`.
5. After loop: `FS.lemma_sorted_up_to_all_digits_implies_sorted`
   bridges from digit ordering to full numeric ordering.
6. `Bridge.base_sorted_implies_l_sorted` and
   `Bridge.base_perm_implies_s_perm` convert to `S.sorted`/`S.permutation`.

Key modules:
* **`RadixSort.Stability`**: Core theorem
  `lemma_stable_pass_preserves_ordering` — each stable pass extends
  the sorted-digit range.
* **`RadixSort.FullSort`**: `digit_decomposition` + lexicographic →
  numeric ordering bridge.
* **`RadixSort.Bridge`**: Definition equivalences.
* **`RadixSort.Base`**: Shared definitions (`digit`, `pow`, `sorted`,
  `permutation`).

## Files

| File | Role |
|------|------|
| `CLRS.Ch08.RadixSort.fst` | Pulse implementation (both variants) |
| `CLRS.Ch08.RadixSort.Base.fst` | Shared definitions (`digit`, `pow`, `sorted`, `permutation`) |
| `CLRS.Ch08.RadixSort.Stability.fst` | Stability theorem (CLRS Lemma 8.3) |
| `CLRS.Ch08.RadixSort.FullSort.fst` | Full sort correctness (digit decomposition → numeric ordering) |
| `CLRS.Ch08.RadixSort.MultiDigit.fst` | Pure multi-digit specifications and lemmas |
| `CLRS.Ch08.RadixSort.Spec.fst` | Pure digit decomposition and helpers |
| `CLRS.Ch08.RadixSort.Lemmas.fsti` | Public interface for key lemma results |
| `CLRS.Ch08.RadixSort.Lemmas.fst` | Re-exports key results from Stability and FullSort |
| `CLRS.Ch08.RadixSort.Bridge.fst` | Equivalences between CountingSort and RadixSort definitions |
| `CLRS.Ch08.CountingSort.Impl.fsti` | Counting sort interface (used as subroutine) |
| `CLRS.Ch08.CountingSort.DigitSortLemmas.fst` | Digit-keyed counting sort invariant lemmas |

## Rubric Compliance (per `autoclrs/audit/RUBRIC.md`)

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `RadixSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `RadixSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `RadixSort.Lemmas.fsti` | ✅ (new) |
| `Impl.fst` | `RadixSort.fst` | ✅ |
| `Impl.fsti` | — | ❌ Blocked (Pulse SMT limitation with `forall` preconditions) |
| `Complexity.fst` | — | ❌ Not present |
| `Complexity.fsti` | — | ❌ Not present |

## Profiling (Build from clean, -j4, wall-clock completion times)

| File | Completion (s) | Max z3rlimit | z3refresh | split_queries |
|------|---------------:|:------------:|:---------:|:-------------:|
| Base.fst | 1 | — | 0 | 0 |
| Stability.fst | 16 | 200 | 0 | 2 |
| Spec.fst | 27 | 200 | 0 | 0 |
| Bridge.fst | 196 | 40 | 0 | 0 |
| MultiDigit.fst | 199 | 100 | 0 | 2 |
| FullSort.fst | 202 | 50 | 0 | 0 |
| Lemmas.fsti | 202 | — | — | — |
| Lemmas.fst | 505 | — | 0 | 0 |
| RadixSort.fst | 585 | 200 | 0 | 0 |

## Checklist

Priority-ordered items for reaching a fully proven, high-quality
implementation:

- [x] Zero admits, zero assumes across all files
- [x] Rubric slots: Spec.fst, Lemmas.fst, Impl.fst
- [x] Lemmas.fsti interface file created
- [x] Multi-digit radix sort with full CLRS Lemma 8.3 stability proof
- [x] Empty-array support (`len = 0`) for both variants
- [x] Bridge module connecting CountingSort and RadixSort definitions
- [ ] **P1 (Rubric)**: Create `Impl.fsti` — currently blocked by Pulse
      SMT limitation with `forall`-quantified preconditions during
      interface checking. Revisit when Pulse toolchain is updated.
- [ ] **P2 (Warning)**: Address deprecated `Array.free` and
      `Reference.free` warnings in `RadixSort.fst` (lines 196-198).
- [ ] **P3 (Rubric)**: Add `Complexity.fst`/`.fsti` with O(d·(n+k))
      complexity proof or ghost counter.
- [ ] **P4 (Spec)**: Remove `distinct s` requirement from pure
      `radix_sort_correct` in `MultiDigit.fst` to match the Pulse
      implementation's generality.
- [ ] **P5 (Optimization)**: Reduce memory usage — `radix_sort_multidigit`
      currently allocates a temporary buffer `b` and copies back after
      each pass. Consider ping-pong buffer strategy.
