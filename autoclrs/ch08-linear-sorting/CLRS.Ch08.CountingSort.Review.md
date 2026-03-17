# Counting Sort (CLRS §8.2)

## Top-Level Signatures

Here are the three function signatures proven about Counting Sort in
`CLRS.Ch08.CountingSort.Impl.fsti`:

### `counting_sort_impl`

```fstar
fn counting_sort_impl
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (k_val: SZ.t)        // Maximum value in array
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    S.in_range sa (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    S.sorted sb' /\
    S.permutation sb' sa
  )
```

### `counting_sort_inplace`

```fstar
fn counting_sort_inplace
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

### `counting_sort_by_digit`

```fstar
fn counting_sort_by_digit
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (base_val: SZ.t)     // Base for digit extraction
  (d: nat)             // Digit position
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    SZ.v base_val >= 2 /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v base_val + 2) /\
    SZ.fits (SZ.v len + SZ.v base_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    Stab.is_stable_sort_on_digit sa sb' d (SZ.v base_val)
  )
```

### Parameters

* `a` is the input array of `nat` (natural numbers, not `int`). For
  `counting_sort_impl` and `counting_sort_by_digit`, it is read-only
  (half-permission `#0.5R`).

* `b` is the output array (separate from input for the CLRS-faithful
  and digit variants).

* `len` is the number of elements.

* `k_val` is the maximum value in the input (for `counting_sort_impl`
  and `counting_sort_inplace`). All elements must be ≤ `k_val`.

* `base_val` is the base for digit extraction (for
  `counting_sort_by_digit`). Must be ≥ 2.

* `d` is the digit position (for `counting_sort_by_digit`).

### Preconditions

* `S.in_range sa (SZ.v k_val)` — all input elements are ≤ `k_val`.

* `SZ.v len > 0` — non-empty input.

* `SZ.fits (SZ.v k_val + 2)` and `SZ.fits (SZ.v len + SZ.v k_val + 2)`
  — overflow guards for count-array indexing.

* For digit variant: `SZ.v base_val >= 2` — base must be at least 2.

### Postcondition

* **`counting_sort_impl`**: Output `sb'` is sorted and is a
  permutation of input `sa`. Input `a` is unchanged (half-permission
  returned).

* **`counting_sort_inplace`**: Array `a` is sorted in-place; output
  `s` is sorted and is a permutation of `s0`.

* **`counting_sort_by_digit`**: Output satisfies
  `is_stable_sort_on_digit sa sb' d (SZ.v base_val)` — a **different**
  postcondition from the other two. This means the output is sorted
  on digit `d`, is a permutation, and preserves relative order of
  elements with equal digit values (stability).

## Auxiliary Definitions

### `sorted` (from `CLRS.Ch08.CountingSort.Spec`)

```fstar
let sorted (s: Seq.seq nat)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

All-pairs sorted, over `nat` (not `int`).

### `permutation` (from `CLRS.Ch08.CountingSort.Spec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq nat) : prop = (SeqP.permutation nat s1 s2)
```

Standard permutation over `nat`, opaque to SMT.

### `in_range` (from `CLRS.Ch08.CountingSort.Spec`)

```fstar
let in_range (s:Seq.seq nat) (k:nat) : prop =
  forall (i:nat). i < Seq.length s ==> Seq.index s i <= k
```

All elements bounded by `k`.

### `is_stable_sort_on_digit` (from `CLRS.Ch08.RadixSort.Stability`)

```fstar
[@@"opaque_to_smt"]
let is_stable_sort_on_digit (s_in s_out: seq nat) (d: nat) (base: nat) : prop =
  base > 0 /\
  permutation s_in s_out /\
  sorted_on_digit s_out d base /\
  (forall (j1 j2: nat). {:pattern (index s_out j1); (index s_out j2)}
    j1 < j2 /\ j2 < length s_out /\
    digit (index s_out j1) d base == digit (index s_out j2) d base /\
    index s_out j1 <> index s_out j2 ==>
    (exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
      index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2))
```

This is a three-part property: (1) the output is a permutation of the
input, (2) the output is sorted on digit `d`, and (3) for any two
distinct elements with equal digit `d`, their relative order in the
output matches their relative order in the input (stability).

## What Is Proven

1. **CLRS-faithful counting sort** (`counting_sort_impl`): Separate
   input/output arrays, 4-phase algorithm (init, count, prefix sum,
   backwards placement). Proves sorted + permutation.

2. **In-place variant** (`counting_sort_inplace`): 2-phase
   (count + write-back). Simpler but not stable. Proves sorted +
   permutation.

3. **Digit-keyed variant** (`counting_sort_by_digit`): Stable sort by
   digit `d` for multi-digit radix sort. Proves
   `is_stable_sort_on_digit` — the strongest postcondition of the
   three, including stability.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **`counting_sort_by_digit` has a DIFFERENT postcondition** than the
   other two variants. It proves `is_stable_sort_on_digit` (stability)
   rather than `sorted /\ permutation`. This is correct — it is
   designed as a subroutine for radix sort, where stability is the key
   property.

2. **Over `nat`, not `int`.** All three variants operate on `seq nat`
   (natural numbers), not `seq int`. This excludes negative values.
   This is appropriate for counting sort (which requires non-negative
   keys) but means the module uses its own `sorted`/`permutation`
   definitions rather than the shared `CLRS.Common.SortSpec` ones.

3. **No complexity bounds.** None of the three variants track a ghost
   counter or prove O(n+k) complexity. The linear-time property of
   counting sort is not formally verified.

4. ~~**`len > 0` precondition.** All variants require non-empty input.~~
   **RESOLVED.** All three variants now accept empty arrays (`len = 0`).
   Empty arrays are trivially sorted and permutations of themselves.
   Each function returns early when `len = 0`, using `empty_sorted_perm`
   or `empty_is_stable_on_digit` helper lemmas.

5. **`SZ.fits` constraints.** The `SZ.fits (SZ.v len + SZ.v k_val + 2)`
   constraint limits the combined size of input and value range.

6. **`counting_sort_inplace` is NOT stable.** The 2-phase in-place
   variant writes values in ascending order, destroying the original
   relative ordering. It cannot be used as a subroutine for radix sort.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Time | O(n + k) expected | ❌ Not proven | N/A |

No ghost counter is threaded through the implementation. The O(n + k)
complexity is inherent in the algorithm's structure (four O(n)- or
O(k)-bounded loops) but is not formally stated or verified.

## Proof Structure

**`counting_sort_impl`** (4-phase CLRS-faithful):
1. **Phase 1**: Allocate count array `C[0..k]`, initialized to 0.
2. **Phase 2**: Count occurrences. Invariant:
   `counts_match_prefix sc sa k j` — `C[v]` equals the count of `v`
   in `sa[0..j)`.
3. **Phase 3**: Prefix sum. Invariant:
   `prefix_sum_inv sc sa k i` — `C[v]` equals the cumulative count
   of elements ≤ `v`.
4. **Phase 4**: Backwards placement. Invariant:
   `phase4_c_inv` (count tracking) and `phase4_b_inv` (output tracking).
   Final lemmas: `phase4_final_sorted` and `phase4_final_perm`.

**`counting_sort_inplace`** (2-phase):
1. **Phase 1**: Count occurrences (same as above).
2. **Phase 2**: Write-back. Outer loop over values 0..k, inner loop
   writes `count[v]` copies of `v`. Invariant: `phase2_inv` tracks
   sorted prefix and count correctness. Final: `final_perm`.

**`counting_sort_by_digit`** (4-phase digit-keyed):
Same structure as `counting_sort_impl`, but keys on
`digit(a[j], d, base)` instead of `a[j]`. Additional invariants
(`phase4_content_inv`) track element identity (not just digit value)
for the stability proof.

## Files

| File | Role |
|------|------|
| `CLRS.Ch08.CountingSort.Impl.fsti` | Public interface (three signatures) |
| `CLRS.Ch08.CountingSort.Impl.fst` | Pulse implementation |
| `CLRS.Ch08.CountingSort.Spec.fst` | `sorted`, `permutation`, `in_range` definitions |
| `CLRS.Ch08.CountingSort.Lemmas.fsti` | Counting/permutation lemma definitions and signatures |
| `CLRS.Ch08.CountingSort.Lemmas.fst` | Counting/permutation lemma proofs |
| `CLRS.Ch08.CountingSort.StableLemmas.fst` | Phase 3/4 invariant lemmas for stable variant |
| `CLRS.Ch08.CountingSort.DigitSortLemmas.fst` | Phase invariant lemmas for digit-keyed variant |
| `CLRS.Ch08.RadixSort.Stability.fst` | `is_stable_sort_on_digit` definition |
| `CLRS.Ch08.RadixSort.Base.fst` | `digit`, `sorted_on_digit` definitions |

## Rubric Compliance (per `autoclrs/audit/RUBRIC.md`)

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `CountingSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `CountingSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `CountingSort.Lemmas.fsti` | ✅ |
| `Impl.fst` | `CountingSort.Impl.fst` | ✅ |
| `Impl.fsti` | `CountingSort.Impl.fsti` | ✅ |
| `Complexity.fst` | — | ❌ Not present |
| `Complexity.fsti` | — | ❌ Not present |

## Profiling (Build from clean, -j4, wall-clock completion times)

| File | Completion (s) | Max z3rlimit | z3refresh | split_queries |
|------|---------------:|:------------:|:---------:|:-------------:|
| Spec.fst | 0 | — | — | — |
| Lemmas.fsti | 2 | — | — | — |
| Lemmas.fst | 195 | 100 | 0 | 0 |
| StableLemmas.fst | 303 | 400 | 0 | 2 |
| DigitSortLemmas.fst | 422 | 200 | 19 | 10 |
| Impl.fsti | 201 | — | — | — |
| **Impl.fst** | **1681** | **400** | **0** | **1** |

**Critical path bottleneck**: `Impl.fst` is the slowest file (~21 min
solo verification). The z3rlimit 800 in `counting_sort_inplace` is the
highest in the chapter and a stability risk.

## Spec Validation (ImplTest)

Spec validation tests in `CLRS.Ch08.CountingSort.ImplTest.fst` verify
the `Impl.fsti` API for `counting_sort_inplace` and `counting_sort_impl`.

**Results**: Both tests pass with **zero admits, zero assumes**.

- **Preconditions**: Satisfiable for concrete inputs (`[3;1;2]`).
  No overly-strong preconditions found.
- **Postconditions**: Fully precise — `sorted ∧ permutation` uniquely
  determines the output for the tested input.
- **Minor issue**: Permutation argument order is inconsistent between
  `counting_sort_impl` (`S.permutation sb' sa`, output→input) and
  `counting_sort_inplace` (`S.permutation s0 s`, input→output). This
  is semantically equivalent but stylistically inconsistent.
- **`counting_sort_by_digit`**: Not tested (requires opaque stability
  lemma work); exercised via radix sort.

See `CLRS.Ch08.CountingSort.ImplTest.md` for detailed analysis.

## Checklist

Priority-ordered items for reaching a fully proven, high-quality
implementation:

- [x] Zero admits, zero assumes across all files
- [x] Rubric slots: Spec.fst, Lemmas.fst, Lemmas.fsti, Impl.fst, Impl.fsti
- [x] Three variants proven: CLRS-faithful, in-place, digit-keyed
- [x] Empty-array support (`len = 0`) for all three variants
- [x] **P1 (Stabilization)**: Reduce z3rlimit 800 in `counting_sort_inplace`
      (line 284 of Impl.fst). ✅ Reduced to 400 with `--split_queries always`
      (removed `--z3refresh` dependency).
- [ ] **P2 (Stabilization)**: Reduce z3refresh count (19) in
      DigitSortLemmas.fst — indicates solver-state sensitivity.
- [ ] **P3 (Stabilization)**: Reduce z3rlimit 400 in StableLemmas.fst
      (line 328).
- [ ] **P4 (Rubric)**: Add `Complexity.fst`/`.fsti` with O(n+k)
      complexity proof or ghost counter.
- [ ] **P5 (Warning)**: Address deprecated `Array.free`/`Reference.free`
      warnings in Impl.fst (use non-deprecated alternatives when
      available in Pulse).
- [ ] **P6 (Spec)**: Generalize from `nat` to `int` (or parameterize
      over ordered types) to align with `CLRS.Common.SortSpec`.
