# Quicksort (CLRS §7.1–7.2)

## Top-Level Signatures

Here are the three function signatures proven about Quicksort in
`CLRS.Ch07.Quicksort.Impl.fsti`:

### `quicksort`

```fstar
fn quicksort
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
```

### `quicksort_with_complexity`

```fstar
fn quicksort_with_complexity
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s (cf: nat). (
    A.pts_to a s ** GR.pts_to ctr cf **
    pure (sorted s /\ permutation s0 s /\
          complexity_bounded_quadratic cf (reveal c0) (SZ.v len)))
```

### `quicksort_bounded`

```fstar
fn quicksort_bounded
  (a: A.array int)
  (lo: nat)
  (hi: (hi:nat{lo <= hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (
    hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    between_bounds s0 lb rb /\
    lb <= rb
  )
  ensures exists* s. (
    A.pts_to_range a lo hi s **
    pure (sorted s /\ permutation s0 s)
  )
```

### Parameters

* `a` is a mutable array of `int`. The ghost variable `s0` captures
  the initial contents.

* `len` is the number of elements, of type `SZ.t`.

* `ctr` is a **ghost counter** for comparison counting (only in
  `quicksort_with_complexity`).

* `lo`, `hi` define a sub-range `a[lo..hi)` (only in
  `quicksort_bounded`).

* `lb`, `rb` are **ghost** value bounds (only in `quicksort_bounded`).

### Preconditions

* `Seq.length s0 == A.length a /\ A.length a == SZ.v len` — consistency.
  No minimum length is required; empty arrays are accepted.

* For `quicksort_bounded`: `between_bounds s0 lb rb /\ lb <= rb` —
  all elements within provided value bounds.

### Postcondition

* **`quicksort`**: `sorted s /\ permutation s0 s` — the output is a
  sorted permutation of the input. No complexity information exposed.

* **`quicksort_with_complexity`**: Additionally proves
  `complexity_bounded_quadratic cf (reveal c0) (SZ.v len)` — the
  worst-case O(n²) bound.

* **`quicksort_bounded`**: `sorted s /\ permutation s0 s` on the
  sub-range `a[lo..hi)`. Uses `pts_to_range` for sub-array ownership.

## Auxiliary Definitions

### `sorted` (from `CLRS.Common.SortSpec`)

```fstar
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

All-pairs sorted definition.

### `permutation` (from `CLRS.Common.SortSpec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

Standard permutation, opaque to SMT.

### `complexity_bounded_quadratic` (from `CLRS.Ch07.Quicksort.Lemmas`)

```fstar
let complexity_bounded_quadratic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= op_Multiply n (n - 1) / 2
```

The number of comparisons `cf - c0` is at most `n(n-1)/2`. This is
the **worst-case** bound for quicksort (CLRS §7.2), which occurs when
the partition is maximally unbalanced (one side empty, the other has
`n-1` elements) at every recursive call.

### `between_bounds` (from `CLRS.Ch07.Partition.Lemmas`)

```fstar
let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb
```

All elements lie in `[lb, rb]`.

### `worst_case_comparisons` (from `CLRS.Ch07.Quicksort.Complexity`)

```fstar
let rec worst_case_comparisons (n: nat) : nat =
  if n <= 1 then 0
  else n - 1 + worst_case_comparisons (n - 1)
```

The recurrence `T(n) = T(n-1) + (n-1)` which solves to `n(n-1)/2`.

## What Is Proven

1. **Functional correctness** (`quicksort`, `quicksort_with_complexity`,
   `quicksort_bounded`): The output is sorted and is a permutation of
   the input. This is the strongest possible specification for a
   sorting algorithm.

2. **Worst-case O(n²)** (`quicksort_with_complexity`): The number of
   comparisons is at most `n(n-1)/2`, proven via ghost counter
   threading through all recursive calls.

3. **Recursive complexity bound** (`lemma_quicksort_complexity_bound`):
   For any partition split `n = n_left + 1 + n_right`, the total cost
   `(n-1) + n_left(n_left-1)/2 + n_right(n_right-1)/2 ≤ n(n-1)/2`.

4. **Standalone complexity analysis** (`Quicksort.Complexity`):
   * `worst_case_bound`: `2·T(n) = n(n-1)` (exact closed form)
   * `partition_split_bounded`: convexity — any split is bounded by
     worst case
   * `worst_case_monotonic`: `T` is monotone increasing

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Only worst-case O(n²) proven, NOT average-case O(n lg n).** CLRS
   §7.4 proves that the expected running time of randomized quicksort
   is O(n lg n). This implementation does not use randomization, and
   the proof only establishes the worst-case `n(n-1)/2` bound. The
   average-case analysis would require probabilistic reasoning not
   present in this framework.

2. ~~**`len > 0` precondition for top-level variants.**~~ **FIXED.**
   `quicksort` and `quicksort_with_complexity` now accept `len >= 0`
   (including empty arrays). The `else` branch handles `len = 0` and
   `len = 1` as trivial base cases (empty/singleton arrays are sorted
   and are permutations of themselves).

3. **Ghost bounds derived from `seq_min`/`seq_max`.** The top-level
   `quicksort` function internally computes `seq_min s0` and
   `seq_max s0` as ghost bounds, which requires `len > 1` (the
   `if` branch). This is purely a specification mechanism with no
   runtime cost.

4. **Lomuto partition (not Hoare).** The implementation uses Lomuto
   partition (last element as pivot), which has worse constant factors
   than Hoare partition. The specification does not distinguish between
   partition strategies.

5. **No tail-call optimization proven.** CLRS §7.4 discusses
   tail-recursive quicksort. This implementation uses standard
   recursion without proving stack depth bounds.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons (quicksort) | O(n²) = n(n-1)/2 | ✅ Ghost counter | Upper bound only |
| Comparisons (partition) | Θ(n-1) exactly | ✅ Ghost counter | ✅ Exact |
| Worst-case (pure model) | n(n-1)/2 = T(n-1)+(n-1) | ❌ Pure only | ✅ Exact recurrence |

The ghost counter is threaded through `partition →
quicksort(left) → quicksort(right)` in a single call chain. The
partition contributes exactly `n-1` ticks, and the recursive calls
are bounded by `n_left(n_left-1)/2` and `n_right(n_right-1)/2`
respectively.

## Profiling (2026-03-16)

Verification times (sequential, `--z3rlimit 5`):

| File | Time (ms) | Notes |
|------|----------:|-------|
| `Quicksort.Impl.fst` | 5354 | Recursive quicksort + top-level API |
| `Quicksort.Lemmas.fst` | 1325 | sorted_append + permutation composition |
| `Quicksort.Impl.fsti` | 1478 | Pulse interface |
| `Quicksort.Lemmas.fsti` | 705 | Definitions + signatures |
| `Quicksort.Complexity.fst` | 524 | Recurrence + convexity |
| `Quicksort.Complexity.fsti` | 324 | Interface |

**Full chapter build:** ~23s sequential (all 12 source files + SortSpec).

**Stability:** All files verify at `--z3rlimit 5` (minimum). No
`#push-options`, no `--retry`, no `--z3rlimit_factor` needed. Proofs
are fully stable.

## Proof Structure

**`clrs_quicksort_with_ticks`** (internal recursive function):
1. If `lo < hi`, call `clrs_partition_wrapper_with_ticks` to split
   `a[lo..hi)` into three owned ranges.
2. Recurse on left `a[lo..p)` and right `a[p+1..hi)`.
3. Reassemble ownership via `quicksort_proof` (a ghost function that
   joins the three `pts_to_range` regions and proves sorted +
   permutation using `lemma_sorted_append`).
4. Prove complexity via `lemma_quicksort_complexity_bound`.

**`quicksort`**: Creates a ghost counter, derives `seq_min`/`seq_max`
bounds, converts `pts_to` to `pts_to_range`, calls the internal
version, and converts back.

Key lemmas in `CLRS.Ch07.Quicksort.Lemmas`:
* `lemma_sorted_append`: combining two sorted sequences with
  `between_bounds` constraints yields a sorted concatenation.
* `append_permutations_3`: 3-way permutation composition.
* `lemma_quicksort_complexity_bound`: the convexity argument for
  recursive cost.

## Checklist

Priority order of work items:

- [x] Quicksort correctness (sorted + permutation) — **Done**
- [x] Worst-case O(n²) complexity bound with ghost counter — **Done**
- [x] Standalone complexity module (recurrence, closed form, convexity, monotonicity) — **Done**
- [x] Three top-level API variants (quicksort, with_complexity, bounded) — **Done**
- [x] Empty/singleton array handling (len >= 0 accepted) — **Done**
- [x] Zero admits, zero assumes — **Done**
- [x] Proof stability (verifies at --z3rlimit 5) — **Done**
- [x] No #push-options or --retry needed — **Done**
- [x] Imports from CLRS.Common.SortSpec (no definition duplication) — **Done**
- [ ] Reduce Quicksort.Impl.fst verification time (5.4s) — *Low priority, not blocking*
- [ ] Randomized quicksort (CLRS §7.3) — *Deferred*
- [ ] Expected O(n lg n) analysis (CLRS §7.4.2, Theorem 7.4) — *Deferred*
- [ ] Tail-recursive quicksort / stack depth bounds — *Deferred*

## Files

| File | Role |
|------|------|
| `CLRS.Ch07.Quicksort.Impl.fsti` | Public interface (three signatures) |
| `CLRS.Ch07.Quicksort.Impl.fst` | Pulse implementation |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | Definitions (`complexity_bounded_quadratic`, `seq_min`, `seq_max`) and lemma signatures |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | Standalone complexity signatures |
| `CLRS.Ch07.Quicksort.Complexity.fst` | Standalone complexity proofs |
| `CLRS.Ch07.Partition.Impl.fsti` | Partition interface |
| `CLRS.Ch07.Partition.Impl.fst` | Partition implementation |
| `CLRS.Ch07.Partition.Lemmas.fsti` | Partition definitions and lemmas |
| `CLRS.Common.SortSpec.fst` | `sorted`, `permutation` |
