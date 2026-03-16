# Partition (CLRS §7.1)

## Top-Level Signature

Here is the top-level signature proven about the Lomuto partition in
`CLRS.Ch07.Partition.Impl.fsti`:

```fstar
fn clrs_partition_wrapper_with_ticks
  (a: A.array int)
  (lo: nat)
  (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires (
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat
  ensures exists* s1 s_pivot s2 (cf: nat). (
    A.pts_to_range a lo   p     s1 **
    A.pts_to_range a p    (p+1) s_pivot **
    A.pts_to_range a (p+1) hi   s2 **
    GR.pts_to ctr cf **
    pure (
      lo <= p /\ p < hi /\ hi <= A.length a /\
      Seq.length s1 == p - lo /\ Seq.length s_pivot == 1 /\ Seq.length s2 == hi - (p+1) /\
      lb <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= rb /\
      between_bounds s1 lb (Seq.index s_pivot 0) /\
      between_bounds s2 (Seq.index s_pivot 0) rb /\
      strictly_larger_than s2 (Seq.index s_pivot 0) /\
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
   ))
```

### Parameters

* `a` is a mutable array of `int`. The ghost variable `s0` captures
  the initial contents of the sub-array `a[lo..hi)`.

* `lo`, `hi` are the (inclusive, exclusive) bounds of the sub-array to
  partition. `lo < hi` is required.

* `lb`, `rb` are **ghost** lower and upper bounds on the values in
  `s0`. They enable the quicksort caller to maintain value-range
  invariants across recursive calls.

* `ctr` is a **ghost counter** for comparison counting. The initial
  value is `c0`.

### Preconditions

* `hi <= A.length a` — the sub-range fits within the physical array.

* `Seq.length s0 = hi - lo` — the ghost sequence matches the range
  length.

* `between_bounds s0 lb rb` — every element in the sub-array is in
  `[lb, rb]`.

**Note:** This function uses `pts_to_range` (sub-array ownership),
not `pts_to` (whole-array ownership). This enables quicksort to split
ownership of the array across recursive calls without copying.

### Postcondition

The partition returns an index `p` and splits ownership of `a[lo..hi)`
into three disjoint ranges:

* `A.pts_to_range a lo p s1` — the left partition.
* `A.pts_to_range a p (p+1) s_pivot` — the pivot (a singleton
  sequence).
* `A.pts_to_range a (p+1) hi s2` — the right partition.

The pure postconditions state:

* `lo <= p /\ p < hi` — the pivot index is within the range.

* `lb <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= rb` — the
  pivot value is within the caller's bounds.

* `between_bounds s1 lb (Seq.index s_pivot 0)` — all left elements
  are ≤ pivot.

* `between_bounds s2 (Seq.index s_pivot 0) rb` — all right elements
  are ≥ pivot.

* `strictly_larger_than s2 (Seq.index s_pivot 0)` — all right elements
  are **strictly greater** than the pivot (the Lomuto guarantee).

* `permutation s0 (Seq.append s1 (Seq.append s_pivot s2))` — the
  concatenation of the three regions is a permutation of the input.

* `complexity_exact_linear cf (reveal c0) (hi - lo - 1)` — exactly
  `n-1` comparisons are performed.

## Auxiliary Definitions

### `between_bounds` (from `CLRS.Ch07.Partition.Lemmas`)

```fstar
let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let strictly_larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb < Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb
```

Every element in `s` lies in the closed interval `[lb, rb]`.
`strictly_larger_than s lb` gives the strict lower bound `lb < s[k]`.

### `complexity_exact_linear` (from `CLRS.Ch07.Partition.Lemmas`)

```fstar
let complexity_exact_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n
```

The counter increased by **exactly** `n`. For partition on `n`
elements, `n = hi - lo - 1` (all elements except the pivot are
compared once).

### `permutation` (from `CLRS.Common.SortSpec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

Standard library permutation, opaque to SMT.

## What Is Proven

1. **Partition correctness**: The output is split into three regions
   where all left elements are ≤ pivot, all right elements are ≥ pivot,
   and the concatenation is a permutation of the input. This is the
   exact specification needed for quicksort.

2. **Exact comparison count**: The Lomuto partition performs **exactly**
   `n-1` comparisons on an `n`-element sub-array. This is captured by
   `complexity_exact_linear` — not just an upper bound, but an exact
   count.

3. **Ownership splitting**: The postcondition splits `pts_to_range` into
   three disjoint regions, enabling the caller (quicksort) to recurse
   on sub-partitions without ownership conflicts.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`between_bounds` for the right partition uses ≥, not >.**~~ **FIXED.**
   The wrapper now exposes `strictly_larger_than s2 (Seq.index s_pivot 0)`
   in addition to `between_bounds`, propagating the strict inequality
   proven internally by `clrs_partition_with_ticks`.

2. **Ghost bounds `lb` and `rb` must be provided by the caller.** The
   partition itself does not compute bounds; it requires them as ghost
   parameters. The quicksort caller derives them from `seq_min` /
   `seq_max`.

3. **Not randomized.** CLRS §7.3 discusses randomized partition (random
   pivot selection). This implementation always uses the last element
   as pivot, giving worst-case O(n) per call but O(n²) for quicksort.

4. **No stability guarantee.** Lomuto partition is not stable; equal
   elements may be reordered.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | Θ(n-1) = n-1 exactly | ✅ Ghost counter | ✅ Exact |

The complexity is **fully linked** to the Pulse implementation: the
ghost counter `ctr` is incremented once per loop iteration, and the
loop runs exactly `hi - lo - 1` times (comparing each non-pivot
element to the pivot).

## Profiling (2026-03-16)

Verification times (sequential, `--z3rlimit 5`):

| File | Time (ms) | Notes |
|------|----------:|-------|
| `Partition.Impl.fst` | 7038 | Heaviest — loop invariant + wrapper |
| `Partition.Lemmas.fst` | 2454 | Swap/bounds lemmas |
| `Partition.Impl.fsti` | 1672 | Pulse interface |
| `Partition.Lemmas.fsti` | 747 | Definitions + signatures |
| `Partition.Complexity.fst` | 582 | Trivial proof |
| `Partition.Complexity.fsti` | 576 | Interface |

**Stability:** All files verify at `--z3rlimit 5` (minimum). No
`#push-options`, no `--retry`, no `--z3rlimit_factor` needed. Proofs
are fully stable.

## Proof Structure

The internal `clrs_partition_with_ticks` maintains a loop invariant
tracking:
* `clrs_partition_pred s lo j i_plus_1 pivot` — elements before
  `i_plus_1` are ≤ pivot, elements between `i_plus_1` and `j` are
  > pivot.
* `permutation s0 s` — the current array is a permutation.
* `vc == reveal c0 + (j - lo)` — exact tick count.

After the loop, a final swap places the pivot at position `i_plus_1`.
The wrapper `clrs_partition_wrapper_with_ticks` then splits ownership
via `pts_to_range_split` and transfers bounds to the sub-regions.

## Checklist

Priority order of work items:

- [x] Partition correctness (permutation + split) — **Done**
- [x] Exact complexity (n-1 comparisons) — **Done**
- [x] Ownership splitting (3-region pts_to_range) — **Done**
- [x] strictly_larger_than for right partition — **Done**
- [x] Zero admits, zero assumes — **Done**
- [x] Proof stability (verifies at --z3rlimit 5) — **Done**
- [x] No #push-options or --retry needed — **Done**
- [ ] Reduce Partition.Impl.fst verification time (7s) — *Low priority, not blocking*
- [ ] Randomized partition (CLRS §7.3) — *Deferred*

## Files

| File | Role |
|------|------|
| `CLRS.Ch07.Partition.Impl.fsti` | Public interface (partition wrapper) |
| `CLRS.Ch07.Partition.Impl.fst` | Pulse implementation (inner + wrapper) |
| `CLRS.Ch07.Partition.Lemmas.fsti` | Definitions (`between_bounds`, `complexity_exact_linear`) and lemma signatures |
| `CLRS.Ch07.Partition.Lemmas.fst` | Lemma proofs (swap, bounds transfer) |
| `CLRS.Ch07.Partition.Complexity.fsti` | Complexity signature |
| `CLRS.Ch07.Partition.Complexity.fst` | Complexity proof (trivial — exact count) |
| `CLRS.Common.SortSpec.fst` | `permutation` definition |
