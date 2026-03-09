# Order Statistics (CLRS Chapter 9)

This directory contains formally verified implementations of order-statistic
algorithms from CLRS Chapter 9: **Minimum/Maximum** (§9.1), **Simultaneous
Min-Max** (§9.1), **Quickselect** (§9.2), and **Partial Selection Sort**.

**All proofs are complete with zero admits, zero assumes, and zero assume_ calls.**

## Summary Table

| Algorithm | CLRS | Postcondition | Complexity (proven) | Admits |
|-----------|------|---------------|---------------------|--------|
| `find_minimum` | §9.1 | `∃k. s[k]==result ∧ ∀k. result ≤ s[k]` | Exact n−1 comparisons | 0 |
| `find_maximum` | §9.1 | `∃k. s[k]==result ∧ ∀k. result ≥ s[k]` | Exact n−1 comparisons | 0 |
| `find_minmax` | §9.1 | min∧max correctness | Exact 2(n−1) comparisons | 0 |
| `find_minmax_pairs` | §9.1 | min∧max correctness | ≤ ⌊3n/2⌋ comparisons | 0 |
| `partition_in_range` | §9.2 | `permutation ∧ partition_ordered` | Exact hi−lo−1 comparisons | 0 |
| `quickselect` | §9.2 | `permutation ∧ result==select_spec` | O(n²) worst-case | 0 |
| `select` | — | `permutation ∧ sorted_prefix ∧ prefix_leq_suffix` | O(nk) | 0 |

## Minimum / Maximum (CLRS §9.1)

### Specification

Complexity bounds are defined in `MinMax.Spec`:

```fstar
let complexity_bounded_min (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

let complexity_bounded_max (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1
```

Both are **exact**: the cost is `n − 1`, not "at most n − 1".

### Correctness Theorem: `find_minimum`

```fstar
fn find_minimum (#p: perm) (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
  pure (SZ.v len == Seq.length s0 /\ SZ.v len > 0 /\ SZ.v len == A.length a)
returns min_val: int
ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
  pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k) /\
    complexity_bounded_min cf (reveal c0) (SZ.v len)
  )
```

**Postcondition conjuncts:**
1. **Existence**: `∃k. s0[k] == min_val` — the result actually appears in the array
2. **Universality**: `∀k. min_val ≤ s0[k]` — the result is ≤ every element
3. **Complexity**: `cf - c0 == n - 1` — exactly n−1 comparisons

**Strongest guarantee?** Yes. Existence + universality uniquely characterize the
minimum. The complexity bound is exact (not just O(n)), matching the information-
theoretic lower bound of n−1 comparisons.

**`find_maximum`** is symmetric: replaces `<=` with `>=`.

### Limitations

- Array is read-only (`#p` permission returned unchanged), which is correct but
  means the function cannot reorder elements.

## Simultaneous Min-Max (CLRS §9.1)

### Specification

Two complexity bounds are defined in `SimultaneousMinMax.Spec`:

```fstar
/// Simple scan: exactly 2(n-1) comparisons
let complexity_bounded_minmax (cf c0 n: nat) : prop =
  n >= 1 /\ cf >= c0 /\ cf - c0 == op_Multiply 2 (n - 1)

/// Pair-processing: at most ⌊3n/2⌋ comparisons
let complexity_bounded_minmax_pairs (cf c0 n: nat) : prop =
  n >= 1 /\ cf >= c0 /\ op_Multiply 2 (cf - c0) <= op_Multiply 3 n
```

### Correctness Theorem: `find_minmax`

The naïve approach scans once maintaining both min and max:

```fstar
fn find_minmax (#p: perm) (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
  pure (SZ.v len == Seq.length s0 /\ SZ.v len >= 1 /\ SZ.v len == A.length a)
returns result: minmax_result
ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
  pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
    complexity_bounded_minmax cf (reveal c0) (SZ.v len)
  )
```

**Postcondition**: Four conjuncts for min (existence + universality) and max
(existence + universality), plus exact 2(n−1) comparison count.

### Correctness Theorem: `find_minmax_pairs`

The CLRS-optimal pair-processing variant:

```fstar
fn find_minmax_pairs (#p: perm) (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
  ensures ... complexity_bounded_minmax_pairs cf (reveal c0) (SZ.v len) ...
```

Same four correctness conjuncts, but with `⌊3n/2⌋` comparisons instead of
`2(n−1)`. The bound is expressed without integer division:
`2 * (cf - c0) <= 3 * n`.

### Strongest Guarantee?

Yes. The correctness part (existence + universality for both min and max) is
the strongest possible. The complexity bounds match CLRS's analysis exactly:
- `find_minmax`: 2(n−1) exact
- `find_minmax_pairs`: ⌊3n/2⌋ upper bound (CLRS Theorem 9.1)

### Limitations

- Read-only: array unchanged.
- The `find_minmax_pairs` bound is `2*(cf-c0) <= 3*n`, not the tighter
  `⌊3(n-1)/2⌋`. The proven bound is slightly loose by at most 1 comparison
  for even n.

## Quickselect (CLRS §9.2)

### Specification

Partition predicates from `Quickselect.Spec`:

```fstar
let partition_ordered (s: Seq.seq int) (lo p hi: nat) : prop =
  lo <= p /\ p < hi /\ hi <= Seq.length s /\
  (forall (idx:nat). lo <= idx /\ idx < p ==> Seq.index s idx <= Seq.index s p) /\
  (forall (idx:nat). p < idx /\ idx < hi ==> Seq.index s idx >= Seq.index s p)
```

The reference answer is defined in `PartialSelectionSort.Spec`:

```fstar
let select_spec (s: seq int) (k: nat{k < Seq.length s}) : int =
  pure_sort_length s;
  Seq.index (pure_sort s) k
```

### Correctness Theorem: `partition_in_range`

```fstar
fn partition_in_range (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t) (hi: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns pivot_pos: SZ.t
ensures exists* s1 (cf: nat). A.pts_to a s1 ** GR.pts_to ctr cf **
  pure (
    Seq.length s1 == Seq.length s0 /\
    SZ.v lo <= SZ.v pivot_pos /\ SZ.v pivot_pos < SZ.v hi /\
    permutation s0 s1 /\ partition_ordered s1 (SZ.v lo) (SZ.v pivot_pos) (SZ.v hi) /\
    unchanged_outside s0 s1 (SZ.v lo) (SZ.v hi) /\
    cf - reveal c0 == SZ.v hi - SZ.v lo - 1
  )
```

**Postcondition**: Permutation, partition ordering, elements outside `[lo,hi)`
unchanged, and exactly `hi−lo−1` comparisons.

### Correctness Theorem: `quickselect`

```fstar
fn quickselect (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t) (k: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns result: int
ensures exists* s_final (cf: nat). A.pts_to a s_final ** GR.pts_to ctr cf **
  pure (
    Seq.length s_final == Seq.length s0 /\
    permutation s0 s_final /\
    SZ.v k < Seq.length s_final /\
    result == Seq.index s_final (SZ.v k) /\
    (forall (i:nat). i < SZ.v k ==> Seq.index s_final i <= result) /\
    (forall (i:nat). SZ.v k < i /\ i < Seq.length s_final ==> result <= Seq.index s_final i) /\
    result == PSSSpec.select_spec s0 (SZ.v k) /\
    complexity_bounded_quickselect cf (reveal c0) (SZ.v n)
  )
```

**Postcondition conjuncts:**
1. `permutation s0 s_final` — output is a rearrangement of input
2. `result == Seq.index s_final (SZ.v k)` — result is element at position k
3. `∀i < k. s_final[i] ≤ result` — everything left of k is ≤
4. `∀i > k. result ≤ s_final[i]` — everything right of k is ≥
5. `result == select_spec s0 k` — result equals the k-th element of the sorted sequence
6. `complexity_bounded_quickselect` — O(n²) worst-case bound

**Strongest guarantee?** The functional correctness (`result == select_spec s0 k`)
is the strongest possible — it connects the imperative result to the unique
mathematical answer. The partition property (conjuncts 3-4) is a structural
bonus that follows from the algorithm's nature.

### Complexity

`complexity_bounded_quickselect` is O(n²) worst-case. The complexity module
(`Quickselect.Complexity.fsti`) proves:
- `qs_cost n <= n * (n + 1) / 2` (tight closed form)
- `qs_cost n <= n * n` (simpler quadratic bound)
- `qs_cost_monotone`: cost is monotone in n

### Limitations

- **Only worst-case proven**: Expected O(n) for randomized pivot is **not**
  mechanized. The implementation uses the last element as pivot (deterministic),
  giving Θ(n²) on sorted inputs.
- **No randomization**: Unlike CLRS's `RANDOMIZED-SELECT`, the pivot is not
  random, so the worst case is achievable.

## Partial Selection Sort

### Specification

```fstar
let sorted_prefix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j:nat). i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)

let prefix_leq_suffix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j:nat). i < bound /\ bound <= j /\ j < Seq.length s ==>
    Seq.index s i <= Seq.index s j)
```

### Correctness Theorem: `select`

```fstar
fn select (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t) (k: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  requires ... pure (SZ.v n > 0 /\ SZ.v k > 0 /\ SZ.v k <= SZ.v n)
returns result: int
ensures exists* s_final (cf: nat). A.pts_to a s_final ** GR.pts_to ctr cf **
  pure (
    Seq.length s_final == Seq.length s0 /\
    permutation s0 s_final /\
    sorted_prefix s_final (SZ.v k) /\
    prefix_leq_suffix s_final (SZ.v k) /\
    result == Seq.index s_final (SZ.v k - 1) /\
    complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
  )
```

**Postcondition conjuncts:**
1. `permutation s0 s_final` — output is a rearrangement
2. `sorted_prefix s_final k` — first k elements are sorted
3. `prefix_leq_suffix s_final k` — prefix ≤ suffix (partition cut)
4. `result == s_final[k-1]` — result is the k-th smallest

### Complexity

`complexity_bounded_select` from `PartialSelectionSort.Complexity.fsti`:
- `select_comparisons n k == k * (n - 1)` exact
- Tighter model: `2 * tight(n,k) == k * (2*n - k - 1)`

### Limitations

- **Not a CLRS algorithm**: This is a selection-sort variant, not from the textbook.
- **O(nk) worst-case**: Worse than quickselect's expected O(n) for small k.
- **Note on k**: The parameter `k` here is 1-indexed (k > 0, finds the k-th
  smallest), while quickselect's k is 0-indexed.

## File Inventory

| File | Role | Admits |
|------|------|--------|
| `CLRS.Ch09.MinMax.Spec.fst` | Complexity predicates for min/max | 0 |
| `CLRS.Ch09.MinMax.Impl.fsti` | Interface: `find_minimum`, `find_maximum` | 0 |
| `CLRS.Ch09.MinMax.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch09.MinMax.Lemmas.fsti` | Lemma interface | 0 |
| `CLRS.Ch09.MinMax.Lemmas.fst` | Helper lemmas | 0 |
| `CLRS.Ch09.MinMax.Complexity.fst` | Complexity: exact n−1 | 0 |
| `CLRS.Ch09.MinMax.Complexity.fsti` | Complexity interface | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Spec.fst` | `minmax_result`, complexity predicates | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Impl.fsti` | Interface: `find_minmax`, `find_minmax_pairs` | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Lemmas.fsti` | Lemma interface | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Lemmas.fst` | Helper lemmas | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Complexity.fst` | Complexity: 2(n−1) and ⌊3n/2⌋ | 0 |
| `CLRS.Ch09.SimultaneousMinMax.Complexity.fsti` | Complexity interface | 0 |
| `CLRS.Ch09.Quickselect.Spec.fst` | Partition predicates, swap lemmas | 0 |
| `CLRS.Ch09.Quickselect.Impl.fsti` | Interface: `partition_in_range`, `quickselect` | 0 |
| `CLRS.Ch09.Quickselect.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch09.Quickselect.Lemmas.fsti` | Lemma interface | 0 |
| `CLRS.Ch09.Quickselect.Lemmas.fst` | Helper lemmas | 0 |
| `CLRS.Ch09.Quickselect.Complexity.fst` | qs_cost ≤ n² proofs | 0 |
| `CLRS.Ch09.Quickselect.Complexity.fsti` | Complexity interface | 0 |
| `CLRS.Ch09.PartialSelectionSort.Spec.fst` | `select_spec`, `pure_sort`, counting lemmas | 0 |
| `CLRS.Ch09.PartialSelectionSort.Impl.fsti` | Interface: `find_min_index_from`, `select` | 0 |
| `CLRS.Ch09.PartialSelectionSort.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch09.PartialSelectionSort.Lemmas.fsti` | Lemma interface | 0 |
| `CLRS.Ch09.PartialSelectionSort.Lemmas.fst` | `sorted_permutation_equal` + helpers | 0 |
| `CLRS.Ch09.PartialSelectionSort.Complexity.fsti` | k*(n−1) exact, O(nk) | 0 |
| `CLRS.Ch09.PartialSelectionSort.Complexity.fst` | Complexity proofs | 0 |
| `Makefile` | Build configuration | — |

## Building

```bash
# From the ch09-order-statistics directory:
make

# Or from the project root:
make -C ch09-order-statistics
```

Requires the Pulse toolchain. Set `PULSE_ROOT` if not at `../../pulse`.
