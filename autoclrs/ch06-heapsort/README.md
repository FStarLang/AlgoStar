# CLRS Chapter 6: Heapsort

Verified implementation of the heapsort algorithm from CLRS Chapter 6, including
MAX-HEAPIFY (§6.2), BUILD-MAX-HEAP (§6.3), and the full HEAPSORT (§6.4). The
implementation is in Pulse with separate pure complexity analysis modules. All
proofs are mechanically checked by F\* and Pulse. **ZERO admits. ZERO assumes.**

## Algorithms

### 1. MAX-HEAPIFY (CLRS §6.2)

**Specification.** The pure Spec module defines max-heap predicates over
0-based array-indexed binary heaps:

```fstar
let parent_idx (i:nat{i > 0}) : nat = (i - 1) / 2
let left_idx (i:nat) : nat = 2 * i + 1
let right_idx (i:nat) : nat = 2 * i + 2

let heap_down_at (s:Seq.seq int) (len:nat) (i:nat{i < len /\ len <= Seq.length s}) : prop =
  (left_idx i < len ==> Seq.index s i >= Seq.index s (left_idx i)) /\
  (right_idx i < len ==> Seq.index s i >= Seq.index s (right_idx i))

let is_max_heap (s:Seq.seq int) (len:nat{len <= Seq.length s}) : prop =
  forall (i:nat). i < len ==> heap_down_at s len i

let almost_heaps_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (bad:nat{bad < len}) : prop =
  bad >= k /\
  (forall (j:nat). k <= j /\ j < len /\ j <> bad ==> heap_down_at s len j)
```

**Correctness Theorem.** The exact `Impl.fsti` signature:

```pulse
fn max_heapify
  (a: A.array int) (idx: SZ.t) (heap_size: SZ.t) (start: Ghost.erased nat)
  (ctr: GR.ref nat)
  (#s: erased (Seq.seq int) { ... })
  (#c0: erased nat)
requires
  A.pts_to a s **
  GR.pts_to ctr c0 **
  pure (
    SZ.v idx >= start /\
    almost_heaps_from s (SZ.v heap_size) start (SZ.v idx) /\
    (SZ.v idx > 0 /\ parent_idx (SZ.v idx) >= start ==>
      (left_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (left_idx (SZ.v idx))) /\
      (right_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (right_idx (SZ.v idx)))))
ensures exists* s' (cf: nat).
  A.pts_to a s' **
  GR.pts_to ctr cf **
  pure (
    Seq.length s' == Seq.length s /\
    heaps_from s' (SZ.v heap_size) start /\
    permutation s s' /\
    (forall (k:nat). SZ.v heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.max_heapify_bound (SZ.v heap_size) (SZ.v idx))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `Seq.length s' == Seq.length s` | Array size preserved |
| `heaps_from s' heap_size start` | Heap property restored from `start` onward |
| `permutation s s'` | Result is a permutation of input |
| Elements outside heap unchanged | Sorted suffix (for heapsort) is preserved |
| `cf - c0 <= max_heapify_bound heap_size idx` | Cost bounded by 2·⌊log₂(heap_size/(idx+1))⌋ |

**Strongest Guarantee.** The postcondition fully restores the heap property
(not just at `idx`, but from `start` onward). Permutation preservation is
essential for the heapsort correctness chain.

**Limitations.** The `start` ghost parameter is an artifact of the proof
technique — it is not in CLRS. The `SZ.fits(2 * Seq.length s + 2)` precondition
is needed to prevent SizeT overflow in child index computation. The cost bound
is per-call and counts 2 comparisons per non-leaf level; for a leaf node, 0
ticks are consumed.

**Complexity.** O(lg n) per call. The cost bound `max_heapify_bound(heap_size, idx) =
2 * log2_floor(heap_size / (idx+1))` is linked to the ghost counter.

### 2. BUILD-MAX-HEAP (CLRS §6.3)

**Correctness Theorem.** The exact `Impl.fsti` signature:

```pulse
fn build_max_heap
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) { ... })
  (#c0: erased nat)
requires
  A.pts_to a s0 ** GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    SZ.v n <= Seq.length s /\
    is_max_heap s (SZ.v n) /\
    permutation s0 s /\
    SZ.fits (op_Multiply 2 (Seq.length s) + 2) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.build_cost_bound (SZ.v n))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `is_max_heap s n` | Output is a valid max-heap over prefix of length n |
| `permutation s0 s` | Output is a permutation of input |
| `cf - c0 <= build_cost_bound n` | Cost bounded by (n/2) × max\_heapify\_bound(n, 0) |

**Strongest Guarantee.** A full max-heap is established. The permutation
guarantee chains through all max\_heapify calls.

**Limitations.** The `build_cost_bound` is `(n/2) * max_heapify_bound(n, 0)` =
`(n/2) * 2 * log2_floor(n)` = `n * log2_floor(n)`. This is O(n log n), NOT the
tight O(n) bound from CLRS Theorem 6.3. The O(n) analysis (sum over heights
with ceiling-division nodes counts) is proven separately in the Complexity module
(`build_heap_ops_linear: build_heap_ops n <= 4n`), but the ghost counter in the
Impl uses the simpler per-node bound at the root level. The tight O(n) result
is proven for the pure cost model but not linked to the ghost counter.

**Complexity.** The linked bound is O(n log n) via `build_cost_bound`. The pure
Complexity module independently proves the O(n) bound (`build_heap_ops_linear`).

### 3. HEAPSORT (CLRS §6.4)

**Correctness Theorem.** The exact `Impl.fsti` signature:

```pulse
fn heapsort
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) { ... })
  (#c0: erased nat)
requires
  A.pts_to a s0 ** GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.heapsort_cost_bound (SZ.v n))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `sorted s` | Output is sorted (∀ i ≤ j. s[i] ≤ s[j]) |
| `permutation s0 s` | Output is a permutation of input |
| `cf - c0 <= heapsort_cost_bound n` | Cost bounded by build\_cost\_bound(n) + extract\_cost\_bound(n) |

**Strongest Guarantee.** Full functional correctness: sorted + permutation. The
cost bound `heapsort_cost_bound(n) = build_cost_bound(n) + extract_cost_bound(n)`
is linked to the ghost counter.

**Limitations.** The linked cost bound expands to
`(n/2 + n-1) * max_heapify_bound(n, 0)`. The `CostBound` module proves
`heapsort_cost_nlogn`: `heapsort_cost_bound n <= 4 * n * log2_floor n`, which
is O(n log n). The separate Complexity module proves tighter bounds:
- `heapsort_ops_simplified`: `heapsort_ops n <= 6n(1 + log2_floor n)`
- `heapsort_better_than_quadratic`: for n ≥ 11, `heapsort_ops n < n²`

However, the pure `heapsort_ops` cost model and the linked `heapsort_cost_bound`
are different quantities — the former sums exact per-height costs, the latter
upper-bounds each call at the root height. The linked bound is looser.

**Complexity.** O(n log n) proven via the linked ghost counter. The pure
Complexity module additionally proves:
- BUILD-MAX-HEAP is O(n): `build_heap_ops n <= 4n`
- HEAPSORT is O(n log n): `heapsort_ops n <= 6n(1 + log₂ n)`
- Beats quadratic for n ≥ 11: `heapsort_ops n < n²`

## File Inventory

| File | Role | Language |
|------|------|---------|
| `CLRS.Ch06.Heap.Spec.fst` | Pure spec: heap indices, `is_max_heap`, `almost_heaps_from`, `sorted`, `permutation`, `swap_seq` | F\* |
| `CLRS.Ch06.Heap.Lemmas.fsti` | Lemma interface: sift-down lemmas, swap properties, permutation helpers | F\* |
| `CLRS.Ch06.Heap.Lemmas.fst` | Lemma proofs | F\* |
| `CLRS.Ch06.Heap.Complexity.fsti` | Pure complexity interface: `build_heap_ops`, `heapsort_ops`, O(n)/O(n log n) bounds | F\* |
| `CLRS.Ch06.Heap.Complexity.fst` | Complexity proofs: geometric series for O(n) build, O(n log n) total, beats quadratic | F\* |
| `CLRS.Ch06.Heap.CostBound.fsti` | Ghost-counter cost bounds: `max_heapify_bound`, `build_cost_bound`, `heapsort_cost_bound` | F\* |
| `CLRS.Ch06.Heap.CostBound.fst` | Cost bound proofs: monotonicity, left/right child bounds, O(n log n) linked | F\* |
| `CLRS.Ch06.Heap.Impl.fsti` | Public interface: `max_heapify`, `build_max_heap`, `heapsort` | Pulse |
| `CLRS.Ch06.Heap.Impl.fst` | Imperative implementation with ghost counters | Pulse |

## Summary

| Algorithm | CLRS Section | Correctness | Linked Complexity | Pure Complexity | Admits |
|-----------|-------------|-------------|-------------------|-----------------|--------|
| MAX-HEAPIFY | §6.2 | Restores heap + permutation | O(lg n): 2·⌊log₂(n/(i+1))⌋ | — | 0 |
| BUILD-MAX-HEAP | §6.3 | `is_max_heap` + permutation | O(n log n) via root bound | O(n): ≤ 4n | 0 |
| HEAPSORT | §6.4 | `sorted` + `permutation` | O(n log n): ≤ 4n·log₂ n | ≤ 6n(1+log₂ n), beats n² for n≥11 | 0 |

## Building

```bash
cd ch06-heapsort && make
```
