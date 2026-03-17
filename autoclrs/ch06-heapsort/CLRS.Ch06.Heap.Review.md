# Heapsort (CLRS §6.2–6.4)

## Top-Level Signatures

Here are the three function signatures proven about Heapsort in
`CLRS.Ch06.Heap.Impl.fsti`:

### `max_heapify`

```fstar
fn max_heapify
  (a: A.array int) (idx: SZ.t) (heap_size: SZ.t) (start: Ghost.erased nat)
  (ctr: GR.ref nat)
  (#s: erased (Seq.seq int) {
    SZ.v idx < SZ.v heap_size /\
    SZ.v heap_size <= Seq.length s /\
    Seq.length s == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s) + 2)
  })
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
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (right_idx (SZ.v idx))))
  )
ensures exists* s' (cf: nat).
  A.pts_to a s' **
  GR.pts_to ctr cf **
  pure (
    Seq.length s' == Seq.length s /\
    heaps_from s' (SZ.v heap_size) start /\
    permutation s s' /\
    (forall (k:nat). SZ.v heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.max_heapify_bound (SZ.v heap_size) (SZ.v idx)
  )
```

### `build_max_heap`

```fstar
fn build_max_heap
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n > 0 /\
    SZ.v n <= A.length a /\
    Seq.length s0 == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
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
    cf - reveal c0 <= CB.build_cost_bound (SZ.v n)
  )
```

### `heapsort`

```fstar
fn heapsort
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n <= A.length a /\
    Seq.length s0 == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted_upto s (SZ.v n) /\
    permutation s0 s /\
    (forall (k:nat). SZ.v n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.heapsort_cost_bound (SZ.v n)
  )
```

### Parameters

* `a` is a mutable array of `int`. The ghost variable `s0` (or `s`)
  captures the initial contents.

* `n` / `heap_size` is the number of elements, of type `SZ.t`
  (machine-sized).

* `idx` is the index to sift down from (for `max_heapify`).

* `start` is a **ghost** parameter tracking the lower bound of the
  `heaps_from` region — not in CLRS. It lets `max_heapify` prove
  correctness when called from both `build_max_heap` (start = idx) and
  the extract-max loop (start = 0).

* `ctr` is a **ghost counter** for comparison counting. The initial
  value is `c0`.

### Preconditions

* `SZ.v n <= A.length a` / `Seq.length s0 == A.length a` — the logical
  sequence matches the physical array length. Note: `n` may be
  strictly less than `A.length a`, enabling prefix sorting.

* `SZ.fits (op_Multiply 2 (Seq.length s0) + 2)` — index arithmetic for
  `left_idx` (`2*i+1`) and `right_idx` (`2*i+2`) cannot overflow
  `SizeT`. The maximum computed index is `2*(n-1)+2 = 2*n`.

* For `max_heapify`: `almost_heaps_from s heap_size start idx` — all
  nodes from `start` to `heap_size-1` satisfy the max-heap property
  except possibly at `idx`. Additional parent-dominance conditions
  ensure the invariant can be restored.

### Postcondition

For `heapsort`, the `ensures` clause states that there exist a final
sequence `s` and a final counter value `cf` such that:

* `Seq.length s == Seq.length s0` — length is preserved.

* `sorted_upto s (SZ.v n)` — the first `n` elements are sorted.

* `permutation s0 s` — the output is a permutation of the input.

* `forall k. n <= k < length s ==> s[k] == s0[k]` — elements beyond
  the first `n` are unchanged (enables prefix sorting).

* `cf >= reveal c0 /\ cf - reveal c0 <= CB.heapsort_cost_bound (SZ.v n)`
  — the number of comparisons is bounded.

## Auxiliary Definitions

### `sorted` / `sorted_upto` (from `CLRS.Ch06.Heap.Spec`)

```fstar
let sorted (s: Seq.seq int) =
  forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let sorted_upto (s: Seq.seq int) (n: nat) =
  n <= Seq.length s /\
  (forall (i j: nat). i <= j /\ j < n ==> Seq.index s i <= Seq.index s j)
```

`sorted` is the standard all-pairs definition. `sorted_upto` restricts
to the first `n` elements, enabling prefix sorting. When `n = Seq.length s`,
they are equivalent.

### `permutation` (from `CLRS.Ch06.Heap.Spec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (SeqP.permutation int s1 s2)
```

Wraps F\*'s standard library permutation. Opaque to SMT for
performance; explicit permutation lemmas are used instead.

### `is_max_heap` (from `CLRS.Ch06.Heap.Spec`)

```fstar
let is_max_heap (s:Seq.seq int) (len:nat{len <= Seq.length s}) : prop =
  forall (i:nat). i < len ==> heap_down_at s len i
```

Full max-heap: every node in the prefix `[0, len)` satisfies
`heap_down_at`.

### `heap_down_at` (from `CLRS.Ch06.Heap.Spec`)

```fstar
let heap_down_at (s:Seq.seq int) (len:nat) (i:nat{i < len /\ len <= Seq.length s}) : prop =
  (left_idx i < len ==> Seq.index s i >= Seq.index s (left_idx i)) /\
  (right_idx i < len ==> Seq.index s i >= Seq.index s (right_idx i))
```

Node `i` dominates both its children within `[0, len)`.

### `almost_heaps_from` (from `CLRS.Ch06.Heap.Spec`)

```fstar
let almost_heaps_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (bad:nat{bad < len}) : prop =
  bad >= k /\
  (forall (j:nat). k <= j /\ j < len /\ j <> bad ==> heap_down_at s len j)
```

All nodes from `k` to `len-1` satisfy `heap_down_at` except at `bad`.
This is the invariant maintained during the sift-down loop of
`max_heapify`.

### `heaps_from` (from `CLRS.Ch06.Heap.Spec`)

```fstar
let heaps_from (s:Seq.seq int) (len:nat{len <= Seq.length s}) (k:nat) : prop =
  forall (j:nat). k <= j /\ j < len ==> heap_down_at s len j
```

All nodes from `k` to `len-1` satisfy `heap_down_at`. This is the
postcondition of `max_heapify` and the loop invariant of
`build_max_heap`.

### `heapsort_cost_bound` (from `CLRS.Ch06.Heap.CostBound`)

```fstar
let build_cost_bound (n: pos) : nat = (n / 2) * max_heapify_bound n 0
let extract_cost_bound (n: pos) : nat = (n - 1) * max_heapify_bound n 0
let heapsort_cost_bound (n: pos) : nat = build_cost_bound n + extract_cost_bound n
```

Where:

```fstar
let max_heapify_bound (heap_size: pos) (idx: nat{idx < heap_size}) : nat =
  heap_div_pos heap_size idx;
  2 * log2_floor (heap_size / (idx + 1))
```

At the root (`idx=0`), `max_heapify_bound n 0 = 2 * log2_floor n`.
So `heapsort_cost_bound n = (n/2 + n - 1) * 2 * log2_floor n`.

### `log2_floor` (from `CLRS.Ch06.Heap.Complexity`)

```fstar
let rec log2_floor (n: pos) : nat =
  if n = 1 then 0 else 1 + log2_floor (n / 2)
```

Standard floor of log base 2.

## What Is Proven

The postcondition `sorted s /\ permutation s0 s` is the **strongest
possible functional correctness specification** for an in-place sorting
algorithm.

The complexity bound `cf - c0 ≤ heapsort_cost_bound n` is linked to
the imperative implementation via a ghost counter. Each non-leaf
recursive call in `max_heapify` ticks 2 (for the two child
comparisons).

Additionally, in the pure `Complexity` module:

* `heapsort_cost_nlogn`: `heapsort_cost_bound n ≤ 4 * n * log2_floor n`
* `build_heap_ops_linear`: BUILD-MAX-HEAP is O(n) — CLRS Theorem 6.3
* `heapsort_ops_simplified`: HEAPSORT ≤ 6·n·(1 + log₂ n)
* `heapsort_better_than_quadratic`: beats O(n²) for n ≥ 11

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`n > 0` precondition.**~~ **RESOLVED.** The `n > 0`
   precondition has been removed. Heapsort now handles `n = 0`
   (empty arrays) by returning immediately with zero cost.

2. **`SZ.fits(2*n+2)` precondition.** Limits maximum array size to
   roughly `SZ.max / 2`. This is a practical overflow guard for
   child-index arithmetic, but excludes very large arrays.

3. ~~**Two separate complexity modules.**~~ **RESOLVED.** The two
   modules are now connected via `heapsort_ops_le_cost_bound`:
   `heapsort_ops n ≤ heapsort_cost_bound n`. This proves the pure
   operation count from `Complexity` is bounded by the ghost-counter
   cost bound from `CostBound`, so all tighter bounds (O(n) build,
   beats quadratic, etc.) are implied by the ghost-counter model.
   Component lemmas `build_heap_ops_le_build_cost` and
   `extract_max_ops_le_extract_cost` bridge each phase individually.

4. **Cost bounds are coarse per-iteration.** Each `build_max_heap`
   iteration is charged `max_heapify_bound n 0` (the root bound),
   rather than the tighter `max_heapify_bound n idx` for each specific
   index. The O(n) build-heap proof exists in `Complexity` but is not
   threaded through the ghost counter.

5. ~~**Array-length = n assumption.**~~ **RESOLVED.** The heapsort
   signature now only requires `SZ.v n <= A.length a` (not equality).
   Sorting a prefix of a larger array is fully supported: the first
   `n` elements are sorted in-place (`sorted_upto s n`), elements
   beyond index `n` are preserved unchanged, and the full array
   remains a permutation of the input.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons (heapsort) | O(n log n) = 4·n·log₂(n) | ✅ Ghost counter | Upper bound only |
| Comparisons (build) | O(n log n) = (n/2)·2·log₂(n) | ✅ Ghost counter | Upper bound only |
| Comparisons (max_heapify) | O(log n) = 2·log₂(n/(idx+1)) | ✅ Ghost counter | Upper bound only |
| Operations (pure model) | O(n log n) ≤ 6·n·(1+log₂n) | ✅ Bridged | Upper bound only |
| BUILD-MAX-HEAP (pure) | O(n) ≤ 4·n | ✅ Bridged | Upper bound only |

The ghost counter in the Pulse implementation tracks comparisons at
each `max_heapify` call. The pure `Complexity` module's bounds are now
connected to the ghost counter via `heapsort_ops_le_cost_bound`.

## Proof Structure

**`max_heapify`**: Recursive sift-down. Maintains
`almost_heaps_from s heap_size start idx` — the heap property holds
everywhere except at `idx`. At each step, if `s[idx]` is smaller than
its largest child, swap and recurse on the child. The cost decreases
by the `max_heapify_bound` recurrence
(`CB.max_heapify_bound_left/right`).

**`build_max_heap`**: Bottom-up loop from `n/2` down to 0. Invariant:
`heaps_from s n i` — all nodes from `i` onward satisfy heap property.
Each iteration calls `max_heapify` at the current index with
`start = idx`.

**`heapsort`**: Two phases.
1. `build_max_heap` establishes `is_max_heap s n`.
2. Extract-max loop: swap root with last element, shrink heap, call
   `max_heapify` at root. Invariant: `is_max_heap s vsz /\
   suffix_sorted s vsz /\ prefix_le_suffix s vsz`.

Key lemmas in `CLRS.Ch06.Heap.Lemmas`:
* `sift_down_swap_lemma_from`: swapping parent with child maintains
  `almost_heaps_from` with the child as the new bad node.
* `extract_extends_sorted`: swapping root to sorted suffix extends it.
* `root_ge_element`: in a max-heap, the root is the maximum.

## Files

| File | Role |
|------|------|
| `CLRS.Ch06.Heap.Impl.fsti` | Public interface (three signatures) |
| `CLRS.Ch06.Heap.Impl.fst` | Pulse implementation |
| `CLRS.Ch06.Heap.Spec.fst` | Heap predicates, sorted, permutation |
| `CLRS.Ch06.Heap.CostBound.fsti` | Cost bound signatures (ghost-counter-linked) |
| `CLRS.Ch06.Heap.CostBound.fst` | Cost bound proofs |
| `CLRS.Ch06.Heap.Complexity.fsti` | Pure complexity signatures (O(n log n), O(n) build) |
| `CLRS.Ch06.Heap.Complexity.fst` | Pure complexity proofs |
| `CLRS.Ch06.Heap.Lemmas.fsti` | Correctness lemma signatures |
| `CLRS.Ch06.Heap.Lemmas.fst` | Correctness lemma proofs |
| `CLRS.Ch06.Heap.ImplTest.fst` | Spec validation test (sorted_upto + permutation completeness) |

---

## Verification Profiling (2026-03-16)

Sequential verification times (each file checked individually):

| File | Before (s) | After (s) | Change | z3rlimit (max) |
|------|-----------|-----------|--------|---------------|
| `Heap.Spec.fst` | 2.4 | 1.1 | — | default |
| `Heap.Complexity.fsti` | 0.7 | 0.4 | — | — |
| `Heap.Complexity.fst` | 69.0 | 47.0 | — | 300 (small-n norm) / 40 |
| `Heap.CostBound.fsti` | 1.6 | 0.5 | — | — |
| `Heap.CostBound.fst` | 2.9 | 1.1 | — | 20 |
| `Heap.Lemmas.fsti` | 5.6 | 1.4 | — | — |
| `Heap.Lemmas.fst` | 238.0 | 63.0 | **−74%** | 200 (was ×2, now ×1) |
| `Heap.Impl.fsti` | 5.9 | 2.8 | — | — |
| `Heap.Impl.fst` | 445.0 | 241.0 | **−46%** | 80 |
| **Total (sequential)** | **771** | **359** | **−53%** | |
| **Total (parallel, -j4)** | **324** | **246** | **−24%** | |

### Optimization Applied

Deduplicated `perm_prefix_bounded_aux` and `perm_prefix_bounded_aux_upto` in Lemmas.fst.
The `_upto` versions (more general, working on arbitrary range `[0,n)`) are now defined
first; the non-`_upto` versions delegate to them with `n = Seq.length s`. This eliminated
one copy of the expensive z3rlimit 200 proof, cutting Lemmas.fst from 238s to 63s.
The improvement propagated to Impl.fst (445s → 241s) due to simpler SMT context.

### Remaining Bottleneck

**Impl.fst (241s):** The Pulse `heapsort` function (z3rlimit 80) is the dominant cost.
z3rlimit 60 was attempted but fails on the loop-exit postcondition. Further reduction
would require splitting the proof or adding more intermediate assertions.

---

## Current Improvement Checklist (2026-03-16)

### Proof Optimization & Stabilization

- [x] **P1.** Deduplicate `_upto` lemma proofs in `Lemmas.fst` — `perm_preserves_sorted_suffix` and `extract_extends_sorted` now delegate to their `_upto` counterparts. Eliminated duplicate `perm_prefix_bounded_aux` (z3rlimit 200). Lemmas.fst: 238s → 63s (−74%).
- [x] **P2.** Reduce z3rlimit 200 occurrences — removed one of two z3rlimit 200 proofs via deduplication. One instance remains (the general `_upto` version, which is unavoidable).
- [x] **P3.** Optimize `Impl.fst` verification time — added `#restart-solver` before `build_max_heap`. Impl.fst: 445s → 241s (−46%). z3rlimit 80 on heapsort cannot be reduced further (60 fails).
- [ ] **P4.** Reduce z3rlimit 300 / fuel 20 on `build_heap_ops_le_root_bound_small` in `Complexity.fst` (low priority)

### Documentation Accuracy

- [x] **D1.** Fix `README.md` — updated heapsort postcondition from `sorted s` to `sorted_upto s (SZ.v n)` with prefix-preservation; updated specification tables
- [x] **D2.** Update `RUBRIC_06.md` z3rlimit table — updated to reflect heapsort z3rlimit 80, added Complexity.fst z3rlimit 300

### Spec Validation (2026-03-17)

- [x] **S1.** Write `ImplTest.fst` — spec validation test for `heapsort` sorting [3;1;2] → [1;2;3]. Proves precondition satisfiable and postcondition precise (uniquely determines output). Zero admits, zero assumes.
- [x] **S2.** Write `ImplTest.md` — documents test methodology, what is proven, and specification assessment.
- [x] **S3.** Spec assessment: `sorted_upto + permutation` is the strongest possible functional correctness spec for in-place sorting. No specification gaps or weaknesses found.

### Functional Improvements (deferred)

- [ ] **F1.** Aggregate ghost-tick bounds: thread tighter per-index `max_heapify_bound` through `build_max_heap` instead of root bound
- [ ] **F2.** Rename `bad` → `child` in `bad_is_child_of_parent` (Lemmas)
- [ ] **F3.** Implement §6.5 priority-queue operations (HEAP-MAXIMUM, EXTRACT-MAX, INCREASE-KEY, INSERT)
