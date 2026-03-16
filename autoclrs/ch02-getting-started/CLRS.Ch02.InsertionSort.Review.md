# Insertion Sort (CLRS §2.1)

## Top-Level Signature

Here is the top-level signature proven about Insertion Sort in
`CLRS.Ch02.InsertionSort.Impl.fsti`:

```fstar
val insertion_sort
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt unit
    (A.pts_to a s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a))
    (fun _ -> exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf ** pure (
       Seq.length s == Seq.length s0 /\
       sorted s /\
       permutation s0 s /\
       complexity_bounded cf (reveal c0) (SZ.v len)))
```

### Parameters

* `a` is a mutable array of `int` (mathematical, unbounded integers in F\*).
  The ghost variable `s0` captures the initial contents of the array.

* `len` is the number of elements to sort, of type `SZ.t` (machine-sized,
  analogous to `size_t` in C).

* `ctr` is a **ghost counter** — a ghost reference to a natural number used to
  count comparisons. The initial value is `c0`. Ghost values are erased at
  runtime; they exist only for specification and proof.

### Preconditions

* `SZ.v len == Seq.length s0`: The length parameter matches the logical
  sequence length.

* `Seq.length s0 <= A.length a`: The logical sequence fits within the physical
  array (the array may be larger than `len`).

### Postcondition

The `ensures` clause states that there exist a final sequence `s` and a final
counter value `cf` such that:

* `Seq.length s == Seq.length s0` — The output has the same length as the input.

* `sorted s` — The output is sorted.

* `permutation s0 s` — The output is a permutation of the input.

* `complexity_bounded cf (reveal c0) (SZ.v len)` — The number of comparisons is
  bounded.

## Auxiliary Definitions

### `sorted` (from `CLRS.Common.SortSpec`)

```fstar
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

This is the standard definition of a sorted sequence: for all pairs of
indices `i ≤ j`, the element at `i` is less than or equal to the element at
`j`. This is an all-pairs characterization, which is the strongest possible
statement (equivalent to the adjacent-pairs definition, but stated more
directly).

### `permutation` (from `CLRS.Common.SortSpec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

This wraps F\*'s standard library notion of permutation (based on
`Seq.Properties.permutation`), which defines that `s2` is a permutation of `s1`
if they have the same length and one can be obtained from the other by a
sequence of transpositions. The `opaque_to_smt` attribute prevents the SMT
solver from unfolding the definition, which is important for performance — the
proofs use explicit permutation lemmas instead.

### `complexity_bounded` (from `CLRS.Ch02.InsertionSort.Spec`)

```fstar
let complexity_bounded (cf c0: nat) (n: nat) : prop =
  cf >= c0 /\
  cf - c0 <= op_Multiply n (n - 1) / 2
```

This says the total number of comparisons (the difference `cf - c0` between the
final and initial counter values) is at most `n(n−1)/2`. This is the
**worst-case** bound for insertion sort, which occurs when the input is sorted
in reverse order.

## What Is Proven

The postcondition `sorted s /\ permutation s0 s` is the **strongest possible
functional correctness specification** for an in-place sorting algorithm: it
states that the output is both sorted and a rearrangement of the input. No
elements are lost, duplicated, or invented.

The complexity bound `cf - c0 ≤ n(n−1)/2` is the **tight worst-case bound**
for insertion sort. In the worst case (reverse-sorted input), the inner loop
performs `1 + 2 + ... + (n−1) = n(n−1)/2` comparisons. The bound is proven by
threading a ghost counter through the Pulse implementation: each comparison in
the inner loop increments the counter by exactly 1.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **~~`len > 0` precondition.~~** *(Addressed.)* The implementation now accepts
   `len >= 0`. When `len = 0`, the function returns immediately using
   `singl_sorted` and `permutation_refl` — the empty sequence is trivially
   sorted and a permutation of itself.

2. **Swap-based vs. shift-based.** CLRS describes insertion sort using a
   shift-based approach (slide elements right to make room for the key). This
   implementation uses adjacent swaps instead, which is functionally equivalent
   but performs more writes. The specification does not distinguish between the
   two strategies — both satisfy `sorted ∧ permutation`.

3. **Best-case complexity not captured.** The bound `n(n−1)/2` is worst-case.
   For already-sorted input, insertion sort performs only `n−1` comparisons. The
   specification does not prove this best-case or adaptive behavior; it only
   upper-bounds the count.

4. **Only upper bound, not exact count.** The specification proves
   `cf - c0 ≤ n(n−1)/2`, not that the count is exactly `n(n−1)/2`. The actual
   count depends on the input, and the specification correctly captures only
   the worst case.

## Profiling (2026-03-16)

| File | Verification Time | Z3 Options |
|------|-------------------|------------|
| `InsertionSort.Spec.fst` | ~7s | defaults |
| `InsertionSort.Lemmas.fst` | ~7s | defaults |
| `InsertionSort.Impl.fst` | **~29s** | `--z3rlimit 20 --fuel 1 --ifuel 1` |

**Bottleneck:** `InsertionSort.Impl.fst` dominates verification time at ~29s.
The inner while loop invariant with 10+ conjuncts drives most of the SMT cost.
Explicit z3 options (`--z3rlimit 20 --fuel 1 --ifuel 1`) have been added for
proof stability; previously the file relied on defaults (which took ~120s).

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | O(n²) = n(n−1)/2 | ✅ Ghost counter | Upper bound only |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented inside the inner comparison loop of the Pulse
code, and the postcondition directly constrains `cf - c0`. This is not a
separate pure proof — it is part of the same verified implementation.

## Proof Structure

The proof proceeds by maintaining a loop invariant on the outer loop
(`j = 1, ..., len-1`): after iteration `j`, the prefix `s[0..j]` is sorted
and the total array is a permutation of the original. Three lemmas in
`CLRS.Ch02.InsertionSort.Lemmas` support the proof:

* `lemma_prefix_le_key`: Elements before the insertion point are ≤ the key.
* `lemma_combine_sorted_regions`: Combining the sorted prefix, the inserted
  key, and the shifted suffix produces a sorted prefix.
* `lemma_triangle_step`: The arithmetic identity `j(j−1)/2 + j = (j+1)j/2`,
  used to maintain the complexity invariant across iterations.

## Files

| File | Role |
|------|------|
| `CLRS.Ch02.InsertionSort.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch02.InsertionSort.Impl.fst` | Pulse implementation |
| `CLRS.Ch02.InsertionSort.Spec.fst` | `complexity_bounded` definition |
| `CLRS.Ch02.InsertionSort.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch02.InsertionSort.Lemmas.fst` | Lemma proofs |
| `CLRS.Common.SortSpec.fst` | `sorted`, `permutation` definitions |
| `CLRS.Common.Complexity.fst` | Ghost tick counter infrastructure |

## Priority Checklist

Items in priority order for reaching a fully proven, high-quality implementation:

- [x] Zero admits, zero assumes — fully proven
- [x] Rubric-conformant file structure (Spec, Lemmas, Impl split)
- [x] Public interface (`Impl.fsti`) with full postcondition
- [x] Handles `len = 0` (no positive-length restriction)
- [x] Complexity bound proven and linked via ghost counter
- [x] Explicit z3 options for proof stability
- [ ] **Reduce verification time** — `Impl.fst` takes ~120s; consider
      splitting the inner loop proof into a separate lemma or using
      `assert ... by (...)` to guide SMT on the 10-conjunct invariant
- [ ] **Best-case / adaptive complexity** — prove Ω(n) for sorted input
- [ ] **Tighten swap-count bound** — prove 2× write overhead vs CLRS shift variant
