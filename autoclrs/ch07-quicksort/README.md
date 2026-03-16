# CLRS Chapter 7: Quicksort

Verified implementation of the quicksort algorithm from CLRS Chapter 7, including
the Lomuto partition scheme (§7.1) and the recursive quicksort with worst-case
O(n²) complexity analysis. The implementation is in Pulse with separate pure
complexity modules. All proofs are mechanically checked by F\* and Pulse.
**ZERO admits. ZERO assumes.**

## Algorithms

### 1. Partition (CLRS §7.1)

**Specification.** The partition uses the Lomuto scheme with the last element as
pivot. The `between_bounds` and `complexity_exact_linear` predicates are defined
in the shared Lemmas module:

```fstar
let between_bounds (s: Seq.seq int) (lb rb: int) =
  larger_than s lb /\ smaller_than s rb

let complexity_exact_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n
```

**Correctness Theorem.** The exact `Partition.Impl.fsti` signature for
`clrs_partition_wrapper_with_ticks`:

```pulse
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
      between_bounds s0 lb rb))
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
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `lo <= p /\ p < hi` | Pivot index is within the range |
| Array split into 3 regions | `s1` (left), `s_pivot` (pivot), `s2` (right) via `pts_to_range` |
| `between_bounds s1 lb pivot` | All left elements ≤ pivot |
| `between_bounds s2 pivot rb` | All right elements ≥ pivot (actually > pivot from partition logic) |
| `permutation s0 (s1 ++ s_pivot ++ s2)` | Result is a permutation of input |
| `complexity_exact_linear cf c0 (hi-lo-1)` | **Exactly** hi−lo−1 comparisons |

**Strongest Guarantee.** The partition performs **exactly** n−1 comparisons (not
just ≤ n−1). This is the tightest possible bound: every non-pivot element is
compared against the pivot exactly once. The three-region split with
`pts_to_range` ownership transfer enables recursive quicksort to process
sub-arrays independently.

**Limitations.** The Lomuto scheme always picks the last element as pivot. This
leads to worst-case O(n²) on sorted/reverse-sorted input. CLRS §7.3 discusses
randomized pivot selection, which is NOT implemented here.

**Complexity.** Exactly hi−lo−1 = n−1 comparisons, linked to ghost counter.

### 2. Quicksort (CLRS §7.1)

**Specification.** The Quicksort.Lemmas module defines:

```fstar
let complexity_bounded_quadratic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n * (n - 1) / 2
```

**Correctness Theorem.** The `Quicksort.Impl.fsti` exports three variants:

**(a) `quicksort`** — correctness only (no complexity):

```pulse
fn quicksort
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
```

**(b) `quicksort_with_complexity`** — sorted + permutation + O(n²):

```pulse
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

**(c) `quicksort_bounded`** — sub-range sorting with caller-provided bounds:

```pulse
fn quicksort_bounded
  (a: A.array int)
  (lo: nat) (hi: (hi:nat{lo <= hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (hi <= A.length a /\ Seq.length s0 = hi - lo /\ between_bounds s0 lb rb /\ lb <= rb)
  ensures exists* s. (A.pts_to_range a lo hi s ** pure (sorted s /\ permutation s0 s))
```

**Strongest Guarantee.** The postcondition proves both sorted order and
permutation — the standard correctness specification for comparison-based sorting.
The O(n²) bound is the tightest *worst-case* bound for deterministic quicksort
with any fixed pivot rule.

**Limitations.**
- **Only worst-case bound proven.** The average-case O(n log n) bound from CLRS
  §7.4 is NOT proven. Proving it would require a randomization analysis
  (expected value over random pivot choices), which is outside the scope of
  this deterministic formalization.
- **Worst case is tight.** For already-sorted or reverse-sorted input with last-element
  pivot, partition always produces a maximally unbalanced split (0 and n−1),
  giving exactly n(n−1)/2 comparisons.
- **Ghost bounds threading.** The recursive calls thread ghost `lb`/`rb` bounds
  through the recursion. The top-level `quicksort` computes these via `seq_min`/
  `seq_max`, which requires a non-empty array (`len > 0`).

**Complexity.** Worst-case O(n²), linked to ghost counter. The pure Complexity
module defines the recurrence and proves:

```fstar
(* Recurrence: T(n) = T(n-1) + (n-1) when partition is maximally unbalanced *)
let rec worst_case_comparisons (n: nat) : nat =
  if n <= 1 then 0
  else n - 1 + worst_case_comparisons (n - 1)

(* Closed form: T(n) = n(n-1)/2 *)
val worst_case_bound (n: nat)
  : Lemma (ensures (2 * worst_case_comparisons n == n * (n - 1)))

(* Convexity: any partition split is bounded by worst case *)
val partition_split_bounded (n: nat{n > 1}) (k: nat{k < n})
  : Lemma (ensures n - 1 + worst_case_comparisons k + worst_case_comparisons (n - 1 - k)
                  <= worst_case_comparisons n)
```

The `partition_split_bounded` lemma is the key insight: for any split point `k`,
the total work `(n-1) + T(k) + T(n-1-k) ≤ T(n)`. This is proved by the
`sum_of_parts_bound` convexity lemma: `T(a) + T(b) ≤ T(a+b)`.

## File Inventory

| File | Role | Language |
|------|------|---------|
| `CLRS.Ch07.Partition.Lemmas.fsti` | Shared definitions: `between_bounds`, `seq_swap`, `complexity_exact_linear` + lemma interface | F\* |
| `CLRS.Ch07.Partition.Lemmas.fst` | Proofs: `permutation_swap`, `transfer_larger_slice`, `transfer_smaller_slice` | F\* |
| `CLRS.Ch07.Partition.Complexity.fsti` | Partition complexity interface | F\* |
| `CLRS.Ch07.Partition.Complexity.fst` | Partition performs exactly n−1 comparisons | F\* |
| `CLRS.Ch07.Partition.Impl.fsti` | Public interface: `clrs_partition_wrapper_with_ticks` | Pulse |
| `CLRS.Ch07.Partition.Impl.fst` | Pulse implementation: `tick`, `swap`, partition loop, wrapper | Pulse |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | Shared definitions: `seq_min`/`seq_max`, `complexity_bounded_quadratic` + lemma interface | F\* |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | Proofs: `lemma_sorted_append`, `append_permutations_3`, complexity bound | F\* |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | Complexity analysis interface | F\* |
| `CLRS.Ch07.Quicksort.Complexity.fst` | Worst-case recurrence, closed form, convexity, monotonicity | F\* |
| `CLRS.Ch07.Quicksort.Impl.fsti` | Public API: `quicksort`, `quicksort_with_complexity`, `quicksort_bounded` | Pulse |
| `CLRS.Ch07.Quicksort.Impl.fst` | Recursive quicksort with ghost proof function | Pulse |

## Summary

| Algorithm | CLRS Section | Correctness | Complexity | Linked? | Admits |
|-----------|-------------|-------------|-----------|---------|--------|
| Partition | §7.1 | 3-region split + permutation | Θ(n−1): exactly n−1 comparisons | Yes (ghost ctr) | 0 |
| Quicksort | §7.1 | `sorted` + `permutation` | O(n²): ≤ n(n−1)/2 comparisons | Yes (ghost ctr) | 0 |
| Quicksort (bounded) | §7.1 | Sub-range sorted + permutation | (no counter) | No | 0 |

## Building

```bash
cd ch07-quicksort && make
```
