# Chapter 2: Getting Started — Insertion Sort & Merge Sort

Fully verified implementations of insertion sort (CLRS §2.1) and merge sort (CLRS §2.3)
in Pulse, with **zero admits, assumes, or assume_ calls** across all files.

## Building

```bash
cd ch02-getting-started
make
```

## File Inventory

| File | Role |
|------|------|
| `CLRS.Ch02.InsertionSort.Spec.fst` | Pure spec: `complexity_bounded` predicate |
| `CLRS.Ch02.InsertionSort.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch02.InsertionSort.Lemmas.fst` | Lemma proofs: `lemma_prefix_le_key`, `lemma_combine_sorted_regions`, `lemma_triangle_step` |
| `CLRS.Ch02.InsertionSort.Impl.fsti` | Public interface for `insertion_sort` |
| `CLRS.Ch02.InsertionSort.Impl.fst` | Pulse implementation with correctness + complexity proof |
| `CLRS.Ch02.MergeSort.Spec.fst` | Pure spec: `seq_merge`, `all_ge`, `ms_cost`, complexity predicates |
| `CLRS.Ch02.MergeSort.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch02.MergeSort.Lemmas.fst` | Lemma proofs: merge properties, suffix stepping, cost splitting |
| `CLRS.Ch02.MergeSort.Complexity.fsti` | Interface: `merge_sort_ops`, `merge_sort_bound`, `merge_sort_is_n_log_n` |
| `CLRS.Ch02.MergeSort.Complexity.fst` | Pure O(n log n) bound proof |
| `CLRS.Ch02.MergeSort.Impl.fsti` | Public interface for `merge` and `merge_sort` |
| `CLRS.Ch02.MergeSort.Impl.fst` | Pulse implementation with correctness + complexity proof |

**Common dependencies** (in `../common/`):
- `CLRS.Common.SortSpec.fst` — `sorted`, `prefix_sorted`, `permutation`, swap/append lemmas
- `CLRS.Common.Complexity` — ghost tick counter (`tick`, `incr_nat`)

---

## Insertion Sort

### Key Definitions

From `CLRS.Common.SortSpec`:

```fstar
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let prefix_sorted (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i <= j /\ j < k ==> Seq.index s i <= Seq.index s j)

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

From `CLRS.Ch02.InsertionSort.Spec`:

```fstar
let complexity_bounded (cf c0: nat) (n: nat) : prop =
  cf >= c0 /\
  cf - c0 <= op_Multiply n (n - 1) / 2
```

### Postcondition (from `Impl.fsti`)

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
       Seq.length s0 <= A.length a /\
       SZ.v len > 0))
    (fun _ -> exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf ** pure (
       Seq.length s == Seq.length s0 /\
       sorted s /\
       permutation s0 s /\
       complexity_bounded cf (reveal c0) (SZ.v len)))
```

**What each conjunct means:**
1. `Seq.length s == Seq.length s0` — the array length is unchanged.
2. `sorted s` — the output is fully sorted (∀ i ≤ j. s[i] ≤ s[j]).
3. `permutation s0 s` — the output is a permutation of the input (same multiset).
4. `complexity_bounded cf (reveal c0) (SZ.v len)` — at most n(n−1)/2 comparisons.

### Strongest Guarantee

`sorted s ∧ permutation s0 s` is the strongest functional correctness specification for an in-place comparison sort. Together they guarantee:
- No element is duplicated, dropped, or fabricated.
- The output is the unique sorted arrangement of the input elements.

### Limitations

- **Positive length required**: The precondition requires `SZ.v len > 0`. Empty arrays are trivially sorted but the implementation's outer loop starts at index 1. Callers must guard against empty inputs.
- **Swap vs. shift**: CLRS shifts elements rightward and inserts the key once; our implementation swaps adjacent elements to bubble the key leftward. The comparison count is identical, but the write count is 2× the textbook's shift variant. This does not affect the proven bound (which counts comparisons).

### Complexity

The complexity proof is **linked**: the same function that proves correctness also proves the bound. The ghost counter is incremented by `tick` (from `CLRS.Common.Complexity`) at each comparison.

- **Bound**: n(n−1)/2 comparisons (worst case). This is **tight** — achieved on reverse-sorted input.
- **Proof technique**: Triangular sum invariant. After outer iteration j, comparisons ≤ j(j−1)/2. Inner loop adds at most j. Arithmetic: j(j−1)/2 + j = (j+1)j/2, proved by `lemma_triangle_step`.

---

## Merge Sort

### Key Definitions

From `CLRS.Ch02.MergeSort.Spec`:

```fstar
let rec seq_merge (s1 s2: Seq.seq int)
  : Tot (Seq.seq int) (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then s2
    else if Seq.length s2 = 0 then s1
    else let h1 = Seq.head s1 in
         let h2 = Seq.head s2 in
         if h1 <= h2
         then Seq.cons h1 (seq_merge (Seq.tail s1) s2)
         else Seq.cons h2 (seq_merge s1 (Seq.tail s2))

let merge_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= hi - lo

let sort_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= ms_cost (hi - lo)
```

From `CLRS.Ch02.MergeSort.Complexity`:

```fstar
let rec merge_sort_ops (n: pos) : Tot nat (decreases n)
  = if n = 1 then 0
    else 2 * merge_sort_ops (ceil_div2 n) + n

let merge_sort_bound (n: pos) : nat = 4 * n * log2_ceil n + 4 * n

let merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_ops n <= merge_sort_bound n)
  = merge_sort_n_log_n_bound n
```

### Postconditions (from `Impl.fsti`)

**Merge:**

```fstar
val merge
  (a: array int) (lo mid hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s1 #s2: Ghost.erased (Seq.seq int))
  : stt unit
    (pts_to_range a (SZ.v lo) (SZ.v mid) s1 **
     pts_to_range a (SZ.v mid) (SZ.v hi) s2 **
     GR.pts_to ctr c0 **
     pure (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ sorted s1 /\ sorted s2))
    (fun _ -> exists* s_out (cf: nat).
       pts_to_range a (SZ.v lo) (SZ.v hi) s_out **
       GR.pts_to ctr cf **
       pure (
         sorted s_out /\
         permutation (Seq.append s1 s2) s_out /\
         merge_complexity_bounded cf (reveal c0) (SZ.v lo) (SZ.v hi)))
```

**Merge Sort:**

```fstar
val merge_sort
  (a: A.array int)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s0: erased (Seq.seq int))
  : stt unit
    (A.pts_to a s0 **
     GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       SZ.v len == A.length a))
    (fun _ -> exists* s (cf: nat).
       A.pts_to a s **
       GR.pts_to ctr cf **
       pure (
         Seq.length s == Seq.length s0 /\
         sorted s /\
         permutation s0 s /\
         sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)))
```

**What each conjunct means (merge_sort):**
1. `Seq.length s == Seq.length s0` — length preserved.
2. `sorted s` — output is fully sorted.
3. `permutation s0 s` — output is a permutation of input.
4. `sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)` — at most `ms_cost(n)` comparisons, where `ms_cost(n) ≤ 4n⌈log₂ n⌉ + 4n`.

### Strongest Guarantee

As with insertion sort, `sorted s ∧ permutation s0 s` is the strongest functional specification for comparison sorting. Merge sort additionally proves the tighter O(n log n) complexity.

Unlike insertion sort, **no positive-length restriction** — empty and singleton arrays are handled by the base case.

### Limitations

- **Temporary allocation**: The merge step heap-allocates two temporary vectors per call. These are freed after each merge, but the allocation pattern differs from CLRS's single-auxiliary-array approach. Does not affect the proven comparison count but increases memory traffic.
- **Loose complexity constant**: The proven bound 4n⌈log₂ n⌉ + 4n is roughly 4× the practical comparison count of ≈ n⌈log₂ n⌉. The constant 4 was chosen to simplify the inductive proof. Tightening it is possible but would complicate the arithmetic lemmas significantly. For example, at n=1000 the bound gives ≤44,000 while actual merge sort uses ≈10,000 comparisons.

### Complexity

The complexity analysis is a pure F* proof in `CLRS.Ch02.MergeSort.Complexity` (no Pulse).

- **Recurrence**: T(1) = 0, T(n) = 2·T(⌈n/2⌉) + n
- **Closed-form bound**: T(n) ≤ 4n⌈log₂ n⌉ + 4n = O(n log n)
- **Proof**: Strong induction. Key lemma `arithmetic_step` shows 8m·log m + 8m + n ≤ 4n·log n + 4n where m = ⌈n/2⌉. Uses `log_linear_bound`: for n ≥ 2, 4·log₂⌈n/2⌉ + 4 ≤ 3n.
- **Implementation link**: The Pulse code threads the ghost counter; its postcondition references `sort_complexity_bounded` defined via `merge_sort_ops`. The bridge lemma `ms_cost_split` connects the floor-division split to the ceiling-division recurrence.

---

## Summary Table

| Property | Insertion Sort | Merge Sort |
|----------|---------------|------------|
| **Sorted** | ✓ | ✓ |
| **Permutation** | ✓ | ✓ |
| **Complexity bound** | n(n−1)/2 (tight) | 4n⌈log₂ n⌉ + 4n (loose, ~4× actual) |
| **Asymptotic class** | O(n²) | O(n log n) |
| **Ghost counter linked** | ✓ | ✓ |
| **Empty input** | ✗ (requires len > 0) | ✓ |
| **In-place** | ✓ (swaps) | ✗ (temp alloc per merge) |
| **Admits/assumes** | 0 | 0 |
| **Spec files** | InsertionSort.Spec | MergeSort.Spec + MergeSort.Complexity |
| **Lemma files** | InsertionSort.Lemmas | MergeSort.Lemmas |
| **Impl files** | InsertionSort.Impl | MergeSort.Impl |

## References

- CLRS Chapter 2: Getting Started
- [PoP-in-FStar, Part 5: Pulse](https://fstar-lang.org/tutorial/pulse)
