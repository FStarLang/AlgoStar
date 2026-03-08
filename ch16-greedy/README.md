# Chapter 16: Greedy Algorithms — Verified in F\*/Pulse

## Overview

This directory implements two greedy algorithms from CLRS Chapter 16:

1. **Activity Selection** (§16.1) — GREEDY-ACTIVITY-SELECTOR
2. **Huffman Coding** (§16.3) — HUFFMAN

Activity Selection is **fully proven** with zero admits and zero assumes
across all files. Huffman Coding is **fully proven** at the specification
level (`Spec.fst`, `Complete.fst`, `Optimality.fst`, `Codec.fst`) with
zero admits and zero assumes. The Pulse imperative implementation
(`Huffman.Impl.fst`) has **zero admits** but the priority-queue integration
relies on **3 `assume_` calls** for PQ distinctness invariants (see
Limitations below).

---

## Activity Selection (CLRS §16.1)

### Algorithm

Given *n* activities with start and finish times (sorted by finish time),
the greedy algorithm selects the maximum number of non-overlapping activities
by always choosing the earliest-finishing compatible activity.

### Specification

Activities are modelled as two sequences of integers (start times and finish
times). The core predicates in `ActivitySelection.Spec.fst` define:

- **`finish_sorted f`**: activities are sorted by finish time.
- **`compatible start finish i j`**: activities `i` and `j` do not overlap.
- **`mutually_compatible start finish selected`**: every pair in `selected`
  is compatible.
- **`max_compatible_count start finish n`**: the maximum cardinality of any
  mutually compatible subset — a ghost specification-level definition using
  `StrongExcludedMiddle`.
- **`is_optimal_selection start finish n selected`**: `selected` is mutually
  compatible, sorted, and has cardinality equal to `max_compatible_count`.

### Correctness Theorem

```fstar
fn activity_selection
  (#p: perm)
  (start_times finish_times: A.array int)
  (out: A.array SZ.t) (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  (#sout0: Ghost.erased (Seq.seq SZ.t))
  (ctr: GR.ref nat) (#c0: erased nat)
  requires
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    A.pts_to out sout0 ** GR.pts_to ctr c0 **
    pure (activity_selection_pre n ss sf sout0 start_times finish_times out)
  returns count: SZ.t
  ensures exists* sout (cf: nat).
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    A.pts_to out sout ** GR.pts_to ctr cf **
    pure (activity_selection_post count n sout cf (reveal c0) ss sf)
```

Where `activity_selection_post` requires:

| Postcondition | Meaning |
|---|---|
| `SZ.v count >= 1 /\ SZ.v count <= SZ.v n` | At least one activity selected, at most n |
| `pairwise_compatible sel ss sf` | Selected activities don't overlap |
| `strictly_increasing sel` | Indices are in sorted order |
| `Seq.index sel 0 == 0` | Greedy always picks the earliest-finishing activity first |
| `earliest_compatible sel ss sf n n` | Each selected activity is the earliest compatible one |
| `SZ.v count == S.max_compatible_count ss sf (SZ.v n)` | **Optimality**: count equals maximum possible |
| `complexity_bounded_linear cf c0 n` | Exactly `n − 1` comparisons |

### Strongest Guarantee

The postcondition `count == max_compatible_count` is the strongest possible
functional guarantee: it proves the greedy result has maximum cardinality
among *all* mutually compatible subsets. The proof chain is:

1. **Greedy choice** (`lemma_greedy_choice`): the earliest-finishing activity
   belongs to some optimal solution (exchange argument).
2. **Dominance** (`lemma_greedy_dominates`): the greedy selection's finish
   times dominate any other valid selection's.
3. **Maximality** (`lemma_greedy_is_maximal`): no compatible set is larger
   than the greedy selection.
4. **Bridge** (`theorem_implementation_optimal`): connects the Pulse output
   (sequences satisfying `pairwise_compatible`, `strictly_increasing`,
   `earliest_compatible`) to the specification-level `is_optimal_selection`.

### Complexity

O(n) — proven tight and **linked** to the Pulse implementation. The ghost
counter proves exactly `n − 1` comparisons for presorted input. This
complexity proof is inside the Pulse implementation (`activity_selection_post`
includes `complexity_bounded_linear cf c0 n`).

### Limitations

None. Zero admits, zero assumes across all files.

---

## Huffman Coding (CLRS §16.3)

### Algorithm

Builds an optimal prefix-code tree by repeatedly merging the two
lowest-frequency subtrees using a priority queue. The formalization has
three levels:

1. **Pure construction** (`huffman_from_sorted` in `Spec.fst`): builds the
   tree from a sorted list. Used for the optimality proof.
2. **Complete construction** (`huffman_complete` in `Complete.fst`):
   full CLRS HUFFMAN algorithm with sorted-list PQ. WPL-optimality fully
   proven.
3. **Pulse implementation** (`huffman_tree` in `Impl.fst`): imperative
   implementation using `Pulse.Lib.PriorityQueue` (binary heap). Postcondition
   includes `is_wpl_optimal`.

### Specification

Huffman trees are an inductive type where every internal node has exactly
two children:

```fstar
type htree =
  | Leaf : sym:nat -> freq:pos -> htree
  | Internal : freq:pos -> left:htree -> right:htree -> htree
```

Key definitions:

- **`weighted_path_length t`**: sum of `freq × depth` over all leaves.
- **`cost t`**: sum of all internal node frequencies.
- **`wpl_equals_cost`**: proves WPL = cost (CLRS equation 16.4).
- **`same_frequency_multiset t freqs`**: the tree's leaf frequencies form
  the same multiset as `freqs`.
- **`is_wpl_optimal t freqs`**: `same_frequency_multiset t freqs` and
  WPL(t) ≤ WPL(t') for all t' with the same frequency multiset.

### Correctness Theorem

The Pulse implementation signature:

```fstar
fn huffman_tree
  (freqs: A.array int) (#freq_seq: Ghost.erased (Seq.seq int)) (n: SZ.t)
  requires A.pts_to freqs freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\ SZ.v n > 0 /\
    SZ.fits (2 * SZ.v n + 2) /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0))
  returns result: hnode_ptr
  ensures A.pts_to freqs freq_seq **
    (exists* ft. is_htree result ft **
      pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
            HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
            HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)))
```

| Postcondition | Meaning |
|---|---|
| `cost ft == greedy_cost (...)` | Tree cost equals the greedy merging cost |
| `same_frequency_multiset ft (...)` | Leaf frequencies match the input |
| `is_wpl_optimal ft (...)` | WPL is minimal among all trees with the same frequency multiset |

The optimality theorem in `Complete.fst`:

```fstar
let huffman_complete_optimal (freqs: list pos{Cons? freqs})
  : Lemma (ensures is_wpl_optimal (huffman_complete freqs) freqs)
```

### Strongest Guarantee

The postcondition `is_wpl_optimal` is the strongest possible guarantee: it
proves the constructed tree minimizes WPL over *all* trees with the same leaf
frequency multiset. The proof relies on three CLRS results:

- **`swap_reduces_wpl`** (CLRS Lemma 16.2, *proven*): swapping a
  high-frequency leaf at a deep position with a low-frequency leaf at a
  shallow position does not increase WPL.
- **`exists_sibling_leaves`** (*proven*): every full binary tree with ≥ 2
  leaves has a pair of sibling leaves.
- **`greedy_choice_property` and `optimal_substructure_property`** (CLRS
  Lemmas 16.2–16.3, *proven*): the full greedy-choice and optimal-substructure
  theorems.

### Codec Module

A separate `Codec` module provides verified encode/decode operations:

- **`encode t msg`**: encodes a message as a bitstring using the Huffman tree.
- **`decode t bits`**: decodes a bitstring back to a message.
- **`encode_decode_roundtrip`**: proves `decode(encode(msg)) == msg`.
- **`decode_encode_roundtrip`**: proves `encode(decode(bits)) == bits`
  (requires well-formedness).

The `Codec.Impl` module provides Pulse implementations of encode and decode
with matching postconditions.

### Complexity

O(n²) — proven for the sorted-list construction (n − 1 merge iterations,
each with O(n) sorted insertion comparisons). The bound `ticks ≤ n²` is
proven by induction in `Complexity.fst`. The Pulse implementation uses a
binary heap (`Pulse.Lib.PriorityQueue`), which would give O(n log n), but
that bound is **not formally proven**.

### Limitations

**⚠️ 3 `assume_` calls in PQ integration.** The Pulse implementation
(`Huffman.Impl.fst`) contains zero `admit` calls, but the priority-queue
integration loop relies on properties of `Pulse.Lib.PriorityQueue` that
are asserted via `assume_` rather than proven:

1. After `extract_min`, the remaining PQ entries still have distinct indices.
2. After `insert`, the new PQ entries have distinct indices.
3. The PQ's size relationship is maintained across extract/insert.

These are properties of the PQ library's `extends` predicate that should
hold but are not exported by the PQ library's interface. The specification
layer (`Spec.fst`, `Complete.fst`, `Optimality.fst`) has **zero assumes** —
the gap is purely in the Pulse-to-PQ bridge.

**Complexity not linked.** The O(n²) bound is for the sorted-list variant;
the Pulse implementation uses a binary heap. Neither complexity bound is
proven inside the Pulse implementation via a ghost counter.

---

## File Inventory

### Activity Selection

| File | Role | Admits |
|---|---|---|
| `CLRS.Ch16.ActivitySelection.Spec.fst` | Full optimality proof: `lemma_greedy_choice`, `lemma_greedy_is_optimal`, `theorem_implementation_optimal` | 0 |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst` | Loop invariant definitions, `greedy_selection_inv`, `lemma_greedy_choice_seq` | 0 |
| `CLRS.Ch16.ActivitySelection.Lemmas.fsti` | Predicate interfaces: `finish_sorted`, `pairwise_compatible`, `earliest_compatible` | 0 |
| `CLRS.Ch16.ActivitySelection.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch16.ActivitySelection.Impl.fsti` | Public API: `activity_selection` signature | 0 |
| `CLRS.Ch16.ActivitySelection.Complexity.fst` | Complexity bound definition | 0 |
| `CLRS.Ch16.ActivitySelection.Complexity.fsti` | `complexity_bounded_linear` | 0 |

### Huffman Coding

| File | Role | Admits |
|---|---|---|
| `CLRS.Ch16.Huffman.Spec.fst` | htree type, WPL, cost, `wpl_equals_cost`, `huffman_from_sorted`, `is_wpl_optimal` | 0 |
| `CLRS.Ch16.Huffman.Complete.fst` | Full CLRS HUFFMAN with sorted-list PQ, `huffman_complete_optimal` | 0 |
| `CLRS.Ch16.Huffman.Optimality.fst` | Bridge: `greedy_cost` ↔ WPL optimality, `greedy_cost_implies_optimal` | 0 |
| `CLRS.Ch16.Huffman.Complexity.fst` | O(n²) bound: `huffman_ticks_bounded`, `huffman_complexity` | 0 |
| `CLRS.Ch16.Huffman.Complexity.fsti` | Complexity interface | 0 |
| `CLRS.Ch16.Huffman.Defs.fst` | Shared defs: PQ entries, forest entries, `seq_to_pos_list`, opaque bundles | 0 |
| `CLRS.Ch16.Huffman.PQLemmas.fst/.fsti` | PQ invariant preservation lemmas | 0 |
| `CLRS.Ch16.Huffman.ForestLemmas.fst/.fsti` | Forest–PQ structural lemmas | 0 |
| `CLRS.Ch16.Huffman.PQForest.fst/.fsti` | Opaque predicate intro/elim, bundle management | 0 |
| `CLRS.Ch16.Huffman.Impl.fst` | Pulse implementation (3 `assume_` for PQ) | 0 admits, 3 assumes |
| `CLRS.Ch16.Huffman.Impl.fsti` | Public API: `huffman_tree` signature, `is_htree` slprop | 0 |
| `CLRS.Ch16.Huffman.Codec.fst` | Pure encode/decode with round-trip proofs | 0 |
| `CLRS.Ch16.Huffman.Codec.fsti` | Codec interface: `encode`, `decode`, round-trip theorems | 0 |
| `CLRS.Ch16.Huffman.Codec.Impl.fst` | Pulse encode/decode | 0 |
| `CLRS.Ch16.Huffman.Codec.Impl.fsti` | Pulse codec interface: `encode_impl`, `decode_impl`, `codeword_impl` | 0 |
| `TestHuffman.fst` | Smoke test (CLRS Figure 16.3 frequencies) | 0 |

---

## Summary

| Algorithm | CLRS | Complexity | Proven | Linked | Admits | Assumes | Key Theorem |
|---|---|---|---|---|---|---|---|
| Activity Selection | §16.1 | O(n) | Tight (n−1) | ✅ | 0 | 0 | `count == max_compatible_count` |
| Huffman Coding | §16.3 | O(n²) sorted / O(n log n) heap | Upper bound | ❌ (pure) | 0 | 3 (PQ) | `is_wpl_optimal` |

---

## Building

```bash
cd /home/nswamy/ws2/AutoCLRS
make -C ch16-greedy
```

Requires `PULSE_ROOT` to be set (defaults to `../../pulse`).
