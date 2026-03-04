# Chapter 16: Greedy Algorithms — Verified in F*/Pulse

## Overview
This directory implements verified greedy algorithms from CLRS Chapter 16:
1. **Activity Selection** (§16.1) — GREEDY-ACTIVITY-SELECTOR
2. **Huffman Coding** (§16.3) — HUFFMAN

Both algorithms have **zero admits** and **zero assumes** across all source files.

---

## Activity Selection (CLRS §16.1)

### Algorithm
Given activities with start and finish times (sorted by finish time), the greedy
algorithm selects the maximum number of non-overlapping activities by always
choosing the earliest-finishing compatible activity.

### Key Results
- **Full optimality**: `count == max_compatible_count` proven end-to-end
- **Exact complexity**: n−1 comparisons (O(n) for presorted input)
- **Greedy choice property** (CLRS Theorem 16.1): proven via exchange argument
- **Optimal substructure**: proven
- **Dominance lemma**: greedy selection dominates any valid selection

### Files
| File | Role |
|------|------|
| `CLRS.Ch16.ActivitySelection.Spec.fst` | Full optimality proof |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst/.fsti` | Loop invariant definitions & lemmas |
| `CLRS.Ch16.ActivitySelection.Complexity.fst/.fsti` | Complexity bound definition |
| `CLRS.Ch16.ActivitySelection.Impl.fst/.fsti` | Pulse implementation |

### Postcondition
```fstar
SZ.v count == S.max_compatible_count ss sf (SZ.v n)
complexity_bounded_linear cf (reveal c0) (SZ.v n)  // exactly n-1 comparisons
```

---

## Huffman Coding (CLRS §16.3)

### Algorithm
Builds an optimal prefix-code tree by repeatedly merging the two lowest-frequency
subtrees using a priority queue. Three levels of implementation:

1. **`huffman_complete`** (Complete.fst) — Pure spec-level construction using
   sorted list as PQ; WPL-optimality fully proven.
2. **`huffman_tree`** (Huffman.Impl.fst) — Imperative Pulse implementation using
   `Pulse.Lib.PriorityQueue` (binary heap); postcondition includes `is_wpl_optimal`.

### Key Results
- **WPL-optimality**: proven for both spec and imperative implementations
- **Greedy choice** (CLRS Lemma 16.2): fully proven via exchange argument
- **Optimal substructure** (CLRS Lemma 16.3): WPL(T) = WPL(T') + f1 + f2
- **Frequency multiset preservation**: proven through construction
- **Complexity**: O(n²) proven for sorted-list variant

### Files
| File | Role |
|------|------|
| `CLRS.Ch16.Huffman.Spec.fst` | htree type, WPL, cost, greedy choice theorem |
| `CLRS.Ch16.Huffman.Complete.fst` | Spec-level construction + WPL optimality |
| `CLRS.Ch16.Huffman.Optimality.fst` | Bridge: greedy cost ↔ WPL |
| `CLRS.Ch16.Huffman.Complexity.fst/.fsti` | O(n²) complexity proof (sorted list) |
| `CLRS.Ch16.Huffman.Defs.fst` | Shared definitions for Impl |
| `CLRS.Ch16.Huffman.PQLemmas.fst/.fsti` | PQ invariant preservation lemmas |
| `CLRS.Ch16.Huffman.ForestLemmas.fst/.fsti` | Forest–PQ structural lemmas |
| `CLRS.Ch16.Huffman.PQForest.fst/.fsti` | Opaque predicate intro/elim |
| `CLRS.Ch16.Huffman.Impl.fst/.fsti` | Pulse imperative implementation |
| `TestHuffman.fst` | Smoke test (CLRS Figure 16.3 frequencies) |

### Postcondition (`huffman_tree`)
```fstar
HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)
```

---

## Building
```bash
cd /home/nswamy/ws2/AutoCLRS
make -C ch16-greedy
```

## Verification Status
- **All source files verified** (`.checked` caches present)
- **Zero admits** across all files
- **Zero assumes** across all files
