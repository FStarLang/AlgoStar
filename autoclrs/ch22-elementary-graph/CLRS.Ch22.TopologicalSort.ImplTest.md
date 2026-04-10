# CLRS.Ch22.TopologicalSort.ImplTest — Spec Validation Report

**Date:** 2026-03-17
**Status:** ✅ Verified (zero admits, zero assumes)
**Concrete Execution:** ✅ Extracted to C, compiled, and executed successfully (latest: 2026-04-10)

## Test Instance

3-vertex DAG with edges 0→1 and 1→2.

```
Adjacency matrix (flat 3×3):
  [0, 1, 0,   -- vertex 0: edge to 1
   0, 0, 1,   -- vertex 1: edge to 2
   0, 0, 0]   -- vertex 2: no edges
```

The only valid topological order for this graph is [0, 1, 2].

## What Is Proven

| Property | Proven? | Method |
|----------|---------|--------|
| Precondition satisfiable | ✅ | Concrete array setup, `assert_norm (SZ.fits 9)` |
| `~(has_cycle sadj 3)` (DAG precondition) | ✅ | Witness topological order + `lemma_topo_order_implies_dag` |
| Output length == n | ✅ | Direct from postcondition |
| All output elements valid indices (< n) | ✅ | Postcondition universal ∀i |
| All output elements non-negative (≥ 0) | ✅ | Postcondition universal ∀i |
| All elements distinct | ✅ | `all_distinct (seq_int_to_nat sout)` from postcondition |
| Valid topological order | ✅ | `is_topological_order sadj n (seq_int_to_nat sout)` |
| Complexity bound (`cf ≤ n²`) | ✅ | Direct from postcondition |

### DAG Precondition Proof Strategy

The topological sort precondition requires `~(has_cycle sadj 3)`. This is
proven indirectly using a theorem from `TopologicalSort.Spec.fst`:

1. **Construct witness order:** `test_order = [0, 1, 2]`
2. **Prove it's valid:** `is_topological_order test_adj 3 test_order`
   - Enumerate all edges: only (0,1) and (1,2)
   - Verify `appears_before` for each edge via `position_in_order`
   - Verify no other edges exist via `assert_norm`
3. **Apply theorem:** `lemma_topo_order_implies_dag test_adj 3 test_order`
   → `is_dag test_adj 3` → `~(has_cycle test_adj 3)`
4. **Connect to ghost state:** `lemma_seq_eq_test_adj sadj` proves
   `sadj == test_adj`, giving `~(has_cycle sadj 3)`

### Postcondition Strength Analysis

The TopologicalSort postcondition is **strong**:
- Valid indices + non-negative + distinct + length n → output is a permutation of {0,...,n-1}
- Topological order constraint → edges respected

For this specific graph (unique topological order), the postcondition
**could** in principle determine the exact output [0,1,2], though the
combinatorial argument is complex.

## What Is NOT Proven

| Property | Status | Reason |
|----------|--------|--------|
| Exact output `== [0, 1, 2]` | ❌ | Requires combinatorial argument |

### Finding: Strong Spec, Minor Precision Gap

Unlike BFS and DFS, the TopologicalSort specification chain is complete:
`Spec → Lemmas → Verified → Impl.Defs → Impl`. The postcondition exposes
all key properties:
- Valid topological order
- Distinct elements
- All valid vertices

The only gap is that the postcondition doesn't uniquely determine the output
when multiple valid topological orders exist. For our test graph (linear chain),
the order IS unique, but proving this requires showing that the topological
constraints combined with distinctness force a unique permutation.

**Impact:** Minor. The postcondition is precise enough for all practical
uses of topological sort.

## Concrete Execution Results (2026-03-22)

The topological sort test was extracted to C via KaRaMeL and executed:

```
$ make test
Ch22 ImplTest: running BFS, DFS, TopologicalSort tests...
Ch22 ImplTest: all tests passed.
```

The extracted C code:
- Allocates adjacency matrix
- Sets edges 0→1 and 1→2 in the adjacency matrix (a DAG)
- Calls `topological_sort` (the verified Kahn's algorithm implementation)
- Frees allocated memory
- Completes without errors, confirming the verified algorithm runs correctly on concrete data
