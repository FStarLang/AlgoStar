# Chapter 23: Minimum Spanning Trees — Kruskal & Prim

This directory contains verified implementations and specifications for MST algorithms from CLRS Chapter 23 in F* and Pulse.

## Files

| File | Lines | Language | Role |
|------|------:|---------|------|
| `CLRS.Ch23.MST.Spec.fsti` | 458 | F* | Cut-property interface + MST existence vals |
| `CLRS.Ch23.MST.Spec.fst` | 1 881 | F* | Full proofs including cut property (Theorem 23.1), MST existence (partial) |
| `CLRS.Ch23.MST.Complexity.fst` | 102 | F* | Arithmetic O(V³) Kruskal / O(V²) Prim bounds |
| `CLRS.Ch23.Kruskal.Spec.fst` | 2 951 | F* | Pure Kruskal: BFS components, insertion sort, `pure_kruskal`, MST theorem |
| `CLRS.Ch23.Kruskal.fst` | 340 | Pulse | Imperative Kruskal (adj-matrix, union-find) |
| `CLRS.Ch23.Kruskal.EdgeSorting.fst` | 339 | F* | sort_edges permutation and MST weight independence |
| `CLRS.Ch23.Kruskal.SortedEdges.fst` | 142 | F* | Kruskal over sorted input: subset/forest proven |
| `CLRS.Ch23.Kruskal.UF.fst` | 405 | F* | Union-find correctness: find_pure, soundness, completeness |
| `CLRS.Ch23.Kruskal.Helpers.fst` | 118 | F* | Forest invariant maintenance lemmas for Kruskal |
| `CLRS.Ch23.Kruskal.Complexity.fst` | 521 | Pulse | Ghost-tick instrumented Kruskal, proves ticks ≤ 4·V³ |
| `CLRS.Ch23.Prim.fst` | 401 | Pulse | Imperative Prim (adj-matrix, key + parent + in_mst arrays) |
| `CLRS.Ch23.Prim.Spec.fst` | 1 036 | F* | Pure Prim: adj-matrix, `pure_prim`, connectivity, safety via cut property |
| `CLRS.Ch23.Prim.Complexity.fst` | 433 | Pulse | Ghost-tick instrumented Prim, proves ticks ≤ 3·V² |

**Total**: ~9 500 lines across 13 source files.

## Verification Status

| Module | Admits | Status |
|--------|------:|--------|
| MST.Spec (.fst + .fsti) | 1 | ⚠️ `acyclic_count_lower_bound` admit (T5 counting lemma) |
| Kruskal.Spec.fst | 0 | ✅ Fully proven |
| Kruskal.fst (Pulse) | 1 `assume_` | ⚠️ Forest property assumed (line 315) |
| Kruskal.EdgeSorting.fst | 0 | ✅ |
| Kruskal.SortedEdges.fst | 0 | ✅ |
| Kruskal.UF.fst | 0 | ✅ Fully proven |
| Kruskal.Helpers.fst | 0 | ✅ Fully proven |
| Kruskal.Complexity.fst | 0 | ✅ |
| Prim.fst (Pulse) | 0 | ✅ Returns (key, parent) pair |
| Prim.Spec.fst | 0 | ✅ Fully proven |
| Prim.Complexity.fst | 0 | ✅ |
| MST.Complexity.fst | 0 | ✅ |

**2 admits** across ~9 500 lines. The `assume_` in Kruskal.fst (line ~320) assumes the imperative output forms a forest. The `admit()` in MST.Spec.fst is the counting induction for `acyclic_count_lower_bound`, needed to derive `acyclic + connected → n-1 edges`.

## Key Results

- **Cut Property (Theorem 23.1)**: Fully formalized and proven in MST.Spec
- **Kruskal MST correctness**: Proven in pure spec (`theorem_kruskal_produces_mst`)
- **Prim MST correctness**: Proven in pure spec (`prim_spec`)
- **Complexity**: Prim O(V²) matches CLRS adj-matrix variant; Kruskal O(V³) reflects V²-scan variant
- **MST Existence (partial)**: `reachable_implies_not_acyclic` and `acyclic_edge_disconnects` proven; `acyclic_connected_length` structure proven (1 admit in counting lemma)

## Building

```bash
cd ch23-mst
make          # verify all files
```

## Technical Notes

1. **Infinity Value**: Prim Pulse uses `65535sz` (SizeT constraint); Prim.Spec uses `1000000000`
2. **Matrix Indexing**: Flat array `weights[u*n+v]` with proven overflow safety when `n² < 2⁶⁴`
3. **Platform Requirement**: Requires 64-bit SizeT (`SZ.fits_u64`)
4. **Imperative gap**: Neither Pulse implementation connects its postcondition to the pure MST specification yet
