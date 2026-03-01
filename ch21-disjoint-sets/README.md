# Chapter 21 — Disjoint Sets (Union-Find)

Verified implementation of CLRS Chapter 21 union-by-rank with full path compression.

## Module Structure

| Module | Description |
|---|---|
| `CLRS.Ch21.UnionFind.Spec` | Pure F\* specification: total `pure_find`, `pure_union`, partition correctness proofs |
| `CLRS.Ch21.UnionFind` | Pulse imperative implementation: `make_set`, `find_set` (full compression), `union` (returns unit) |
| `CLRS.Ch21.UnionFind.RankBound` | Proof that `size ≥ 2^rank` and `rank ≤ ⌊log₂ n⌋`, tree height ≤ rank |

## Key Properties Proven

### Specification (`Spec.fst`)
- **Total `pure_find`**: No fuel, no Option — terminates via `count_above` measure
- **`pure_union_same_set`**: After `union(x,y)`, `find(x) == find(y)` (merge correctness)
- **`pure_union_other_set`**: Unrelated elements are unchanged (stability)
- **`pure_union_preserves_inv`**: Invariant preservation

### Implementation (`UnionFind.fst`)
- **`make_set`**: Postcondition includes `Spec.uf_inv` on the pure spec bridge
- **`find_set`**: Two-pass full CLRS path compression (find root, then compress)
- **`union`**: Union by rank, returns unit (not tuple)
- All operations preserve `is_forest` (acyclicity)

### Rank Bound (`RankBound.fst`)
- Tree height ≤ rank\[root\] ≤ ⌊log₂ n⌋
- Logarithmic worst-case find complexity

## CLRS Section Mapping

| CLRS Section | Content | Module |
|---|---|---|
| §21.1 | Disjoint-set operations | `Spec.fst` (pure model) |
| §21.2 | Linked-list representation | Not implemented (array-based instead) |
| §21.3 | Disjoint-set forests | `UnionFind.fst` |
| §21.3 | MAKE-SET | `make_set` in `UnionFind.fst` |
| §21.3 | FIND-SET (with compression) | `find_set` in `UnionFind.fst` |
| §21.3 | UNION / LINK | `union` in `UnionFind.fst` |
| Lemma 21.4 | rank\[x\] < rank\[parent\[x\]\] | `Spec.fst` (`rank_invariant`) |
| Theorem 21.5 | rank ≤ ⌊log₂ n⌋ | `RankBound.fst` §4-6 |
| §21.4 | Amortised O(α(n)) | Not implemented |

## Verification

All modules verify with zero admits and zero assumes.

```bash
# From ch21-disjoint-sets/
make    # Uses Pulse test.mk
```
