# Chapter 21 — Disjoint Sets (Union-Find)

Verified implementation of CLRS Chapter 21: union by rank with full path
compression.  The formalization covers the pure forest model
(§21.1/§21.3), a Pulse imperative implementation with memory-safe
mutable arrays, termination proofs, compression correctness, and
rank-bound analysis establishing O(log n) worst-case find.

**Verification status:** All modules verify with **zero admits and zero
assumes**.

---

## Summary Table

| Property | Status | Notes |
|---|---|---|
| Functional correctness (`make_set`, `find_set`, `union`) | ✅ Fully proven | All postconditions reference `pure_find` |
| `uf_inv` preservation | ✅ Fully proven | Across all three operations and compression |
| `pure_find` totality | ✅ Proven | Via `count_above` measure — no fuel, no Option |
| Merge correctness (`pure_union_same_set`) | ✅ Proven | `find(x) == find(y)` after `union(x,y)` |
| Stability (`pure_union_other_set`) | ✅ Proven | Unrelated elements unchanged |
| Path compression preserves all finds | ✅ Proven | `compress_preserves_find_all` |
| `size ≥ 2^rank` | ✅ Proven | `size_rank_invariant` in Lemmas |
| `rank ≤ ⌊log₂ n⌋` | ✅ Proven | `rank_logarithmic_bound_sized` |
| Tree height ≤ rank[root] | ✅ Proven | `height_le_root_rank` |
| O(log n) worst-case find | ✅ Proven | `union_by_rank_logarithmic_find` |
| Amortized O(α(n)) (CLRS §21.4) | ❌ Not formalized | Inverse Ackermann analysis out of scope |
| Admits | **0** | |
| Assumes | **0** | |

---

## File Inventory

| File | Language | LOC | Role |
|---|---|---|---|
| `CLRS.Ch21.UnionFind.Spec.fst` | F* | ~376 | Pure specification: `uf_forest`, `pure_find` (total), `pure_union`, compression lemmas, merge/stability theorems |
| `CLRS.Ch21.UnionFind.Impl.fsti` | Pulse | ~151 | Public interface: `make_set`, `find_set`, `union` signatures with full postconditions |
| `CLRS.Ch21.UnionFind.Impl.fst` | Pulse | ~669 | Imperative implementation: two-pass find, union by rank, bridge lemmas (`to_uf`, `to_nat_seq`) |
| `CLRS.Ch21.UnionFind.Lemmas.fst` | F* | ~677 | Rank bounds: `size ≥ 2^rank`, `rank ≤ ⌊log₂ n⌋`, tree height ≤ rank, O(log n) find |

---

## Specification (`Spec.fst`)

### Forest Model

```fstar
type uf_forest = {
  parent: Seq.seq nat;
  rank: Seq.seq nat;
  n: nat;
}
```

A valid forest (`is_valid_uf`) requires `n > 0`, parent/rank sequences
of length `n`, and all parent pointers in bounds.  A root satisfies
`parent[i] = i`.  The rank invariant (CLRS Lemma 21.4) states that for
every non-root `x`, `rank[x] < rank[parent[x]]`.  The combined
invariant `uf_inv` is the conjunction of `is_valid_uf` and
`rank_invariant`.

### Total Pure Find

`pure_find` follows parent pointers to the root.  It is **total without
fuel** — termination is proved via a `count_above` measure that counts
nodes with rank strictly above the current node's rank.  Since the rank
invariant ensures rank strictly increases along parent pointers, this
count decreases at each recursive call.

Key properties:
- `pure_find_is_root`: result is always a valid root
- `pure_find_in_bounds`: result is in `[0, n)`
- `pure_find_idempotent`: `pure_find(pure_find(x)) == pure_find(x)`
- `pure_find_step`: for non-roots, `pure_find(x) == pure_find(parent[x])`

### Pure Union

`pure_union` implements union by rank (CLRS §21.3): attach the shorter
tree under the taller one; on equal rank, attach and increment the new
root's rank.

### Compression Lemmas

- `compress_preserves_uf_inv`: setting `parent[v] := pure_find(v)`
  preserves `uf_inv`
- `compress_preserves_find_all`: single-node compression preserves
  `pure_find` for **all** nodes simultaneously

### Correctness Theorems

- **`pure_union_same_set`**: After `union(x,y)`, `pure_find(x) == pure_find(y)`.
- **`pure_union_other_set`**: For any `z` whose representative differs from
  both `x` and `y`, `pure_find(z)` is unchanged.
- **`pure_union_stability`**: Universal quantifier version of stability.
- **`pure_union_preserves_inv`**: `uf_inv` maintained.

---

## Correctness Theorem — Implementation (`Impl.fsti`)

The Pulse interface exposes three operations.  All postconditions
reference the pure specification via the bridge function `to_uf`.

### `make_set`

```
fn make_set (parent rank: array SZ.t) (#sparent #srank: Ghost.erased ...) (n: SZ.t)
  requires A.pts_to parent sparent ** A.pts_to rank srank ** pure (...)
  ensures  exists* sp sr.
    A.pts_to parent sp ** A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      (forall idx. idx < n ==> is_root_at sp idx) /\
      (forall idx. idx < n ==> rank[idx] == 0)
    )
```

Initializes an `n`-element forest where each element is its own root
with rank 0.

### `find_set`

```
fn find_set (parent: array SZ.t) (x n: SZ.t) (...)
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      root == Spec.pure_find(original, x) /\
      is_forest sp n /\ Spec.uf_inv(to_uf sp srank n) /\
      parent[x] == root /\ parent[root] == root /\
      ∀z < n. pure_find(compressed, z) == pure_find(original, z)
    )
```

Two-pass CLRS path compression:
1. **Pass 1** (`find_root_imp`): Read-only traversal to locate the root.
2. **Pass 2** (`compress_path`): Set every node on the path to point
   directly to the root.

**Postcondition analysis:**
- `root == pure_find(original, x)` — functional correctness
- `∀z. pure_find(compressed, z) == pure_find(original, z)` — compression
  does not change any element's representative
- `uf_inv` preserved — invariant maintenance
- `is_forest` preserved — acyclicity

### `union`

```
fn union (parent rank: array SZ.t) (...) (x y n: SZ.t)
  ensures exists* sp sr.
    A.pts_to parent sp ** A.pts_to rank sr **
    pure (
      is_forest sp n /\ Spec.uf_inv(to_uf sp sr n) /\
      pure_find(result, x) == pure_find(result, y) /\
      ∀z < n.
        pure_find(orig, z) <> pure_find(orig, x) ==>
        pure_find(orig, z) <> pure_find(orig, y) ==>
        pure_find(result, z) == pure_find(orig, z)
    )
```

Union by rank.  Uses `find_root_imp` (read-only) for both operands,
then links roots by rank.

**Postcondition analysis:**
- **Merge**: `pure_find(result, x) == pure_find(result, y)` — the two
  elements share the same representative after union.
- **Stability**: any element `z` whose original representative differs
  from both `x`'s and `y`'s retains its original representative.
- `uf_inv` and `is_forest` preserved.

### Why This Is the Strongest Functional Guarantee

The postconditions fully characterize union-find semantics:
1. Find returns the **exact** pure representative (not just "some root").
2. Compression preserves **all** representatives, not just the queried one.
3. Union's stability clause covers **all** disjoint elements.
4. The invariant `uf_inv` (rank invariant + validity) is maintained
   through every operation, enabling composition.

The only missing guarantee is amortized complexity (see Limitations).

### Bridge: `to_uf`

The bridge function converts imperative `SZ.t` arrays to the pure
`Spec.uf_forest`:

```fstar
let to_uf (parent rank: Seq.seq SZ.t) (n: nat) : Spec.uf_forest =
  { Spec.parent = to_nat_seq parent n;
    Spec.rank = to_nat_seq rank n;
    Spec.n = n }
```

---

## Rank Bound Analysis (`Lemmas.fst`)

### Size ≥ 2^Rank

The module introduces `uf_forest_sized` extending the forest with
subtree sizes.  The key invariant:

```fstar
let size_rank_invariant (f: uf_forest_sized) : prop =
  is_valid_uf_sized f ==>
  (forall (x: nat{x < f.n}).
    Seq.index f.size x >= pow2 (Seq.index f.rank x))
```

Preservation under union is proved case-by-case:
- **rank_x < rank_y**: merged size ≥ 2^rank_y (trivially, since size_y
  already ≥ 2^rank_y)
- **rank_x > rank_y**: symmetric
- **rank_x = rank_y**: merged size ≥ 2^rank_x + 2^rank_x = 2^(rank_x+1)

### Rank ≤ ⌊log₂ n⌋

Since `2^rank ≤ size ≤ n`, we get `rank ≤ ⌊log₂ n⌋`
(`rank_logarithmic_bound_sized`).

### Tree Height ≤ Rank

`height_plus_rank_le_root_rank_fuel` proves that for any node `x`:
```
path_length(x, root) + rank[x] ≤ rank[root]
```
Since `rank[x] ≥ 0`, this gives `height(x) ≤ rank[root] ≤ ⌊log₂ n⌋`.

### Summary Theorem

```fstar
let union_by_rank_logarithmic_find
  (f: uf_forest_sized{...}) (x: nat{x < f.n})
  : Lemma (ensures tree_height f x <= log2_floor f.n)
```

---

## Complexity

| Aspect | Proven | Bound |
|---|---|---|
| Worst-case find (union-by-rank only) | ✅ | O(log n) — `tree_height ≤ ⌊log₂ n⌋` |
| Amortized find (rank + compression) | ❌ | O(α(n)) — not formalized |
| Ghost tick counter | N/A | No complexity instrumentation file |

The O(log n) bound is for worst-case find **without** path compression.
With both union-by-rank and path compression, the amortized cost is
O(m · α(n)) where α is the inverse Ackermann function (CLRS Theorem
21.14).  **The amortized analysis is not formalized.**

---

## Limitations

1. **Amortized O(α(n)) not proven.** The inverse Ackermann amortized
   analysis (CLRS §21.4) is not formalized.  Only the O(log n)
   worst-case bound from union-by-rank is proven.

2. **No ghost tick counter.** Unlike other chapters, there is no
   `Complexity.fst` module with instrumented ghost ticks.  The O(log n)
   bound is stated as a lemma on tree height, not as a runtime counter.

3. **Subtree sizes are specification-only.**  The `uf_forest_sized` type
   in `Lemmas.fst` is a proof device — the imperative code does not
   maintain size fields.  This is correct (union-by-rank does not need
   sizes at runtime), but means the size-rank invariant cannot be
   directly connected to the imperative state without additional
   bridging.

4. **Linked-list representation (§21.2) not implemented.** The
   formalization uses the array-based forest representation (§21.3) only.

---

## CLRS Section Mapping

| CLRS Section | Content | Module |
|---|---|---|
| §21.1 | Disjoint-set operations | `Spec.fst` (pure model) |
| §21.2 | Linked-list representation | Not implemented (array-based instead) |
| §21.3 | Disjoint-set forests | `Impl.fst` + `Impl.fsti` |
| §21.3 | MAKE-SET | `make_set` in `Impl` |
| §21.3 | FIND-SET (with compression) | `find_set` in `Impl` |
| §21.3 | UNION / LINK | `union` in `Impl` |
| Lemma 21.4 | rank[x] < rank[parent[x]] | `Spec.fst` (`rank_invariant`) |
| Theorem 21.5 | rank ≤ ⌊log₂ n⌋ | `Lemmas.fst` (`rank_logarithmic_bound_sized`) |
| §21.4 | Amortized O(α(n)) | Not implemented |

---

## Build Instructions

```bash
cd ch21-disjoint-sets/
make    # Verifies all modules via Pulse test.mk
```
