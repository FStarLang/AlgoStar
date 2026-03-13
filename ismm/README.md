# ISMM: Verified Implementation of "Reference Counting Deeply Immutable Data Structures with Cycles"

A formally verified implementation in [Pulse/F\*](https://github.com/FStarLang/pulse) of the memory management algorithm from:

> **Matthew J. Parkinson, Sylvan Clebsch, and Tobias Wrigstad.**
> "Reference Counting Deeply Immutable Data Structures with Cycles: an Intellectual Abstract."
> *ISMM '24*, June 2024, Copenhagen, Denmark.
> DOI: [10.1145/3652024.3665507](https://doi.org/10.1145/3652024.3665507)

## Overview

The paper presents an algorithm for managing memory of deeply immutable, possibly cyclic
data structures using reference counting at the level of strongly connected components (SCCs).
The key insight is that since the graph is immutable after freezing, its SCCs can be computed
once and used to factor the graph into an acyclic DAG of SCCs, enabling standard reference
counting without a backup garbage collector or cycle detector.

This implementation provides:

- **5,170 lines** of verified Pulse/F\* across **30 modules**
- **Zero semantic assumes** — all correctness properties fully proved
- **All 30 files verified** in a clean parallel build (~7 minutes)
- Proofs of CLRS Lemma 21.4 (rank boundedness via size-rank invariant)
- Union-find with path compression and union-by-rank, fully verified
- Complete implementations of freeze, dispose, acquire, and release

## Paper Algorithm Summary

### Node Status (4 states, Fig. 2)

Each node carries a status field with one of four states:

| Status | Tag | Meaning |
|--------|-----|---------|
| `UNMARKED` | 0 | Not yet visited by freeze |
| `RANK(n)` | 1 | On pending stack during freeze; UF rank = n |
| `REP(ptr)` | 2 | UF non-root; representative reachable via ptr |
| `RC(n)` | 3 | SCC representative with external reference count n |

### Three Core Operations (§3)

1. **`freeze(root)`** (§3.1, Fig. 2) — DFS over the reachable graph; computes SCCs via
   Purdom's path-based algorithm fused with union-find; assigns each SCC an initial
   external reference count.

2. **`dispose(rep)`** (§3.2, Fig. 4) — Deallocates all nodes in an SCC whose RC hit 0;
   cascades decrements to child SCCs, potentially triggering their disposal recursively.
   Uses three stacks: `dfs` (DAG traversal), `scc` (intra-SCC traversal), `free_list`.

3. **`acquire(r)` / `release(r)`** (§3.3) — Increment/decrement the SCC-level reference
   count via `find(r)`; release triggers `dispose` when RC reaches 0.

### Complexity

- Freeze: O(|E| · α(|N|)) — almost linear
- Dispose: O(|E| · α(|N|)) — almost linear
- Acquire/Release: O(α(|N|)) — almost constant (amortized)

## Implementation Architecture

### Data Representation

The paper's single `status` field is split into parallel arrays for Pulse compatibility:

```
tag[i]:       int    — status discriminant (0=UNMARKED, 1=RANK, 2=REP, 3=RC)
parent[i]:    SZ.t   — UF parent pointer (self for roots)
rank[i]:      SZ.t   — UF rank (doubles as RC data for RC-tagged nodes)
adj[i*n+j]:   SZ.t   — flat adjacency matrix
refcount[i]:  SZ.t   — external reference count (for RC-tagged nodes)
```

The abstract specification uses `uf_state = { n: nat; tag: seq int; parent: seq nat; rank: seq nat }`.

### Module Organization

The implementation follows a layered **Spec → Lemmas → Impl** pattern:

#### Foundation Layer

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.Status` | 55 | 4-state tag constants and predicates |
| `ISMM.Graph` | 71 | Adjacency matrix, k-step reachability, SCC equivalence |
| `ISMM.Arith.Lemmas` | 309 | Arithmetic lemmas for matrix indexing (`i*n+j < n*n`) |
| `ISMM.Count` | 197 | Counting occurrences of tag values in sequences |

#### Union-Find (core data structure)

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.UnionFind.Spec` | 345 | **Central spec**: `uf_state`, `uf_inv`, `pure_find`, `pure_union`, rank bound proof |
| `ISMM.UnionFind.Union` | 123 | `pure_union` correctness, stability, and tag preservation lemmas |
| `ISMM.UnionFind.Compress` | 114 | Path compression preserves `uf_inv` and `pure_find` for all nodes |
| `ISMM.UF.SizeRank` | 129 | CLRS Lemma 21.4: `pure_union` preserves size-rank invariant |
| `ISMM.UF.Lemmas` | 127 | Bridge lemmas: tag updates and no-op writes preserve `uf_inv` |
| `ISMM.UnionFind.Impl` (.fsti+.fst) | 706+169 | Pulse implementation: `find_impl`, `union_impl`, `make_set` |

#### Freeze (SCC computation + initial RC assignment)

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.Freeze.Spec` | 103 | Postcondition predicates: tags, reachability, SCC correctness |
| `ISMM.Freeze.Impl` (.fsti+.fst) | 87+705 | Pulse `freeze_inner` loop + `freeze` wrapper |

#### Dispose (cascade deallocation)

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.Dispose.Spec` | 61 | `dispose_post`: freed SCCs, preserved others |
| `ISMM.Dispose.Impl` (.fsti+.fst) | 87+102 | Top-level `dispose`: alloc stacks, setup, loop, free |
| `ISMM.Dispose.Setup` (.fsti+.fst) | 87+106 | Push initial rep to DFS stack, mark PROCESSING |
| `ISMM.Dispose.Loop` (.fsti+.fst) | 97+155 | Main DFS loop over SCC DAG |
| `ISMM.Dispose.ProcessSCC` (.fsti+.fst) | 103+192 | Process a single SCC: collect nodes, examine edges |
| `ISMM.Dispose.Inner` (.fsti+.fst) | 109+172 | Inner loop: traverse adjacency row for one node |
| `ISMM.Dispose.Helpers` | 296 | Pure lemmas for dispose invariant maintenance |

#### Reference Counting (acquire/release)

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.RefCount.Spec` | 32 | `acquire_post`, `release_post` |
| `ISMM.RefCount.Impl` (.fsti+.fst) | 117+165 | Pulse `acquire`, `release` with find + incref/decref |

#### Test

| Module | Lines | Description |
|--------|-------|-------------|
| `ISMM.Test` | 49 | Allocation + make_set + freeze + dispose integration test |

## Verified Properties

### Union-Find Invariants

1. **`uf_inv_base`** — Structural well-formedness:
   - All parent pointers are in-bounds (`parent[i] < n`)
   - Tags are valid (0–3)
   - **Rank invariant**: rank strictly increases along parent edges
     (`parent[x] ≠ x ⟹ rank[x] < rank[parent[x]]`)

2. **`size_rank_inv`** (CLRS Lemma 21.4) — For every root `r`:
   ```
   comp_count(r) ≥ 2^rank(r)
   ```
   where `comp_count(r)` is the number of nodes whose `pure_find` equals `r`.

3. **`uf_inv = uf_inv_base ∧ size_rank_inv`** — Full invariant.

4. **Rank boundedness** — Derived from size-rank invariant:
   ```
   rank[i] < n   for all i
   ```
   Proof chain: `rank < pow2(rank) ≤ comp_count ≤ n`.

### Union-Find Operations

5. **`pure_find` totality** — Terminates under `uf_inv_base` (measure: count of nodes
   with rank above current rank).

6. **`pure_find` is idempotent and finds a root** — `pure_find(s, pure_find(s, x)) = pure_find(s, x)`
   and `parent[pure_find(s, x)] = pure_find(s, x)`.

7. **`pure_union` correctness** — After `union(x, y)`: `pure_find(x) = pure_find(y)`.

8. **`pure_union` stability** — Union does not merge unrelated equivalence classes.

9. **`pure_union` preserves `uf_inv`** — Including the size-rank invariant (via `ISMM.UF.SizeRank`).

10. **Path compression preserves `uf_inv` and `pure_find`** — For all nodes, not just the
    compressed path.

### Extensionality Lemmas (for invariant propagation)

11. **`pure_find_ext`** — If two states agree on parent, rank, and n, `pure_find` gives
    identical results. Used for tag-only updates.

12. **`comp_count_find_ext`** — If `pure_find` agrees on all nodes, `comp_count` agrees.
    Used for compression (which changes parent but preserves `pure_find`).

13. **`size_rank_inv_tag_ext`** — Tag-only changes preserve `size_rank_inv`.

14. **`size_rank_inv_find_ext`** — If `pure_find` is preserved and roots are preserved,
    `size_rank_inv` is preserved. Used for compression.

### Freeze Properties

15. **Tags correctness** — All reachable nodes become REP or RC; unreachable stay UNMARKED.

16. **SCC representatives** — Every reachable node's UF representative is RC-tagged.

17. **UF invariant maintained** through all freeze operations (find, union, tag updates).

### Dispose Properties

18. **SCC freed** — All nodes in the disposed SCC are set to UNMARKED (freed).

19. **Others preserved** — Nodes outside the disposed SCC retain their tags (or are
    cascaded-freed if their RC reaches 0).

20. **UF invariant maintained** through dispose (forest structure preserved).

21. **RC-positive invariant** — After dispose, all RC-tagged nodes have positive refcount.

### Reference Counting

22. **Acquire** — Increments the SCC representative's refcount; preserves all other state.

23. **Release** — Decrements the SCC representative's refcount; triggers dispose if RC=0.

## Comparison with Paper

### What is implemented

| Paper Section | Status | Notes |
|---------------|--------|-------|
| §2.1 Union-Find | ✅ Fully verified | Find with path compression, union by rank |
| §2.2 SCC definition | ✅ Specified | `scc_equiv` via mutual reachability |
| §3.1 Freeze (Fig. 2) | ✅ Implemented | Purdom's path-based SCC + union-find fusion |
| §3.2 Dispose (Fig. 4) | ✅ Implemented | Three-stack algorithm (dfs, scc, free_list) |
| §3.3 Acquire/Release | ✅ Implemented | Standard incref/decref via find |
| §4 Correctness invariant | ✅ Verified | "RC nodes only reach RC nodes" |
| §4 CLRS Lemma 21.4 | ✅ Proved | Size-rank invariant, rank < n |
| §5 Complexity analysis | ❌ Not formalized | User directive: no complexity formalization |

### Design differences from the paper

1. **Parallel arrays vs. single status field** — The paper uses a single polymorphic
   `status` field per node. Our implementation uses separate `tag`, `parent`, `rank`,
   and `refcount` arrays. This avoids the problem where converting a RANK root to REP
   destroys rank information needed by children in the UF forest.

2. **Adjacency matrix** — The paper is abstract about graph representation. We use a flat
   adjacency matrix (`adj[u*n+j]`) following the CLRS-style convention used in the
   `autoclrs/` companion codebase.

3. **Iterative vs. recursive freeze** — The paper presents `freeze_inner` as recursive.
   Our Pulse implementation uses explicit stack-based iteration (necessary for
   verified low-level code without general recursion).

4. **Dispose decomposition** — The paper presents dispose as a single function. We
   decompose it into 6 modules (Setup, Loop, ProcessSCC, Inner, Helpers, Impl) for
   parallel verification and manageable proof obligations.

5. **Reference count in separate array** — The paper stores RC in the status field. We
   use a separate `refcount` array, allowing the `rank` array to remain purely a UF
   rank throughout the algorithm's lifetime.

### Remaining assumptions

Only **2 `assume_`** remain, both in `ISMM.Freeze.Impl.fst`:

```fstar
assume_ (pure (SZ.fits (SZ.v rc + 1)));   // line 292
assume_ (pure (SZ.fits (SZ.v rc + 1)));   // line 689
```

These assert that the reference count fits in a machine-sized integer (`SZ.t`).
This is a machine-arithmetic overflow guard, not a semantic property. Discharging
it would require either a global bound on in-degree (e.g., `max_edges < SZ.max_value`)
or a runtime check. Both are deferred by design.

**Zero semantic assumes remain.** All correctness properties of the union-find,
freeze, dispose, and reference counting algorithms are fully proved.

## Building

```bash
cd ismm
make -j4          # parallel build, ~7 minutes
make clean        # remove _cache/ and _output/
```

Requires:
- F\* from `../FStar/bin/fstar.exe` (submodule)
- Pulse from `../pulse/` (submodule, built against the same F\*)

## Relation to autoclrs/

This implementation adapts verified algorithms from the `autoclrs/` companion codebase:

- **Union-Find** — `autoclrs/ch21/` provides the CLRS Chapter 21 union-find with rank
  invariant and path compression. Our `ISMM.UnionFind.*` modules extend this with
  the 4-state tag encoding and the size-rank invariant proof.

- **Graph model** — `autoclrs/ch22/` provides DFS and graph representation conventions.
  Our `ISMM.Graph` adapts the flat adjacency matrix representation.

- **Proof patterns** — The Spec → Lemmas → Impl layering, ghost state threading, and
  SMT profiling techniques follow patterns established in the autoclrs codebase.
