# Chapter 35: Approximation Algorithms — Rubric Compliance

## Current File Inventory

| # | File | Lines | Status | Description |
|---|------|------:|--------|-------------|
| 1 | `CLRS.Ch35.VertexCover.Spec.fst` | 451 | ✅ Verified | Pure specification + CLRS Theorem 35.1 proof |
| 2 | `CLRS.Ch35.VertexCover.fst` | 347 | ✅ Verified | Pulse implementation of APPROX-VERTEX-COVER |

**Total: 2 files, 798 lines. 0 admits, 0 assumes.**

## Algorithms Covered

### Vertex Cover 2-Approximation (CLRS §35.1, pp. 1108–1109)

The implementation is a faithful deterministic realisation of APPROX-VERTEX-COVER.
It scans edges in lexicographic `(u, v)` order (upper-triangular, `u < v`), adds both
endpoints of an uncovered edge to the cover, and tracks the matching as ghost state.

**Proven properties:**
- Valid cover: every edge has ≥1 endpoint in the cover (`is_cover`)
- Binary output: all cover values are 0 or 1
- 2-approximation: `|C| ≤ 2 · OPT` via `approximation_ratio_theorem`
- Memory safety: separation-logic framing via Pulse `pts_to`

## Rubric Compliance Matrix

The canonical rubric requires **7 files** per algorithm. Current status for `VertexCover`:

| Required File | Rubric Role | Exists? | Notes |
|---------------|-------------|---------|-------|
| `CLRS.Ch35.VertexCover.Spec.fst` | Pure F* specification | ✅ | 451 lines; types, counting lemmas, Theorem 35.1, bridge to Pulse |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | Proofs of correctness lemmas | ❌ Missing | Lemmas are currently inlined in `Spec.fst` and `VertexCover.fst` |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | Interface for lemma signatures | ❌ Missing | — |
| `CLRS.Ch35.VertexCover.Complexity.fst` | Complexity proofs | ❌ Missing | Trivial O(V²) bound exists inline (lines 361–366 per audit) but source file absent; stale `.checked` in `_cache/` |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | Interface for complexity definitions | ❌ Missing | — |
| `CLRS.Ch35.VertexCover.Impl.fst` | Pulse implementation | 🔶 Exists as `VertexCover.fst` | File name is `CLRS.Ch35.VertexCover.fst`, not `*.Impl.fst` per rubric |
| `CLRS.Ch35.VertexCover.Impl.fsti` | Public signature for implementation | ❌ Missing | — |

**Compliance: 1/7 fully conforming, 1/7 partial (wrong name), 5/7 missing.**

## Detailed Action Items

### P0 — Structural compliance (bring to rubric shape)

1. **Create `CLRS.Ch35.VertexCover.Lemmas.fst`**
   Extract the ~20 pure lemmas currently in `Spec.fst` (e.g., `count_cover_ext`, `count_split`,
   `matching_lower_bound`, `matching_cover_size`, `theorem_35_1`, `pulse_cover_is_valid`,
   `approximation_ratio_theorem`) into a dedicated Lemmas module. `Spec.fst` should retain
   only type definitions, `extract_edges`, `min_vertex_cover_size`, and helper predicates.

2. **Create `CLRS.Ch35.VertexCover.Lemmas.fsti`**
   Expose signatures for key lemmas: `theorem_35_1`, `approximation_ratio_theorem`,
   `pulse_cover_is_valid`, `matching_lower_bound`, `matching_cover_size`.

3. **Create `CLRS.Ch35.VertexCover.Complexity.fst`**
   Formalize the O(V²) time bound connected to the actual nested-loop structure.
   Current trivial inline bound (`v*v ≤ v*v`) is disconnected from the code.

4. **Create `CLRS.Ch35.VertexCover.Complexity.fsti`**
   Define `vertex_cover_time_bound` and expose the complexity lemma signature.

5. **Rename or create `CLRS.Ch35.VertexCover.Impl.fst`**
   The current `CLRS.Ch35.VertexCover.fst` serves as the implementation. Either rename it
   to `CLRS.Ch35.VertexCover.Impl.fst` or create a thin wrapper that re-exports.

6. **Create `CLRS.Ch35.VertexCover.Impl.fsti`**
   Extract the public signature of `approx_vertex_cover` (lines 166–189 of current `.fst`)
   into an `.fsti` interface file.

### P1 — Correctness & quality fixes

7. **Remove dead lemma `cover_values_are_binary`** (VertexCover.fst, if present) — precondition restates conclusion.

8. **Add undirected-graph precondition** — explicitly require `adj[u*n+v] = adj[v*n+u]` or document the upper-triangular convention as a precondition on `approx_vertex_cover`.

9. **Relax `n < 256` constraint** — replace with `SZ.fits (SZ.v n * SZ.v n)` to support larger graphs. (Current code already requires `SZ.fits (SZ.v n * SZ.v n)` but the 256 limit may be an artifact.)

10. **Clean stale cache entry** — delete `_cache/CLRS.Ch35.VertexCover.Complexity.fst.checked` (source file does not exist).

### P2 — Documentation

11. **Fix README.md** — remove references to 5 nonexistent files (`Complexity.fst`, `Test.fst`, `P2.7_SUMMARY.md`, `P2.7_API.md`, `P2.7_COMPLETE.md`) and `verify_all.sh`.

### Deferred — Additional Ch35 algorithms

| CLRS Section | Algorithm | Priority | Difficulty |
|--------------|-----------|----------|------------|
| §35.2 | APPROX-TSP-TOUR (2-approx TSP) | Low | Hard (needs Ch23 MST + Euler tour) |
| §35.3 | GREEDY-SET-COVER (H(n)-approx) | Medium | Medium |
| §35.4 | MAX-3-CNF randomised (8/7-approx) | Low | Medium (probabilistic reasoning) |
| §35.4 | LP-relaxation vertex cover (2-approx) | Low | Hard (needs Ch29 LP infra) |
| §35.5 | APPROX-SUBSET-SUM (FPTAS) | Low | Medium |

## Quality Checks

| Dimension | Status | Detail |
|-----------|--------|--------|
| **Zero admits** | ✅ | Confirmed: 0 `admit()` in both files |
| **Zero assumes** | ✅ | Confirmed: 0 `assume` in both files |
| **Verified** | ✅ | Both `.checked` files present in `_cache/` |
| **Solver limits** | ✅ | Modest: `--z3rlimit 30` and `--z3rlimit 40` only |
| **CLRS fidelity** | ✅ | Faithful to APPROX-VERTEX-COVER pseudocode |
| **Spec strength** | ✅ | All 3 key properties proven (valid cover, binary, 2-approx) |
| **Rubric file structure** | ❌ | 5 of 7 required files missing; 1 misnamed |
| **Complexity proof** | ❌ | No standalone complexity file; inline bound is trivial |
| **Documentation** | 🔶 | In-code docs excellent; README has 6 phantom references |
