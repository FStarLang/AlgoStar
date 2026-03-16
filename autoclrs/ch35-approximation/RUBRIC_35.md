# Chapter 35: Approximation Algorithms — Rubric Compliance

**Last updated**: 2026-03-16

## Current File Inventory

| # | File | Lines | Status | Description |
|---|------|------:|--------|-------------|
| 1 | `CLRS.Ch35.VertexCover.Spec.fst` | 105 | ✅ Verified | Pure specification: types, graph predicates, counting functions |
| 2 | `CLRS.Ch35.VertexCover.Lemmas.fsti` | 122 | ✅ Verified | Interface for lemma signatures |
| 3 | `CLRS.Ch35.VertexCover.Lemmas.fst` | 383 | ✅ Verified | Proofs: counting lemmas, Theorem 35.1, approximation ratio |
| 4 | `CLRS.Ch35.VertexCover.Complexity.fsti` | 41 | ✅ Verified | Interface for complexity definitions |
| 5 | `CLRS.Ch35.VertexCover.Complexity.fst` | 58 | ✅ Verified | O(V²) time bound proof |
| 6 | `CLRS.Ch35.VertexCover.Impl.fsti` | 48 | ✅ Verified | Public signature for Pulse implementation |
| 7 | `CLRS.Ch35.VertexCover.Impl.fst` | 358 | ✅ Verified | Pulse implementation with correctness proof |

**Total: 7 files, 1115 lines. 0 admits, 0 assumes. ~48s clean verification.**

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
| `CLRS.Ch35.VertexCover.Spec.fst` | Pure F* specification | ✅ | Types, counting functions, graph predicates |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | Proofs of correctness lemmas | ✅ | Counting lemmas, Theorem 35.1, approximation ratio |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | Interface for lemma signatures | ✅ | Key lemma signatures exposed |
| `CLRS.Ch35.VertexCover.Complexity.fst` | Complexity proofs | ✅ | O(V²) time bound proven |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | Interface for complexity definitions | ✅ | `vertex_cover_iterations` and `vertex_cover_quadratic` |
| `CLRS.Ch35.VertexCover.Impl.fst` | Pulse implementation | ✅ | Full Pulse implementation with correctness proof |
| `CLRS.Ch35.VertexCover.Impl.fsti` | Public signature for implementation | ✅ | Public signature of `approx_vertex_cover` |

**Compliance: 7/7 fully conforming.**

## Detailed Action Items

### P0 — Structural compliance (bring to rubric shape)

1. ~~**Create `CLRS.Ch35.VertexCover.Lemmas.fst`**~~ ✅ Done
   Extracted ~20 pure lemmas from `Spec.fst` into dedicated Lemmas module.

2. ~~**Create `CLRS.Ch35.VertexCover.Lemmas.fsti`**~~ ✅ Done
   Exposes signatures for key lemmas: `theorem_35_1`, `approximation_ratio_theorem`,
   `pulse_cover_is_valid`, `matching_lower_bound`, `matching_cover_size`.

3. ~~**Create `CLRS.Ch35.VertexCover.Complexity.fst`**~~ ✅ Done
   Defines `vertex_cover_iterations` as v*(v-1)/2 and proves O(V²) bound.

4. ~~**Create `CLRS.Ch35.VertexCover.Complexity.fsti`**~~ ✅ Done
   Defines `vertex_cover_time_bound` and exposes the complexity lemma signature.

5. ~~**Rename or create `CLRS.Ch35.VertexCover.Impl.fst`**~~ ✅ Done
   Renamed from `CLRS.Ch35.VertexCover.fst` to `CLRS.Ch35.VertexCover.Impl.fst`.
   Uses `Spec.is_cover` and imports `Lemmas`.

6. ~~**Create `CLRS.Ch35.VertexCover.Impl.fsti`**~~ ✅ Done
   Public signature of `approx_vertex_cover` exposed.

### P1 — Correctness & quality fixes

7. ~~**Remove dead lemma `cover_values_are_binary`**~~ ✅ Already removed (not present in code)

8. **Add undirected-graph precondition** — documented in Impl.fst header comment; not added as a formal precondition to avoid breaking the existing API.

9. ~~**Relax `n < 256` constraint**~~ ✅ Already uses `SZ.fits (SZ.v n * SZ.v n)` (no 256 limit present)

10. ~~**Clean stale cache entry**~~ ✅ Done. All old `.checked` files removed; fresh verification passed.

### P2 — Documentation

11. ~~**Fix README.md**~~ ✅ Done. Removed all phantom file references. Updated file list to match rubric structure.

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
| **Zero admits** | ✅ | Confirmed: 0 `admit()` in all files |
| **Zero assumes** | ✅ | Confirmed: 0 `assume` in all files |
| **Verified** | ✅ | All 7 `.checked` files produced; ~48s clean build |
| **Solver limits** | ✅ | Modest: `--z3rlimit 30` and `--z3rlimit 40` only |
| **CLRS fidelity** | ✅ | Faithful to APPROX-VERTEX-COVER pseudocode |
| **Spec strength** | ✅ | All 5 key properties proven (length, valid cover, binary, min exists, 2-approx) |
| **Rubric file structure** | ✅ | 7 of 7 required files present and verified |
| **Complexity proof** | ✅ | Standalone complexity file with O(V²) bound linked via ghost counter |
| **Documentation** | ✅ | README accurate, Review.md comprehensive |
| **Proof stability** | ✅ | No z3refresh, no retry, no fuel/ifuel adjustments |
