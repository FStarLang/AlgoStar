# Audit Report — Chapter 35: Approximation Algorithms (Vertex Cover)

**Date**: 2026-03-16 (updated from 2025-02-26)
**Scope**: `ch35-approximation/` — 7 files (1115 lines total)
**Verification**: All 7 `.checked` files produced, ~48s clean build
**Admits**: 0 | **Assumes**: 0

---

## 1. CLRS Fidelity — APPROX-VERTEX-COVER

### CLRS Pseudocode (p. 1108–1109)

```
APPROX-VERTEX-COVER(G)
1  C = ∅
2  E' = G.E
3  while E' ≠ ∅
4      let (u,v) be an arbitrary edge of E'
5      C = C ∪ {u, v}
6      remove from E' every edge incident on either u or v
7  return C
```

### Implementation Mapping

| CLRS step | Implementation | Faithful? |
|-----------|---------------|-----------|
| Empty cover (line 1) | `V.alloc 0 n` — zero-initialised cover array | ✅ |
| Edge set E' (line 2) | Adjacency matrix `adj[u*n+v]`, scanned in-order | ✅ equivalent |
| While loop (line 3) | Nested `for u in 0..n, for v in u+1..n` | ✅ equivalent |
| Pick arbitrary edge (line 4) | Sequential scan; edge picked when `has_edge ≠ 0 && cu = 0 && cv = 0` | ✅ |
| Add both endpoints (line 5) | `cover[u] := 1; cover[v] := 1` | ✅ |
| Remove incident edges (line 6) | Implicit: future edges skip covered vertices (`cu = 0 && cv = 0` guard) | ✅ equivalent |
| Return C (line 7) | Returns `cover` vec | ✅ |

**Verdict**: The implementation is a faithful deterministic realisation of APPROX-VERTEX-COVER. The CLRS algorithm picks an "arbitrary" uncovered edge; the implementation scans edges in lexicographic `(u,v)` order, which is a valid instantiation. The "remove incident edges" step is implicit via the guard that checks both endpoints are uncovered — edges incident on already-covered vertices are skipped in constant time per edge rather than being physically deleted from a set, which is a standard and correct optimisation.

**Minor difference**: CLRS uses adjacency lists and explicitly removes edges. The implementation uses an adjacency matrix and skips edges whose endpoints are already covered. Both produce a maximal matching and a valid 2-approximate cover. The adjacency-matrix representation changes the complexity from O(V+E) to O(V²) — see §3.

---

## 2. Specification Strength

### What is proven (postcondition of `approx_vertex_cover`, lines 188–195 of `.fst`):

| Property | Status | Location |
|----------|--------|----------|
| **Valid cover**: every edge has ≥1 endpoint in cover | ✅ Proven | `is_cover s_adj s_cover n n 0` |
| **Binary output**: cover values are 0 or 1 | ✅ Proven | `∀ i < n. s_cover[i] = 0 ∨ s_cover[i] = 1` |
| **2-approximation**: `|C| ≤ 2·OPT` | ✅ Proven | `count_cover(...) ≤ 2 * opt` for all `opt` satisfying `min_vertex_cover_size` |
| **Memory safety**: separation-logic framing | ✅ Proven | Pulse pre/post with `pts_to` |

### Proof architecture (Lemmas.fst + Impl.fst)

The approximation proof follows the CLRS Theorem 35.1 argument exactly:

1. **Matching is pairwise-disjoint** (`pairwise_disjoint m`) — maintained as a ghost invariant. Each new edge `(u,v)` is added to matching `m` only when `cu = 0 ∧ cv = 0`, meaning neither endpoint appears in any prior matching edge. Proved in `matching_inv_step` (Impl.fst).

2. **Cover = matching endpoints** (`matching_inv`, Impl.fst) — cover[x] ≠ 0 iff x appears in some matching edge. Proved by `existsb`/`edge_uses_vertex` correspondence.

3. **|C| = 2|M|** (`matching_cover_size`, Lemmas.fst) — by induction on the matching list, using `matching_cover_add_two` to account for each edge contributing exactly 2 vertices.

4. **|C*| ≥ |M|** (`matching_lower_bound`, Lemmas.fst) — any valid cover must include ≥1 endpoint of each disjoint matching edge, so OPT ≥ |M|.

5. **Combining**: `|C| = 2|M| ≤ 2|C*|` (`theorem_35_1` and `approximation_ratio_theorem`, Lemmas.fst).

**Key bridge lemma**: `pulse_cover_is_valid` (Lemmas.fst) connects the Pulse `is_cover` predicate (which works on sequences and bounded quantifiers) to the pure `is_valid_graph_cover` predicate (which works on `extract_edges` lists). This is necessary because the Pulse implementation tracks coverage incrementally via `(bound_u, bound_v)` bounds, while the spec reasons about edge lists.

### Specification completeness

The `min_vertex_cover_size` definition (Spec.fst) is existentially quantified:
```fstar
let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn). is_minimum_vertex_cover adj n c_min /\ count_cover c_min n = opt
```
This is clean — the postcondition says "for all opt, if opt is the minimum cover size, then our cover is ≤ 2·opt." The universal quantification over `opt` is correct and standard.

**Graph symmetry is formally required** via `Spec.is_symmetric_adj s_adj (SZ.v n)` in the precondition, requiring `adj[u*n+v] = adj[v*n+u]` for all `u, v < n`. This makes explicit that the algorithm is correct only for undirected graphs.

**Minimum cover existence is proven** via `Lemmas.min_cover_exists`, using a well-ordering argument. This makes the 2-approximation guarantee non-vacuous.

---

## 3. Complexity

### CLRS complexity: O(V + E)

Using adjacency lists, CLRS achieves O(V + E) by removing edges incident on matched vertices.

### Implementation complexity: O(V²) — formally linked

The implementation uses a nested loop over all `(u, v)` pairs with `u < v`:
- Outer loop: `u` from `0` to `n-1` → n iterations
- Inner loop: `v` from `u+1` to `n-1` → up to n-1 iterations
- Total iterations: `n*(n-1)/2 = O(V²)`

The complexity is defined in `CLRS.Ch35.VertexCover.Complexity`:
```fstar
let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2
let vertex_cover_quadratic (v: nat) : Lemma (ensures vertex_cover_iterations v <= v * v) = ()
let vertex_cover_tight_bound (v: nat) : Lemma (ensures vertex_cover_iterations v <= v * v / 2) = ()
```

The complexity is **formally linked** to the Pulse implementation via a ghost
iteration counter (`ghost_iters`). The counter tracks cumulative iterations
through `partial_iterations`, and after the nested loops, an assertion
establishes `ghost_iters == vertex_cover_iterations(n)`.

| Aspect | CLRS | Implementation | Gap |
|--------|------|----------------|-----|
| Time | O(V+E) | O(V²) | ⚠️ Quadratic regardless of edge density |
| Space | O(V+E) for adj list + O(V) for cover | O(V²) for adj matrix + O(V) for cover | ⚠️ |

**Assessment**: The O(V²) bound is correct for an adjacency-matrix representation and is formally linked to the Pulse implementation via a ghost iteration counter. The `partial_iterations` function tracks cumulative iterations row-by-row, and `partial_iterations_total` proves equivalence to `vertex_cover_iterations`. For sparse graphs this is suboptimal vs. CLRS's O(V+E), which is a design choice (adjacency matrix vs. adjacency list).

---

## 4. Code Quality

### Strengths

- **Clean separation**: Spec.fst (pure types/predicates), Lemmas.fst (proofs), Complexity.fst (complexity), Impl.fst (Pulse imperative code). Rubric-compliant 7-file structure.
- **Ghost state**: The matching `m` is tracked via `GR.alloc`/`GR.pts_to` (ghost reference), introducing zero runtime overhead. This is an elegant encoding of the CLRS proof's "set A of edges picked in line 4."
- **Incremental invariants**: `is_cover` uses `(bound_u, bound_v)` to track which edges have been processed so far — a natural inductive approach for the nested loop.
- **Snippet markers**: `//SNIPPET_START` / `//SNIPPET_END` for documentation extraction.
- **Modest solver settings**: Only `--z3rlimit 30` and `--z3rlimit 40` — no extreme resource limits. No z3refresh, no retry, no fuel/ifuel adjustments.
- **Complexity linked**: Ghost iteration counter formally linked to `vertex_cover_iterations(n)`.

### Issues (all resolved or low priority)

| Issue | Severity | Status |
|-------|----------|--------|
| ~~README lists nonexistent files~~ | Medium | ✅ Fixed |
| ~~Complexity proof disconnected from code~~ | Medium | ✅ Fixed — ghost counter links to `partial_iterations` |
| ~~No graph symmetry precondition~~ | Medium | ✅ Fixed — `is_symmetric_adj` in precondition |
| ~~`min_vertex_cover_size` vacuously true~~ | Medium | ✅ Fixed — `min_cover_exists` proves existence |
| ~~Stale cache entries~~ | Low | ✅ Fixed |
| Unconditional writes (O(n²) writes vs O(E)) | Low | Design choice, simplifies proof |
| No n=0 support | Low | Trivial degenerate case |

---

## 5. Proof Quality — Admits / Assumes

### Admits

**None.** Zero `admit()` calls in either file.

### Assumes

**None.** Zero `assume` calls in either file.

### Verification status

All 7 files have `.checked` cache entries (~48s clean build):
- `CLRS.Ch35.VertexCover.Spec.fst.checked` ✅
- `CLRS.Ch35.VertexCover.Lemmas.fsti.checked` ✅
- `CLRS.Ch35.VertexCover.Lemmas.fst.checked` ✅
- `CLRS.Ch35.VertexCover.Complexity.fsti.checked` ✅
- `CLRS.Ch35.VertexCover.Complexity.fst.checked` ✅
- `CLRS.Ch35.VertexCover.Impl.fsti.checked` ✅
- `CLRS.Ch35.VertexCover.Impl.fst.checked` ✅

### Solver hints used

| File | Location | Option |
|------|----------|--------|
| `Impl.fst` | `is_cover_step` | `#push-options "--z3rlimit 30"` |
| `Impl.fst` | `matching_inv_step` | `#push-options "--z3rlimit 40"` |
| `Lemmas.fst` | `min_cover_exists_aux` | `#push-options "--z3rlimit 30"` |

No `z3refresh`, no `retry`, no `fuel`/`ifuel` adjustments. The solver limits are modest.

### Proof structure summary

| Lemma / Function | File | Status |
|-----------------|------|--------|
| `is_cover_skip_to` | Impl.fst | ✅ Proven (trivial) |
| `is_cover_next_row` | Impl.fst | ✅ Proven (trivial) |
| `is_cover_step` | Impl.fst | ✅ Proven (z3rlimit 30) |
| `is_cover_binary_step` | Impl.fst | ✅ Proven |
| `matching_inv_step` | Impl.fst | ✅ Proven (z3rlimit 40) |
| `apply_approximation_bound` | Impl.fst | ✅ Proven |
| `approx_vertex_cover` | Impl.fst | ✅ Proven (Pulse fn) |
| `count_cover_ext` | Lemmas.fst | ✅ Proven (induction) |
| `count_zero` | Lemmas.fst | ✅ Proven (induction) |
| `count_single` | Lemmas.fst | ✅ Proven (induction) |
| `count_cover_mono` | Lemmas.fst | ✅ Proven (induction) |
| `count_split_one` | Lemmas.fst | ✅ Proven (induction) |
| `count_split` | Lemmas.fst | ✅ Proven |
| `sum_ge_length` | Lemmas.fst | ✅ Proven (induction) |
| `sum_restricted` | Lemmas.fst | ✅ Proven (induction) |
| `sum_le_count` | Lemmas.fst | ✅ Proven (induction) |
| `matching_lower_bound` | Lemmas.fst | ✅ Proven |
| `matching_cover_add_one` | Lemmas.fst | ✅ Proven (induction) |
| `matching_cover_add_two` | Lemmas.fst | ✅ Proven (induction) |
| `matching_cover_size` | Lemmas.fst | ✅ Proven (induction) |
| `theorem_35_1` | Lemmas.fst | ✅ Proven |
| `extract_edges_complete` | Lemmas.fst | ✅ Proven (induction) |
| `extract_edges_valid` | Lemmas.fst | ✅ Proven (induction) |
| `pulse_cover_is_valid` | Lemmas.fst | ✅ Proven |
| `extract_edges_contains` | Lemmas.fst | ✅ Proven (induction) |
| `valid_graph_cover_covers_edge` | Lemmas.fst | ✅ Proven |
| `valid_cover_covers_matching` | Lemmas.fst | ✅ Proven (induction) |
| `all_true_is_valid` | Lemmas.fst | ✅ Proven |
| `count_all_true` | Lemmas.fst | ✅ Proven (induction) |
| `min_cover_exists_aux` | Lemmas.fst | ✅ Proven (z3rlimit 30) |
| `min_cover_exists` | Lemmas.fst | ✅ Proven |
| `approximation_ratio_theorem` | Lemmas.fst | ✅ Proven |
| `vertex_cover_iterations` | Complexity.fst | ✅ Definition |
| `vertex_cover_quadratic` | Complexity.fst | ✅ Proven (trivial) |
| `vertex_cover_tight_bound` | Complexity.fst | ✅ Proven (trivial) |
| `partial_iterations` | Complexity.fst | ✅ Definition |
| `partial_iterations_zero` | Complexity.fst | ✅ Proven (trivial) |
| `partial_iterations_step` | Complexity.fst | ✅ Proven (trivial) |
| `partial_iterations_formula` | Complexity.fst | ✅ Proven (induction) |
| `partial_iterations_total` | Complexity.fst | ✅ Proven |

**Total: 0 admits, 0 assumes, ~40 lemmas/definitions all fully proven.**

---

## 6. Documentation Accuracy

### README.md

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| "Zero admits. Zero assumes." | ✅ Correct | Verified by grep |
| "All proofs complete" | ✅ Correct | All 7 files verify |
| File inventory table | ✅ Correct | All 7 listed files exist and match |
| Build instructions | ✅ Correct | `make verify` works |
| Summary table | ✅ Correct | All properties accurately described |

### In-code documentation

The block comment at lines 335–358 of Impl.fst is accurate and clearly explains the proof technique. The `(* CLRS Theorem 35.1 *)` section in Lemmas.fst accurately describes what is proven.

---

## 7. Task List — Missing Ch35 Algorithms

CLRS Chapter 35 contains **5 sections**:

| Section | Algorithm / Topic | Status |
|---------|------------------|--------|
| **35.1** | APPROX-VERTEX-COVER (2-approx vertex cover) | ✅ **Implemented & fully proven** |
| **35.2** | APPROX-TSP-TOUR (2-approx TSP with triangle inequality) | ❌ Not implemented |
| **35.2** | Theorem 35.3: Inapproximability of general TSP | ❌ Not stated |
| **35.3** | GREEDY-SET-COVER (H(max|S|)-approx set cover) | ❌ Not implemented |
| **35.4** | Randomized MAX-3-CNF (8/7-approx) | ❌ Not implemented |
| **35.4** | Weighted vertex cover via LP relaxation (2-approx) | ❌ Not implemented |
| **35.5** | APPROX-SUBSET-SUM (FPTAS for subset sum) | ❌ Not implemented |

### Estimated difficulty for missing algorithms

| Algorithm | Difficulty | Notes |
|-----------|-----------|-------|
| APPROX-TSP-TOUR | **Hard** | Requires MST (Ch23) + Euler tour + shortcutting. Triangle inequality proof non-trivial. |
| GREEDY-SET-COVER | **Medium** | Greedy loop similar to vertex cover. Harmonic-number approximation ratio proof is moderately complex. |
| MAX-3-CNF | **Medium** | Randomized; would need probabilistic reasoning or expected-value specs. |
| LP vertex cover | **Hard** | Requires LP solver infrastructure (Ch29) not present in AutoCLRS. |
| APPROX-SUBSET-SUM | **Medium** | Dynamic programming variant with trimming. FPTAS proof involves careful error tracking. |

---

## Summary

| Dimension | Rating | Notes |
|-----------|--------|-------|
| **CLRS Fidelity** | ★★★★★ | Faithful to APPROX-VERTEX-COVER; deterministic scan is valid instantiation |
| **Specification Strength** | ★★★★★ | All 5 key properties proven: length, valid cover, binary output, min cover existence, 2-approximation |
| **Complexity** | ★★★★☆ | O(V²) vs CLRS's O(V+E); formally linked via ghost counter |
| **Code Quality** | ★★★★★ | Clean 7-file rubric structure; ghost matching is elegant; all prior issues resolved |
| **Proof Quality** | ★★★★★ | 0 admits, 0 assumes, ~40 lemmas fully proven, modest solver limits |
| **Documentation** | ★★★★★ | README, Review.md, RUBRIC_35.md all accurate and comprehensive |
| **Proof Stability** | ★★★★★ | Modest z3rlimits (≤40), no z3refresh/retry/fuel tweaks, ~48s clean build |
| **Ch35 Coverage** | ★★☆☆☆ | 1 of 5 sections implemented (APPROX-VERTEX-COVER only) |

### Remaining items (low priority)

1. **Unconditional writes**: Cover array written O(n²) times; could guard behind branch (simplifies proof, low priority).
2. **No n=0 support**: Precondition requires n > 0; degenerate case excluded.
3. **O(V²) vs O(V+E)**: Adjacency-matrix representation; design choice, not correctness issue.
4. **Tight ratio not proven**: 2-approx bound proven achieved but not proven tight.

### Deferred: Additional Ch35 algorithms

| CLRS Section | Algorithm | Priority | Difficulty |
|--------------|-----------|----------|------------|
| §35.2 | APPROX-TSP-TOUR (2-approx TSP) | Low | Hard (needs Ch23 MST + Euler tour) |
| §35.3 | GREEDY-SET-COVER (H(n)-approx) | Medium | Medium |
| §35.4 | MAX-3-CNF randomised (8/7-approx) | Low | Medium (probabilistic reasoning) |
| §35.4 | LP-relaxation vertex cover (2-approx) | Low | Hard (needs Ch29 LP infra) |
| §35.5 | APPROX-SUBSET-SUM (FPTAS) | Low | Medium |
