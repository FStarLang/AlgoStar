# Audit Report — Chapter 35: Approximation Algorithms (Vertex Cover)

**Date**: 2025-02-26
**Scope**: `ch35-approximation/` — 2 files (816 lines total)
**Verification cache**: Both `.checked` files present

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

### Proof architecture (Spec.fst, 451 lines)

The approximation proof follows the CLRS Theorem 35.1 argument exactly:

1. **Matching is pairwise-disjoint** (`pairwise_disjoint m`) — maintained as a ghost invariant. Each new edge `(u,v)` is added to matching `m` only when `cu = 0 ∧ cv = 0`, meaning neither endpoint appears in any prior matching edge. Proved in `matching_inv_step` (line 116).

2. **Cover = matching endpoints** (`matching_inv`, line 96) — cover[x] ≠ 0 iff x appears in some matching edge. Proved by `existsb`/`edge_uses_vertex` correspondence.

3. **|C| = 2|M|** (`matching_cover_size`, line 264) — by induction on the matching list, using `matching_cover_add_two` to account for each edge contributing exactly 2 vertices.

4. **|C*| ≥ |M|** (`matching_lower_bound`, line 208) — any valid cover must include ≥1 endpoint of each disjoint matching edge, so OPT ≥ |M|.

5. **Combining**: `|C| = 2|M| ≤ 2|C*|` (`theorem_35_1`, line 300, and `approximation_ratio_theorem`, line 431).

**Key bridge lemma**: `pulse_cover_is_valid` (Spec.fst:362) connects the Pulse `is_cover` predicate (which works on sequences and bounded quantifiers) to the pure `is_valid_graph_cover` predicate (which works on `extract_edges` lists). This is necessary because the Pulse implementation tracks coverage incrementally via `(bound_u, bound_v)` bounds, while the spec reasons about edge lists.

### Specification completeness

The `min_vertex_cover_size` definition (Spec.fst:66) is existentially quantified:
```fstar
let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn). is_minimum_vertex_cover adj n c_min /\ count_cover c_min n = opt
```
This is clean — the postcondition says "for all opt, if opt is the minimum cover size, then our cover is ≤ 2·opt." The universal quantification over `opt` is correct and standard.

**No assumption is made about graph symmetry** (i.e., `adj[u*n+v] = adj[v*n+u]`). The algorithm only examines upper-triangular entries `u < v`. For symmetric graphs this is correct; for directed graphs the cover only covers edges `(u,v)` with `u < v`. This is consistent with CLRS's assumption of undirected graphs but could be stated more explicitly as a precondition.

---

## 3. Complexity

### CLRS complexity: O(V + E)

Using adjacency lists, CLRS achieves O(V + E) by removing edges incident on matched vertices.

### Implementation complexity: O(V²)

The implementation uses a nested loop over all `(u, v)` pairs with `u < v`:
- Outer loop: `u` from `0` to `n-1` → n iterations
- Inner loop: `v` from `u+1` to `n-1` → up to n-1 iterations
- Total iterations: `n*(n-1)/2 = O(V²)`

The code at line 361 acknowledges this:
```fstar
let vertex_cover_iterations (v: nat) : nat = v * v
let vertex_cover_quadratic (v: nat) : Lemma (ensures vertex_cover_iterations v <= v * v) = ()
```

| Aspect | CLRS | Implementation | Gap |
|--------|------|----------------|-----|
| Time | O(V+E) | O(V²) | ⚠️ Quadratic regardless of edge density |
| Space | O(V+E) for adj list + O(V) for cover | O(V²) for adj matrix + O(V) for cover | ⚠️ |

**Assessment**: The O(V²) bound is correct for an adjacency-matrix representation and is stated/proven. For sparse graphs this is suboptimal vs. CLRS's O(V+E). The complexity "proof" (lines 361–366) is trivially `v*v ≤ v*v` — it asserts a bound but does not connect it to the actual loop structure or count of operations. This is a **weak complexity proof** — it's a statement about a standalone function, not about the imperative code.

---

## 4. Code Quality

### Strengths

- **Clean separation**: Spec.fst (pure math) vs. VertexCover.fst (Pulse imperative code). The spec is 451 lines of pure F*, fully independent of Pulse.
- **Ghost state**: The matching `m` is tracked via `GR.alloc`/`GR.pts_to` (ghost reference), introducing zero runtime overhead. This is an elegant encoding of the CLRS proof's "set A of edges picked in line 4."
- **Incremental invariants**: `is_cover` uses `(bound_u, bound_v)` to track which edges have been processed so far — a natural inductive approach for the nested loop.
- **Snippet markers**: `//SNIPPET_START` / `//SNIPPET_END` for documentation extraction.
- **Modest solver settings**: Only `--z3rlimit 30` and `--z3rlimit 40` — no extreme resource limits.

### Issues

| Issue | Severity | Location |
|-------|----------|----------|
| **README lists 5 nonexistent files**: `Complexity.fst`, `Test.fst`, `P2.7_SUMMARY.md`, `P2.7_API.md`, `P2.7_COMPLETE.md` | Medium | README.md:53–57 |
| **Complexity.fst cached but missing**: `_cache/CLRS.Ch35.VertexCover.Complexity.fst.checked` exists but the source file does not | Low | `_cache/` |
| **`cover_values_are_binary` is trivial**: Precondition restates the conclusion. The lemma (lines 145–151) is dead code — it does nothing the caller doesn't already know. | Low | `.fst:145–151` |
| **n < 256 constraint**: Precondition requires `SZ.v n < 256` (line 181). This is conservative for `SizeT` — the real constraint is `n*n` fits in `SizeT`, which would allow n up to ~65535 on 32-bit or much more on 64-bit. The 256 limit appears to be an artifact. | Low | `.fst:181` |
| **No undirected-graph precondition**: The algorithm assumes upper-triangular adjacency but does not require `adj[u*n+v] = adj[v*n+u]`. For non-symmetric matrices, edges `(v,u)` with `v > u` are silently ignored. | Low | — |

---

## 5. Proof Quality — Admits / Assumes

### Admits

**None.** Zero `admit()` calls in either file.

### Assumes

**None.** Zero `assume` calls in either file.

### Verification status

Both files have `.checked` cache entries:
- `ch35-approximation/_cache/CLRS.Ch35.VertexCover.fst.checked` ✅
- `ch35-approximation/_cache/CLRS.Ch35.VertexCover.Spec.fst.checked` ✅

### Solver hints used

| File | Line | Option |
|------|------|--------|
| `VertexCover.fst` | 52 | `#push-options "--z3rlimit 30"` (for `is_cover_step`) |
| `VertexCover.fst` | 73 | `#pop-options` |
| `VertexCover.fst` | 115 | `#push-options "--z3rlimit 40"` (for `matching_inv_step`) |
| `VertexCover.fst` | 141 | `#pop-options` |

No `z3refresh`, no `retry`, no `fuel`/`ifuel` adjustments. The solver limits are modest.

### Proof structure summary

| Lemma / Function | File | Lines | Status |
|-----------------|------|-------|--------|
| `is_cover_skip_to` | .fst | 35–39 | ✅ Proven (trivial) |
| `is_cover_next_row` | .fst | 42–46 | ✅ Proven (trivial) |
| `is_cover_step` | .fst | 53–73 | ✅ Proven (z3rlimit 30) |
| `is_cover_binary_step` | .fst | 76–93 | ✅ Proven |
| `matching_inv_step` | .fst | 116–141 | ✅ Proven (z3rlimit 40) |
| `cover_values_are_binary` | .fst | 145–151 | ✅ Proven (trivially) |
| `apply_approximation_bound` | .fst | 154–169 | ✅ Proven |
| `approx_vertex_cover` | .fst | 172–331 | ✅ Proven (Pulse fn) |
| `count_cover_ext` | Spec | 74–78 | ✅ Proven (induction) |
| `count_zero` | Spec | 80–82 | ✅ Proven (induction) |
| `count_single` | Spec | 84–95 | ✅ Proven (induction) |
| `count_cover_mono` | Spec | 97–101 | ✅ Proven (induction) |
| `count_split_one` | Spec | 106–118 | ✅ Proven (induction) |
| `count_split` | Spec | 120–135 | ✅ Proven |
| `sum_ge_length` | Spec | 148–154 | ✅ Proven (induction) |
| `sum_restricted` | Spec | 157–166 | ✅ Proven (induction) |
| `sum_le_count` | Spec | 185–203 | ✅ Proven (induction) |
| `matching_lower_bound` | Spec | 208–215 | ✅ Proven |
| `matching_cover_add_one` | Spec | 220–234 | ✅ Proven (induction) |
| `matching_cover_add_two` | Spec | 236–259 | ✅ Proven (induction) |
| `matching_cover_size` | Spec | 264–295 | ✅ Proven (induction) |
| `theorem_35_1` | Spec | 300–312 | ✅ Proven |
| `extract_edges_complete` | Spec | 331–345 | ✅ Proven (induction) |
| `extract_edges_valid` | Spec | 348–359 | ✅ Proven (induction) |
| `pulse_cover_is_valid` | Spec | 362–380 | ✅ Proven |
| `extract_edges_contains` | Spec | 385–400 | ✅ Proven (induction) |
| `valid_graph_cover_covers_edge` | Spec | 403–408 | ✅ Proven |
| `valid_cover_covers_matching` | Spec | 411–422 | ✅ Proven (induction) |
| `approximation_ratio_theorem` | Spec | 431–449 | ✅ Proven |

**Total: 0 admits, 0 assumes, ~30 lemmas all fully proven.**

---

## 6. Documentation Accuracy

### README.md issues

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| "No `admit()` calls" | ✅ Correct | Verified by grep |
| "No `assume` statements" | ✅ Correct | Verified by grep |
| "Proper resource management (no memory leaks)" | ✅ Correct | Ghost ref is freed (line 322); Vec returned to caller |
| Files: `Complexity.fst`, `Test.fst` | ❌ **Do not exist** | README:53–54 references phantom files |
| Files: `P2.7_SUMMARY.md`, `P2.7_API.md`, `P2.7_COMPLETE.md` | ❌ **Do not exist** | README:55–57 references phantom files |
| `verify_all.sh` | ❌ **Does not exist** | README:87 |
| Verification commands | ⚠️ Unverified | The `fstar.exe` invocations reference paths that may not resolve |

### In-code documentation

The block comment at lines 333–356 of `.fst` is accurate and clearly explains the proof technique. The `(* CLRS Theorem 35.1 *)` comment in Spec.fst accurately describes what is proven.

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
| **Specification Strength** | ★★★★★ | All 3 key properties proven: valid cover, binary output, 2-approximation |
| **Complexity** | ★★★☆☆ | O(V²) vs CLRS's O(V+E); complexity "proof" is trivial and disconnected from code |
| **Code Quality** | ★★★★☆ | Clean architecture; ghost matching is elegant; one dead lemma; README references 5 nonexistent files |
| **Proof Quality** | ★★★★★ | 0 admits, 0 assumes, ~30 lemmas fully proven, modest solver limits |
| **Documentation** | ★★★☆☆ | In-code docs excellent; README has 6 phantom file/script references |
| **Ch35 Coverage** | ★★☆☆☆ | 1 of 5 sections implemented (APPROX-VERTEX-COVER only) |

### Recommendations

1. **Fix README.md**: Remove references to 5 nonexistent files and `verify_all.sh`.
2. **Delete dead lemma**: `cover_values_are_binary` (line 145) has its conclusion in its precondition.
3. **Strengthen complexity proof**: Connect `vertex_cover_iterations` to the actual loop structure, or remove the misleading standalone function.
4. **Add graph symmetry precondition**: Explicitly require `adj[u*n+v] = adj[v*n+u]` for undirected graphs, or document the upper-triangular convention.
5. **Relax n < 256**: The constraint could be `n*n < SZ.bound` to support larger graphs.
6. **Clean stale cache**: Remove `_cache/CLRS.Ch35.VertexCover.Complexity.fst.checked` (source file deleted).
7. **Implement remaining Ch35 algorithms**: Prioritise GREEDY-SET-COVER (medium difficulty, high pedagogical value) and APPROX-TSP-TOUR (leverages existing Ch23 MST work).
