# Vertex Cover 2-Approximation — Review (CLRS §35.1)

**Last reviewed**: 2026-03-17
**Reviewer**: Copilot audit
**Verdict**: ✅ Fully proven, rubric-compliant, spec-validated

---

## Priority Checklist

- [x] **P0: Rubric compliance** — 7/7 required files present and verified
- [x] **P0: Zero admits** — Confirmed: 0 `admit()`, 0 `assume` in all files
- [x] **P0: Verification** — All 8 files verify cleanly (including ImplTest)
- [x] **P0: Spec strength** — Valid cover + binary output + 2-approximation + min cover existence + even count
- [x] **P0: CLRS fidelity** — Faithful to APPROX-VERTEX-COVER pseudocode
- [x] **P0: Spec validation** — ImplTest proves postcondition precision on K₃ (3 of 8 covers, see below)
- [x] **P1: Symmetry precondition** — `is_symmetric_adj` formally enforced
- [x] **P1: Min cover existence** — `min_cover_exists` makes 2-approx non-vacuous
- [x] **P1: Complexity linked** — Ghost counter tracks `vertex_cover_iterations(n)`
- [x] **P1: Proof stability** — Modest solver limits (z3rlimit 30, 40 only)
- [x] **P1: Even count exposed** — Postcondition includes `∃ k. count = 2k` (vertices added in pairs)
- [ ] **P2: Unconditional writes** — Cover array written O(n²) times; could guard writes behind a branch (low priority, simplifies proof)
- [ ] **P2: No n=0 support** — Precondition requires n > 0; degenerate case not handled
- [ ] **P3: O(V²) vs O(V+E)** — Adjacency-matrix representation; CLRS uses adjacency lists for O(V+E) on sparse graphs
- [ ] **P3: Tight ratio not proven** — The 2-approx bound is proven achieved but not proven tight (existence of worst-case graph not formalized)
- [ ] **Deferred: Additional Ch35 algorithms** — GREEDY-SET-COVER, APPROX-TSP-TOUR, etc.

---

## Top-Level Signature (`Impl.fsti`)

```fstar
fn approx_vertex_cover
  (#p: perm)
  (adj: array int)
  (#s_adj: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to adj #p s_adj ** 
    pure (
      SZ.v n > 0 /\ 
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_adj == SZ.v n * SZ.v n /\
      Spec.is_symmetric_adj s_adj (SZ.v n)
    )
  returns cover: V.vec int
  ensures exists* s_cover.
    A.pts_to adj #p s_adj **
    V.pts_to cover s_cover **
    pure (
      V.is_full_vec cover /\
      Seq.length s_cover == SZ.v n /\
      Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0 /\
      (forall (i: nat). i < SZ.v n ==>
        (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      (exists (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt) /\
      (forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
        Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n)
          <= 2 * opt) /\
      (exists (k: nat). Spec.count_cover
        (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) = 2 * k)
    )
```

### Parameters

* `adj` — read-only adjacency matrix as a flat `array int`;
  `adj[u*n + v] ≠ 0` indicates edge (u, v). Ghost `s_adj` captures contents.
* `n` — vertex count (`SZ.t`). Matrix has `n × n` entries.
* `cover` — freshly allocated `V.vec int` of length `n`.
  `cover[i] = 1` means vertex `i` is in the cover; `cover[i] = 0` means not.

### Preconditions

| Precondition | Purpose |
|---|---|
| `SZ.v n > 0` | At least one vertex |
| `SZ.fits (SZ.v n * SZ.v n)` | Matrix size fits in machine arithmetic |
| `Seq.length s_adj == SZ.v n * SZ.v n` | Adjacency matrix has expected size |
| `Spec.is_symmetric_adj s_adj (SZ.v n)` | Undirected graph: `adj[u*n+v] = adj[v*n+u]` |

### Postconditions (6 properties)

1. **Full vec**: `V.is_full_vec cover` — caller can free the returned Vec
2. **Correct length**: `Seq.length s_cover == SZ.v n`
3. **Valid cover**: `is_cover s_adj s_cover n n 0` — every edge has ≥1 endpoint covered
4. **Binary output**: `∀ i < n. cover[i] = 0 ∨ cover[i] = 1`
5. **Min cover existence**: `∃ opt. min_vertex_cover_size adj n opt` (non-vacuous guarantee)
6. **2-approximation**: `count_cover(cover) ≤ 2 × OPT` (CLRS Theorem 35.1)
7. **Even count**: `∃ k. count_cover(cover) = 2 × k` (vertices added in pairs)

---

## Proof Structure

The proof uses a **ghost matching** technique with a **ghost iteration counter**:

1. A `GR.ref (list Spec.edge)` ghost reference tracks the matching — edges
   whose endpoints were added to the cover during execution.

2. A `GR.ref nat` ghost reference tracks inner-loop iterations, linked to
   `Complexity.vertex_cover_iterations`.

3. The `matching_inv` invariant states:
   - The matching is pairwise disjoint (no shared vertices)
   - Cover entries ↔ matching endpoints:
     `(s_cover[x] ≠ 0) ↔ existsb (edge_uses_vertex · x) matching`
   - Each matching edge is a valid graph edge with `u < v`

4. After loops, `apply_approximation_bound` applies
   `Lemmas.approximation_ratio_theorem` to connect ghost matching to the
   2-approximation guarantee.

### Key Lemmas

| Lemma | File | Purpose |
|-------|------|---------|
| `matching_lower_bound` | Lemmas.fst | Any valid cover ≥ matching size |
| `matching_cover_size` | Lemmas.fst | Algorithm cover = 2 × matching size |
| `theorem_35_1` | Lemmas.fst | Combines above: `|C| ≤ 2 × OPT` |
| `pulse_cover_is_valid` | Lemmas.fst | Connects Pulse `is_cover` to pure `is_valid_graph_cover` |
| `approximation_ratio_theorem` | Lemmas.fst | Bridge: Pulse output → CLRS theorem |
| `min_cover_exists` | Lemmas.fst | Every finite graph has a minimum vertex cover |
| `is_cover_step` | Impl.fst | Processing one edge preserves `is_cover` |
| `matching_inv_step` | Impl.fst | Updating cover+matching preserves `matching_inv` |
| `derive_even_count` | Impl.fst | Cover size = 2 × matching size (even count) |

---

## Profiling & Proof Stability

### Build Profiling (clean build)

| File | Lines | Role |
|------|------:|------|
| `Spec.fst` | 105 | Pure specification |
| `Complexity.fsti` | 41 | Complexity interface |
| `Complexity.fst` | 58 | Complexity proofs |
| `Lemmas.fsti` | 122 | Lemma signatures |
| `Lemmas.fst` | 383 | Lemma proofs |
| `Impl.fsti` | 48 | Public interface |
| `Impl.fst` | 358 | Pulse implementation |
| **Total** | **1115** | **~48s verification time** |

### Solver Settings

| File | Location | Setting | Purpose |
|------|----------|---------|---------|
| `Impl.fst` | `is_cover_step` | `--z3rlimit 30` | Seq.upd reasoning with cover property |
| `Impl.fst` | `matching_inv_step` | `--z3rlimit 40` | Matching invariant maintenance |
| `Lemmas.fst` | `min_cover_exists_aux` | `--z3rlimit 30` | Well-ordering induction |

**Assessment**: All solver limits are modest (≤ 40). No `z3refresh`, no
`retry`, no `fuel`/`ifuel` adjustments. The proofs are **stable** — no
fragile solver dependencies.

---

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Iterations | O(V²) = V(V−1)/2 | ✅ Ghost counter | Exact |
| Quadratic bound | V(V−1)/2 ≤ V² | ✅ `vertex_cover_quadratic` | — |
| Tight bound | V(V−1)/2 ≤ V²/2 | ✅ `vertex_cover_tight_bound` | — |

The ghost iteration counter is tracked through both loop invariants using
`partial_iterations` and linked at exit via `partial_iterations_total`.

**Note**: CLRS achieves O(V+E) with adjacency lists. The adjacency-matrix
representation is a design choice, not a correctness issue.

---

## Specification Gaps and Limitations

1. ~~**Missing `V.is_full_vec` in postcondition**~~ — **FIXED.** The original
   postcondition did not expose `V.is_full_vec cover`, preventing callers from
   freeing the returned Vec. Fixed by adding `V.is_full_vec cover` to the
   postcondition and both loop invariants. Zero admits.

2. ~~**Missing even count property**~~ — **FIXED.** The postcondition did not
   expose that cover size is always even. Added `∃ k. count = 2k` via
   `derive_even_count` lemma. This narrowed the K₃ test from 4 to 3 admissible
   covers.

3. **O(V²) vs O(V+E)** — Adjacency-matrix scan vs. CLRS adjacency lists.
   Asymptotically slower for sparse graphs. Design choice.

3. **No n=0 support** — Precondition requires `n > 0`. Trivial case excluded.

4. **Unconditional writes** — Cover array written O(n²) times (simplifies
   proof but adds redundant writes). Low priority.

5. **No weighted cover** — Only unweighted vertex cover. CLRS §35.2
   discusses weighted variants.

6. **Tight ratio not proven** — 2-approx bound is proven achieved but not
   proven tight (no worst-case graph construction formalized).

---

## Spec Validation (ImplTest)

**Test file:** `CLRS.Ch35.VertexCover.ImplTest.fst`
**Documentation:** `CLRS.Ch35.VertexCover.ImplTest.md`
**Status:** ✅ Fully verified — zero admits, zero assumes

### Test Instance

Complete graph K₃ (triangle on 3 vertices, all edges present).

### Results

| Aspect | Result |
|--------|--------|
| Precondition satisfiable | ✅ All 4 preconditions proven for K₃ |
| Postcondition constrains output | ✅ Output narrowed to 3 of 8 possible binary vectors |
| Invalid outputs excluded | ✅ All 5 invalid covers (0-vertex, 1-vertex, 3-vertex) excluded |
| Spec fix needed | ✅ Fixed: added `V.is_full_vec cover` and even count to postcondition |
| 2-approx bound useful | ⚠️ For K₃, `is_cover + binary + even count` is strictly stronger than 2·OPT bound |

### Spec Issues Found and Fixed

1. The postcondition was missing `V.is_full_vec cover`, making it impossible
   for callers to free the returned Vec. Fixed.

2. The postcondition was missing the even count property (`∃ k. count = 2k`).
   This prevented ruling out `[1,1,1]` for K₃, since count=3 is odd but the
   algorithm only adds vertices in pairs. Fixed by `derive_even_count` lemma,
   narrowing K₃ admissible covers from 4 to 3.

---

## File Inventory

| File | Lines | Role | Admits |
|------|------:|------|--------|
| `CLRS.Ch35.VertexCover.Spec.fst` | 105 | Pure types, predicates, counting | 0 |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | 122 | Lemma signatures | 0 |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | 383 | All proofs: counting, Thm 35.1, bridge | 0 |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | 41 | Complexity definitions | 0 |
| `CLRS.Ch35.VertexCover.Complexity.fst` | 58 | O(V²) bound, partial_iterations | 0 |
| `CLRS.Ch35.VertexCover.Impl.fsti` | 50 | Public Pulse interface | 0 |
| `CLRS.Ch35.VertexCover.Impl.fst` | 379 | Pulse implementation + proof | 0 |
| `CLRS.Ch35.VertexCover.ImplTest.fst` | 162 | Spec validation test | 0 |
| **Total** | **1300** | | **0** |
