# Chapter 33: Computational Geometry — Rubric Compliance

## Current File Inventory

| File | Lines | Pure Specs | Lemmas | Pulse Impl | Complexity | .fsti |
|------|------:|:----------:|:------:|:----------:|:----------:|:-----:|
| `CLRS.Ch33.Segments.Spec.fst` | 73 | ✅ 6 defs | — | — | — | — |
| `CLRS.Ch33.Segments.Lemmas.fst` | 30 | — | ✅ 5 | — | — | ✅ |
| `CLRS.Ch33.Segments.Complexity.fst` | 35 | — | — | — | ✅ 4 defs, 2 lemmas | ✅ |
| `CLRS.Ch33.Segments.Impl.fst` | 92 | — | — | ✅ 4 fns | — | ✅ |
| `CLRS.Ch33.GrahamScan.Spec.fst` | 186 | ✅ 11 defs | — | — | — | — |
| `CLRS.Ch33.GrahamScan.Lemmas.fst` | 157 | — | ✅ 8 | — | — | ✅ |
| `CLRS.Ch33.GrahamScan.Complexity.fst` | 38 | — | — | — | ✅ 6 defs, 2 lemmas | ✅ |
| `CLRS.Ch33.GrahamScan.Impl.fst` | 235 | — | — | ✅ 4 fns | — | ✅ |
| `CLRS.Ch33.JarvisMarch.Spec.fst` | 128 | ✅ 10 defs | — | — | — | — |
| `CLRS.Ch33.JarvisMarch.Lemmas.fst` | 258 | — | ✅ 14 | — | — | ✅ |
| `CLRS.Ch33.JarvisMarch.Complexity.fst` | 30 | — | — | — | ✅ 3 defs, 2 lemmas | ✅ |
| `CLRS.Ch33.JarvisMarch.Impl.fst` | 355 | — | — | ✅ 4 fns | — | ✅ |

All twelve files follow the rubric's 7-file decomposition per algorithm (Spec, Lemmas+fsti,
Complexity+fsti, Impl+fsti). The original three monolithic files (`CLRS.Ch33.Segments.fst`,
`CLRS.Ch33.GrahamScan.fst`, `CLRS.Ch33.JarvisMarch.fst`) are retained for reference but
are superseded by the decomposed versions.

---

## Algorithms Covered

### 1. Segment Intersection Primitives (`Segments.fst` — CLRS §33.1)

Shared infrastructure used by Graham Scan and Jarvis March.

| CLRS Procedure | Spec Function | Pulse `fn` | Status |
|---|---|---|---|
| Cross product | `cross_product_spec` | `cross_product` | ✅ Complete |
| DIRECTION(pi,pj,pk) | `direction_spec` | `direction` | ✅ Complete |
| ON-SEGMENT(pi,pj,pk) | `on_segment_spec` | `on_segment` | ✅ Complete |
| SEGMENTS-INTERSECT | `segments_intersect_spec` | `segments_intersect` | ✅ Complete |

**Lemmas present (inline):** `cross_product_antisymmetric`, `orient_antisymmetric`,
`cross_product_translation`, `cross_product_degenerate_p2`, `cross_product_degenerate_p3`.

**Complexity:** Comment-only ("All operations are O(1)"). No formal op-count definitions.

### 2. Graham Scan (`GrahamScan.fst` — CLRS §33.3)

| Component | Spec Function | Pulse `fn` | Status |
|---|---|---|---|
| Find bottom-most point | `find_bottom_spec` | `find_bottom` | ✅ Complete |
| Polar angle comparison | `polar_cmp_spec` | `polar_cmp` | ✅ Complete |
| Pop non-left turns | `pop_while_spec` | `pop_while` | ✅ Complete |
| Scan loop + full scan | `graham_loop`, `graham_scan_sorted` | — | 🔶 Spec only, no Pulse |
| Polar-angle sorting | — | — | ❌ Missing entirely |

**Lemmas present (inline):** `find_bottom_spec_bounded`, `find_bottom_aux_is_min`,
`find_bottom_is_bottommost`, `pop_while_spec_bounded`, `pop_while_ensures_left_turn`,
`all_left_turns` (correctness definition, not proved as invariant).

**Complexity (inline):** `find_bottom_ops`, `polar_cmp_ops`, `pop_while_ops`,
`graham_scan_ops`, `graham_scan_quadratic` (O(n²)), `scan_linear` (O(n) amortized).

### 3. Jarvis March (`JarvisMarch.fst` — CLRS §33.3)

| Component | Spec Function | Pulse `fn` | Status |
|---|---|---|---|
| Find leftmost point | `find_leftmost_spec` | `find_leftmost` | ✅ Complete |
| Find next hull vertex | `find_next_spec` | `find_next` | ✅ Complete |
| Full Jarvis march | `jarvis_march_spec` | `jarvis_march` | ✅ Complete |

**Lemmas present (inline):** `find_leftmost_spec_bounded`, `find_next_spec_bounded`,
`find_next_spec_not_current`, `jarvis_loop_count_bounded`, `jarvis_march_spec_bounded`,
`jarvis_loop_step`, `find_leftmost_aux_is_min`, `find_leftmost_is_leftmost`,
`cross_prod_swap23`, `half_plane_transitivity`, `cross_prod_transitivity`,
`cross_prod_transitivity_degenerate`, `find_next_aux_beats_all`, `find_next_all_left_of`.

**Correctness properties:** `is_leftmost`, `all_left_of` — formal definitions with proofs.

**Complexity (inline):** `find_leftmost_ops`, `find_next_ops`, `jarvis_march_ops`,
`jarvis_march_quadratic_bound` (O(nh) ≤ O(n²)), `helpers_linear`.

---

## Rubric Compliance Matrix

The rubric requires 7 files per algorithm: `Spec.fst`, `Lemmas.fst`, `Lemmas.fsti`,
`Complexity.fst`, `Complexity.fsti`, `Impl.fst`, `Impl.fsti`.

### Segments (§33.1 primitives)

| Required File | Status | Notes |
|---|---|---|
| `CLRS.Ch33.Segments.Spec.fst` | ✅ Done | Pure specs: cross_product_spec, direction_spec, on_segment_spec, segments_intersect_spec, orientation |
| `CLRS.Ch33.Segments.Lemmas.fst` | ✅ Done | 5 lemmas: antisymmetry, translation invariance, degenerate cases |
| `CLRS.Ch33.Segments.Lemmas.fsti` | ✅ Done | Interface with val signatures for all 5 lemmas |
| `CLRS.Ch33.Segments.Complexity.fst` | ✅ Done | Formal O(1) op counts + composition lemma |
| `CLRS.Ch33.Segments.Complexity.fsti` | ✅ Done | Interface with op count vals + lemma sigs |
| `CLRS.Ch33.Segments.Impl.fst` | ✅ Done | 4 Pulse fns with spec-equivalence postconditions |
| `CLRS.Ch33.Segments.Impl.fsti` | ✅ Done | Interface with Pulse fn signatures |

**Score: 7/7 files** — Fully decomposed. All files verified (zero warns/errors).

### Graham Scan (§33.3)

| Required File | Status | Notes |
|---|---|---|
| `CLRS.Ch33.GrahamScan.Spec.fst` | ✅ Done | Pure specs using Segments.Spec.cross_product_spec; includes scan_step, graham_loop, pop_while_spec, correctness defs |
| `CLRS.Ch33.GrahamScan.Lemmas.fst` | ✅ Done | Bounds lemmas, find_bottom_is_bottommost, pop_while_ensures_left_turn |
| `CLRS.Ch33.GrahamScan.Lemmas.fsti` | ✅ Done | Interface with val signatures for all lemmas |
| `CLRS.Ch33.GrahamScan.Complexity.fst` | ✅ Done | Op counts + O(n²) bound + scan_linear lemma |
| `CLRS.Ch33.GrahamScan.Complexity.fsti` | ✅ Done | Interface with op count vals + lemma sigs |
| `CLRS.Ch33.GrahamScan.Impl.fst` | ✅ Done | 3 Pulse fns: find_bottom, polar_cmp, pop_while |
| `CLRS.Ch33.GrahamScan.Impl.fsti` | ✅ Done | Interface with Pulse fn signatures |

**Score: 7/7 files** — Fully decomposed. All files verified (zero warns/errors).
Pulse impl is partial (helpers only; no end-to-end `graham_scan` Pulse fn; no sorting).

### Jarvis March (§33.3)

| Required File | Status | Notes |
|---|---|---|
| `CLRS.Ch33.JarvisMarch.Spec.fst` | ✅ Done | Pure specs using Segments.Spec.cross_product_spec; includes jarvis_march_spec, correctness defs |
| `CLRS.Ch33.JarvisMarch.Lemmas.fst` | ✅ Done | 14 lemmas including half_plane_transitivity, find_next_all_left_of |
| `CLRS.Ch33.JarvisMarch.Lemmas.fsti` | ✅ Done | Interface with val signatures for all 14 lemmas |
| `CLRS.Ch33.JarvisMarch.Complexity.fst` | ✅ Done | O(nh) ≤ O(n²) bound + helpers_linear lemma |
| `CLRS.Ch33.JarvisMarch.Complexity.fsti` | ✅ Done | Interface with op count vals + lemma sigs |
| `CLRS.Ch33.JarvisMarch.Impl.fst` | ✅ Done | 3 Pulse fns: find_leftmost, find_next, jarvis_march |
| `CLRS.Ch33.JarvisMarch.Impl.fsti` | ✅ Done | Interface with Pulse fn signatures |

**Score: 7/7 files** — Fully decomposed. All files verified (zero warns/errors).
Most complete algorithm with full Pulse implementation and substantial correctness proofs.

### Overall Rubric Compliance

| Rubric Dimension | Segments | Graham Scan | Jarvis March |
|---|---|---|---|
| Separate Spec file | ✅ | ✅ | ✅ |
| Separate Lemmas file | ✅ | ✅ | ✅ |
| Lemmas .fsti | ✅ | ✅ | ✅ |
| Separate Complexity file | ✅ | ✅ | ✅ |
| Complexity .fsti | ✅ | ✅ | ✅ |
| Separate Impl file | ✅ | ✅ | ✅ |
| Impl .fsti | ✅ | ✅ | ✅ |
| Pure spec exists (anywhere) | ✅ | ✅ | ✅ |
| Pulse impl exists (anywhere) | ✅ | 🔶 Partial | ✅ |
| Impl postcondition = spec | ✅ | ✅ (for helpers) | ✅ |
| Zero admits | ✅ | ✅ | ✅ |
| Zero assumes | ✅ | ✅ | ✅ |
| Complexity analysis | ✅ Formal | ✅ Formal | ✅ Formal |
| Correctness lemmas | 🔶 Algebraic only | 🔶 Partial | ✅ Substantial |

---

## Detailed Action Items

### Priority 1: File Decomposition (structural rubric compliance) — ✅ COMPLETE

All three monolithic `.fst` files have been decomposed into the rubric's 7-file structure.
All 21 new files verify with zero admits, zero assumes, and zero warnings.
Cross-product definitions are now shared from `Segments.Spec.cross_product_spec`.

### Priority 2: Missing Implementations

| # | Action | CLRS Section | Est. Effort |
|---|---|---|---|
| 4 | Implement full `graham_scan` Pulse fn (sorting + stack scan) | §33.3 | High |
| 5 | Implement polar-angle sorting (or reuse existing sort infrastructure) | §33.3 | Medium |
| 6 | Implement ANY-SEGMENTS-INTERSECT (sweep line + BST) | §33.2 | High |
| 7 | Implement closest pair of points (divide & conquer) | §33.4 | High |

### Priority 3: Strengthen Specifications and Proofs

| # | Action | File | Est. Effort |
|---|---|---|---|
| 8 | Prove geometric correctness of `segments_intersect_spec` (intersection ↔ ∃ point on both) | Segments | High |
| 9 | Enforce collinearity precondition on `on_segment_spec` | Segments | Low |
| 10 | Prove `all_left_turns` is maintained as a loop invariant of Graham scan | GrahamScan | Medium |
| 11 | Connect GrahamScan complexity to O(n lg n) with merge-sort (not O(n²) insertion) | GrahamScan | Medium |
| 12 | Introduce `type point = { x: int; y: int }` record to reduce parameter counts | All | Medium |

### Priority 4: Cross-file Deduplication — ✅ COMPLETE

| # | Action | Notes |
|---|---|---|
| 13 | ✅ Deduplicate `cross_prod` | Graham Scan & Jarvis March now alias `Segments.Spec.cross_product_spec` |
| 14 | Deduplicate `find_bottom` / `find_leftmost` — structurally identical (min-y vs min-x) | Consider a generic `find_extreme` with a comparator parameter |

---

## Quality Checks

### Admits and Assumes

| File | `admit()` | `assume` | Verdict |
|---|---|---|---|
| `Segments.fst` | 0 | 0 | ✅ Clean |
| `GrahamScan.fst` | 0 | 0 | ✅ Clean |
| `JarvisMarch.fst` | 0 | 0 | ✅ Clean |

### Proof Robustness

| File | `#push-options` | rlimit | fuel/ifuel | Verdict |
|---|---|---|---|---|
| `Segments.*` | 0 | — | — | ✅ Default settings |
| `GrahamScan.Impl.fst` | 1 | — | `--fuel 2 --ifuel 0` (pop_while) | ✅ Modest |
| `GrahamScan.Lemmas.fst` | 1 | `--z3rlimit 20` | `--fuel 1 --ifuel 0` | ✅ Modest |
| `JarvisMarch.Lemmas.fst` | 3 | `--z3rlimit 10` (2×), `--z3rlimit 20` (1×) | — | ✅ Modest |
| `JarvisMarch.Impl.fst` | 2 | `--z3rlimit 120` (`jarvis_march_with_hull`) | `--fuel 2 --ifuel 0` | ⚠️ High rlimit |
| `JarvisMarch.fst` | 5 | `--z3rlimit 40` (max) | `--fuel 2 --ifuel 0` | ✅ Modest |

### Functional Equivalence Postconditions

All Pulse functions have postconditions proving `result == <pure_spec>(...)`:

| File | Pulse fns | All have spec-equivalence postcondition? |
|---|---|---|
| `Segments.fst` | `cross_product`, `direction`, `on_segment`, `segments_intersect` | ✅ Yes |
| `GrahamScan.fst` | `find_bottom`, `polar_cmp`, `pop_while`, `graham_scan_step` | ✅ Yes |
| `JarvisMarch.fst` | `find_leftmost`, `find_next`, `jarvis_march`, `jarvis_march_with_hull` | ✅ Yes |

### Correctness Depth

| Algorithm | Spec mirrors CLRS? | Independent correctness proof? | Geometric soundness? |
|---|---|---|---|
| Segments | ✅ Faithful to §33.1 | ❌ Spec is implementation mirror | ❌ No intersection ↔ geometry proof |
| Graham Scan | ✅ Faithful to §33.3 | 🔶 `is_bottommost` proved; `all_left_turns` defined but not proved as invariant | ❌ No convex-hull-contains-all-points proof |
| Jarvis March | ✅ Faithful to §33.3 | ✅ `find_next_all_left_of` proved under upper-half-plane + general position | 🔶 Requires assumptions (strict upper half-plane, general position) |

### Summary

**Chapter 33 is fully rubric-compliant in file structure.** All three algorithms
(Segments, Graham Scan, Jarvis March) have been decomposed into the rubric's 7-file
structure (Spec, Lemmas, Lemmas.fsti, Complexity, Complexity.fsti, Impl, Impl.fsti).
All 24 files (21 decomposed + 3 monolithic) verify with zero admits, zero assumes,
and zero warnings. Cross-product definitions in GrahamScan.Spec and JarvisMarch.Spec
alias Segments.Spec.cross_product_spec, eliminating duplication.

**Full build time**: ~2m30s (parallel, 4 jobs).

| Metric | Current | Target |
|---|---|---|
| Rubric-compliant files | 21 / 21 | 21 / 21 |
| Algorithms with complete Pulse impl | 2 / 3 | 3 / 3 (+ §33.2, §33.4) |
| .fsti interface files | 9 | 9 (3 × Lemmas + Complexity + Impl) |
| Cross-product definitions | 1 (shared via alias) | 1 (shared from Segments.Spec) |
| Max z3rlimit (decomposed) | 120 (`jarvis_march_with_hull`) | ≤ 40 |
| Warnings | 0 | 0 |
