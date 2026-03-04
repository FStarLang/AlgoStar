# Chapter 33: Computational Geometry — Rubric Compliance

## Current File Inventory

| File | Lines | Pure Specs | Lemmas | Pulse Impl | Complexity | .fsti |
|------|------:|:----------:|:------:|:----------:|:----------:|:-----:|
| `CLRS.Ch33.Segments.fst` | 205 | Inline | Inline (5) | 4 fns | Comment only | ❌ |
| `CLRS.Ch33.GrahamScan.fst` | 499 | Inline | Inline (5) | 3 fns (partial) | Inline (6 defs, 2 lemmas) | ❌ |
| `CLRS.Ch33.JarvisMarch.fst` | 702 | Inline | Inline (14) | 3 fns (full) | Inline (3 defs, 2 lemmas) | ❌ |

All three files are **monolithic**: specs, lemmas, Pulse implementations, and complexity
analysis are co-located in a single `.fst` file per algorithm. No file follows the
rubric's 7-file decomposition.

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
| `CLRS.Ch33.Segments.Spec.fst` | ❌ Missing | Specs are inline in `Segments.fst` (lines 20–64) |
| `CLRS.Ch33.Segments.Lemmas.fst` | ❌ Missing | 5 lemmas inline in `Segments.fst` (lines 78–102) |
| `CLRS.Ch33.Segments.Lemmas.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.Segments.Complexity.fst` | ❌ Missing | Only a comment; no formal defs |
| `CLRS.Ch33.Segments.Complexity.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.Segments.Impl.fst` | ❌ Missing | Pulse fns inline in `Segments.fst` (lines 104–201) |
| `CLRS.Ch33.Segments.Impl.fsti` | ❌ Missing | No interface file |

**Score: 0/7 files** — All content exists but in a single monolithic file.

### Graham Scan (§33.3)

| Required File | Status | Notes |
|---|---|---|
| `CLRS.Ch33.GrahamScan.Spec.fst` | ❌ Missing | Specs inline (lines 30–142) |
| `CLRS.Ch33.GrahamScan.Lemmas.fst` | ❌ Missing | Lemmas inline (lines 56–287) |
| `CLRS.Ch33.GrahamScan.Lemmas.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.GrahamScan.Complexity.fst` | ❌ Missing | Complexity inline (lines 465–498) |
| `CLRS.Ch33.GrahamScan.Complexity.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.GrahamScan.Impl.fst` | ❌ Missing | Pulse fns inline (lines 289–463); partial — no top-level `graham_scan` fn |
| `CLRS.Ch33.GrahamScan.Impl.fsti` | ❌ Missing | No interface file |

**Score: 0/7 files** — Content exists monolithically. Pulse impl is incomplete (helpers
only; no end-to-end `graham_scan` Pulse function; no polar-angle sorting step).

### Jarvis March (§33.3)

| Required File | Status | Notes |
|---|---|---|
| `CLRS.Ch33.JarvisMarch.Spec.fst` | ❌ Missing | Specs inline (lines 29–174) |
| `CLRS.Ch33.JarvisMarch.Lemmas.fst` | ❌ Missing | 14 lemmas inline (lines 60–461) |
| `CLRS.Ch33.JarvisMarch.Lemmas.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.JarvisMarch.Complexity.fst` | ❌ Missing | Complexity inline (lines 676–702) |
| `CLRS.Ch33.JarvisMarch.Complexity.fsti` | ❌ Missing | No interface file |
| `CLRS.Ch33.JarvisMarch.Impl.fst` | ❌ Missing | Pulse fns inline (lines 464–674); complete — `jarvis_march` fn present |
| `CLRS.Ch33.JarvisMarch.Impl.fsti` | ❌ Missing | No interface file |

**Score: 0/7 files** — Content exists monolithically. This is the most complete of the
three, with full Pulse implementation and substantial correctness proofs
(`find_next_all_left_of`, `half_plane_transitivity`).

### Overall Rubric Compliance

| Rubric Dimension | Segments | Graham Scan | Jarvis March |
|---|---|---|---|
| Separate Spec file | ❌ | ❌ | ❌ |
| Separate Lemmas file | ❌ | ❌ | ❌ |
| Lemmas .fsti | ❌ | ❌ | ❌ |
| Separate Complexity file | ❌ | ❌ | ❌ |
| Complexity .fsti | ❌ | ❌ | ❌ |
| Separate Impl file | ❌ | ❌ | ❌ |
| Impl .fsti | ❌ | ❌ | ❌ |
| Pure spec exists (anywhere) | ✅ | ✅ | ✅ |
| Pulse impl exists (anywhere) | ✅ | 🔶 Partial | ✅ |
| Impl postcondition = spec | ✅ | ✅ (for helpers) | ✅ |
| Zero admits | ✅ | ✅ | ✅ |
| Zero assumes | ✅ | ✅ | ✅ |
| Complexity analysis | 🔶 Comment | ✅ Formal | ✅ Formal |
| Correctness lemmas | 🔶 Algebraic only | 🔶 Partial | ✅ Substantial |

---

## Detailed Action Items

### Priority 1: File Decomposition (structural rubric compliance)

Each monolithic `.fst` must be split into the rubric's 7-file structure. The content
already exists; the work is mechanical extraction.

| # | Action | Source | Target Files | Est. Effort |
|---|---|---|---|---|
| 1a | Extract Segments specs | `Segments.fst` lines 18–76 | `Segments.Spec.fst` | Low |
| 1b | Extract Segments lemmas | `Segments.fst` lines 78–102 | `Segments.Lemmas.fst` + `.fsti` | Low |
| 1c | Create Segments complexity | New (O(1) for all) | `Segments.Complexity.fst` + `.fsti` | Low |
| 1d | Extract Segments Pulse impl | `Segments.fst` lines 104–201 | `Segments.Impl.fst` + `.fsti` | Low |
| 2a | Extract GrahamScan specs | `GrahamScan.fst` lines 28–181 | `GrahamScan.Spec.fst` | Low |
| 2b | Extract GrahamScan lemmas | `GrahamScan.fst` lines 183–287 | `GrahamScan.Lemmas.fst` + `.fsti` | Low |
| 2c | Extract GrahamScan complexity | `GrahamScan.fst` lines 465–498 | `GrahamScan.Complexity.fst` + `.fsti` | Low |
| 2d | Extract GrahamScan Pulse impl | `GrahamScan.fst` lines 289–463 | `GrahamScan.Impl.fst` + `.fsti` | Low |
| 3a | Extract JarvisMarch specs | `JarvisMarch.fst` lines 27–174 | `JarvisMarch.Spec.fst` | Low |
| 3b | Extract JarvisMarch lemmas | `JarvisMarch.fst` lines 176–461 | `JarvisMarch.Lemmas.fst` + `.fsti` | Medium |
| 3c | Extract JarvisMarch complexity | `JarvisMarch.fst` lines 676–702 | `JarvisMarch.Complexity.fst` + `.fsti` | Low |
| 3d | Extract JarvisMarch Pulse impl | `JarvisMarch.fst` lines 464–674 | `JarvisMarch.Impl.fst` + `.fsti` | Low |

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

### Priority 4: Cross-file Deduplication

| # | Action | Notes |
|---|---|---|
| 13 | Deduplicate `cross_prod` — defined identically in all 3 files | Graham Scan & Jarvis March should import from `Segments.Spec` |
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
| `Segments.fst` | 0 | — | — | ✅ Default settings |
| `GrahamScan.fst` | 1 | — | `--fuel 2 --ifuel 0` (pop_while) | ✅ Modest |
| `JarvisMarch.fst` | 3 | `--z3rlimit 10` (2×), `--fuel 2 --ifuel 0` (1×) | See left | ✅ Modest |

### Functional Equivalence Postconditions

All Pulse functions have postconditions proving `result == <pure_spec>(...)`:

| File | Pulse fns | All have spec-equivalence postcondition? |
|---|---|---|
| `Segments.fst` | `cross_product`, `direction`, `on_segment`, `segments_intersect` | ✅ Yes |
| `GrahamScan.fst` | `find_bottom`, `polar_cmp`, `pop_while` | ✅ Yes |
| `JarvisMarch.fst` | `find_leftmost`, `find_next`, `jarvis_march` | ✅ Yes |

### Correctness Depth

| Algorithm | Spec mirrors CLRS? | Independent correctness proof? | Geometric soundness? |
|---|---|---|---|
| Segments | ✅ Faithful to §33.1 | ❌ Spec is implementation mirror | ❌ No intersection ↔ geometry proof |
| Graham Scan | ✅ Faithful to §33.3 | 🔶 `is_bottommost` proved; `all_left_turns` defined but not proved as invariant | ❌ No convex-hull-contains-all-points proof |
| Jarvis March | ✅ Faithful to §33.3 | ✅ `find_next_all_left_of` proved under upper-half-plane + general position | 🔶 Requires assumptions (strict upper half-plane, general position) |

### Summary

**Chapter 33 is the least rubric-compliant chapter in the repository.** While the
algorithmic content is substantial — particularly Jarvis March with 14 inline lemmas
including a non-trivial transitivity proof — no file follows the rubric's 7-file
decomposition. All three files are monolithic. The primary remediation is mechanical
file splitting (Priority 1), followed by completing the Graham Scan Pulse implementation
(Priority 2) and strengthening correctness proofs (Priority 3).

| Metric | Current | Target |
|---|---|---|
| Rubric-compliant files | 0 / 21 | 21 / 21 |
| Algorithms with complete Pulse impl | 2 / 3 | 3 / 3 (+ §33.2, §33.4) |
| .fsti interface files | 0 | 9 (3 × Lemmas + Complexity + Impl) |
| Cross-product definitions | 3 (duplicated) | 1 (shared from Segments.Spec) |
