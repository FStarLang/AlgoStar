# Audit Report — Chapter 33: Computational Geometry (Segments)

**File audited:** `ch33-comp-geometry/CLRS.Ch33.Segments.fst` (185 lines)
**Date:** 2025-07-15
**CLRS Reference:** Chapter 33 — Computational Geometry (Sections 33.1–33.4)

---

## 1. CLRS Fidelity

### Algorithms Implemented

| CLRS Algorithm | Section | Implemented | Notes |
|---|---|---|---|
| Cross product | §33.1 | ✅ | `cross_product` / `cross_product_spec` — computes (p2−p1) × (p3−p1) |
| DIRECTION(pi, pj, pk) | §33.1 | ✅ | `direction` / `direction_spec` — thin wrapper over cross product |
| ON-SEGMENT(pi, pj, pk) | §33.1 | ✅ | `on_segment` / `on_segment_spec` — bounding-box containment check |
| SEGMENTS-INTERSECT(p1,p2,p3,p4) | §33.1 | ✅ | `segments_intersect` / `segments_intersect_spec` — orientation-based test |
| ANY-SEGMENTS-INTERSECT(S) | §33.2 | ❌ | Not implemented |
| GRAHAM-SCAN(Q) | §33.3 | ❌ | Not implemented |
| Jarvis's march | §33.3 | ❌ | Not implemented |
| Closest pair (divide & conquer) | §33.4 | ❌ | Not implemented |

### Fidelity of Implemented Algorithms

The SEGMENTS-INTERSECT implementation faithfully follows the CLRS pseudocode (p. 1017–1018):

- **Lines 1–4** (compute d1–d4 via DIRECTION): Correctly mapped at lines 131–134 of the `.fst` file. The argument order matches CLRS exactly: `d1 = DIRECTION(p3,p4,p1)`, etc.
- **Line 5–6** (general straddling case): Correctly implemented at lines 137–142.
- **Lines 7–14** (collinear special cases): Correctly implemented at lines 145–158 with the same four checks in the same order as CLRS.
- **Line 15** (else FALSE): Correctly implemented via the final `case4` fallthrough at line 158.

DIRECTION is a direct cross-product return, matching CLRS exactly. ON-SEGMENT uses min/max bounding-box containment, matching CLRS.

**Verdict: §33.1 is faithfully implemented. §33.2–§33.4 are entirely absent.**

---

## 2. Specification Strength

### What Is Proven

Each Pulse `fn` has a postcondition proving functional equivalence to a pure spec:

| Function | Postcondition |
|---|---|
| `cross_product` | `result == cross_product_spec x1 y1 x2 y2 x3 y3` (line 72) |
| `direction` | `result == direction_spec x1 y1 x2 y2 x3 y3` (line 99) |
| `on_segment` | `result == on_segment_spec x1 y1 x2 y2 x y` (line 109) |
| `segments_intersect` | `result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4` (line 127) |

### What Is NOT Proven

- **Geometric correctness**: No proof that the cross-product sign actually indicates orientation (CW/CCW/collinear). The spec functions are just definitions; no lemma connects them to geometric meaning.
- **Intersection soundness/completeness**: No proof that `segments_intersect_spec` returns `true` iff the two segments geometrically intersect. This is the most important missing property—the spec itself is unverified against a mathematical definition of segment intersection.
- **No precondition on ON-SEGMENT**: The comment says "assumes the three points are collinear" but this is not enforced in the type—callers could pass non-collinear points and get a meaningless result.

### Specification Assessment

The specs are **implementation mirrors**—they restate the algorithm rather than expressing an independent geometric property. The proofs establish "the code computes what the spec says" but do not establish "the spec is geometrically correct." This is a common pattern in the AutoCLRS library. For these O(1) computational geometry primitives the main value is in getting the formula right, and the spec does serve as readable documentation.

---

## 3. Complexity

### Stated Complexity (lines 166–184)

```fstar
let cross_product_ops : nat = 3        // 3 arithmetic ops (2 muls + 1 sub)
let direction_ops : nat = 3            // delegates to cross_product
let on_segment_ops : nat = 4           // 4 comparisons
let segments_intersect_ops : nat = 16  // 4 directions + up to 4 on_segment checks
```

Two trivial lemmas:
- `all_constant`: sum of all op counts ≤ 30 (line 176–178)
- `segments_intersect_composition`: `segments_intersect_ops ≤ 4 * direction_ops + 2 * on_segment_ops` (lines 181–183)

### Assessment

- All operations are O(1) as stated, which is correct.
- The op counts are just `nat` constants with no connection to the actual code—they are not derived from the implementations.
- `cross_product_ops = 3` is slightly off: the implementation performs 4 subtractions and 2 multiplications and 1 final subtraction = 7 arithmetic operations (or 5 if counting sub+mul+sub). The constant 3 appears to count only major operations (2 multiplies + 1 subtract).
- `segments_intersect_ops = 16` is not justified by any derivation.
- The composition lemma claims `16 ≤ 4*3 + 2*4 = 20`, which is trivially true but gives a loose bound.
- **No connection to CLRS complexity analysis.** The CLRS chapter discusses O(n lg n) for ANY-SEGMENTS-INTERSECT and O(n lg n) / O(nh) for convex hull algorithms—none of which are implemented.

---

## 4. Code Quality

### Structure

The file is well-organized into three sections:
1. **Pure Specifications** (lines 18–64): Four pure functions
2. **Pulse Implementations** (lines 66–163): Four Pulse `fn` functions
3. **Complexity Analysis** (lines 165–184): Op-count constants and lemmas

### Points Representation

Points are passed as individual `int` coordinates (e.g., `x1 y1 x2 y2 x3 y3`), not as structured types. `segments_intersect` takes 8 `int` parameters. This is functional but unwieldy—a `point` record type would improve readability.

### Memory Model

All functions use `emp` (empty heap) for pre/postconditions—no heap allocation, no mutation. These are effectively pure functions wrapped in Pulse syntax. The Pulse wrapper adds no value over pure F* for these particular functions.

### Missing Content from CLRS Ch33

| Missing | CLRS Section | Complexity | Difficulty |
|---|---|---|---|
| ANY-SEGMENTS-INTERSECT | §33.2 | O(n lg n) | High — requires sweep-line with balanced BST (red-black tree) |
| GRAHAM-SCAN | §33.3 | O(n lg n) | Medium — requires sorting + stack |
| Jarvis's march | §33.3 | O(nh) | Medium — requires polar-angle comparisons |
| Closest pair of points | §33.4 | O(n lg n) | High — divide-and-conquer with merge step |

The implemented file covers only the **primitive building blocks** from §33.1. The four main algorithms of Ch33 (sweep-line intersection detection, two convex hull algorithms, closest pair) are all missing.

### Is This a Stub?

**No**—it is a complete, verified implementation of CLRS §33.1's three procedures (DIRECTION, ON-SEGMENT, SEGMENTS-INTERSECT) and the cross-product primitive. However, it covers only ~25% of Ch33's algorithmic content by section count and 0% of the chapter's non-trivial algorithms (those requiring data structures, sorting, or divide-and-conquer).

---

## 5. Proof Quality

### Admits and Assumes

**Zero `admit()` calls.** ✅
**Zero `assume` calls.** ✅

This is confirmed by grep—the only occurrences of "admit" and "assume" in the file are in comments (lines 10 and 39).

### Proof Effort

All proofs are **automatic**—no manual lemma invocations, no `assert` chains, no `calc` blocks. The SMT solver handles everything. This is expected for O(1) arithmetic functions with no loops or recursion.

### Robustness

No `#set-options` for rlimit or fuel/ifuel adjustments appear in the file. The proofs rely on default settings, suggesting they are stable and lightweight.

---

## 6. Documentation Accuracy

### Module Header (lines 1–11)
- ✅ Correctly lists the two main capabilities (cross product, segment intersection)
- ✅ Correctly cites §33.1
- ✅ "NO admits. NO assumes." — **verified accurate**

### README.md
- ✅ Accurately describes all four functions with correct signatures
- ✅ Algorithm description matches CLRS
- ⚠️ Claims "All rlimits < 0.1"—this is plausible but unverifiable without running the checker with `--query_stats`
- ⚠️ References "page 1017" for SEGMENTS-INTERSECT—correct for CLRS 3rd edition
- ✅ Section "Properties" correctly describes the spec-equivalence proofs

### Inline Comments
- ✅ Cross-product formula comment (line 25) is correct
- ✅ Orientation semantics (lines 27–29) are correct (positive = left/CCW, negative = right/CW, zero = collinear)
- ⚠️ Line 39: "Assumes the three points are collinear" is a documentation-only precondition, not enforced in the type

---

## 7. Task List — Missing CLRS Ch33 Algorithms

### Priority 1: Core Algorithms

| # | Algorithm | Section | Est. Difficulty | Dependencies |
|---|---|---|---|---|
| 1 | ANY-SEGMENTS-INTERSECT | §33.2 | Hard | Requires balanced BST (Ch13 red-black tree), sorting, sweep-line logic |
| 2 | GRAHAM-SCAN | §33.3 | Medium | Requires sorting by polar angle (uses cross product), stack operations |
| 3 | Jarvis's march | §33.3 | Medium | Requires polar-angle minimum finding (uses cross product) |
| 4 | Closest pair of points | §33.4 | Hard | Requires divide-and-conquer, sorting, merge-strip logic |
| 5 | Geometric soundness of cross product | Prove cross_product_spec > 0 ↔ CCW orientation (relative to a formal definition) |
| 6 | Intersection correctness | Prove `segments_intersect_spec` ↔ geometric intersection (∃ point on both segments) |
| 7 | Point type abstraction | Introduce `type point = { x: int; y: int }` to reduce parameter count |

### Defer

CLRS §33.1 includes 8 exercises (33.1-1 through 33.1-8) covering:
- Cross-product orientation proof (33.1-1)
- Intersection of two segments (33.1-2) — already done
- Polar-angle sorting via cross products (33.1-3)
- Segment intersection with axis-aligned segments (33.1-4)
- Simple polygon definition and intersection counting (33.1-5, 33.1-6)
- Point-in-polygon test (33.1-7)
- Simple polygon determination (33.1-8)

---

## Summary

| Dimension | Rating | Notes |
|---|---|---|
| CLRS Fidelity | ⭐⭐⭐ (§33.1 only) | §33.1 faithfully implemented; §33.2–§33.4 entirely missing |
| Specification Strength | ⭐⭐ | Specs mirror implementations; no geometric correctness proofs |
| Complexity | ⭐⭐ | O(1) is trivially correct; op counts are ad-hoc constants |
| Code Quality | ⭐⭐⭐⭐ | Clean, well-structured, readable; coordinate-based API is verbose |
| Proof Quality | ⭐⭐⭐⭐⭐ | Zero admits, zero assumes, fully automatic proofs |
| Documentation | ⭐⭐⭐⭐ | Accurate README and comments; minor unchecked claims |

**Overall: A solid, clean, fully-verified implementation of CLRS §33.1 primitives. The chapter is ~25% complete—all four non-trivial algorithms (sweep-line, Graham scan, Jarvis march, closest pair) remain to be implemented.**
