# CLRS Chapter 33: Computational Geometry

This directory contains verified Pulse implementations of computational geometry
algorithms from CLRS Chapter 33, covering §33.1 segment primitives and §33.3
convex hull algorithms.

## Module: CLRS.Ch33.Segments

Implements line segment properties, intersection tests, and geometric orientation
lemmas from CLRS Section 33.1.

### Functions

#### 1. Cross Product (`cross_product`)
Computes the cross product (p2-p1) × (p3-p1) for three points.

**Formula:** `(x2-x1)*(y3-y1) - (x3-x1)*(y2-y1)`

#### 2. Direction Test (`direction`)
Wrapper around `cross_product` to determine orientation of three points.

#### 3. Point on Segment (`on_segment`)
Checks if a point lies on a segment (assumes collinearity).

#### 4. Segment Intersection (`segments_intersect`)
Determines if two line segments intersect using orientation tests (CLRS p.1017).

### Geometric Properties

The module proves several properties of the cross product:
- **Antisymmetry**: swapping p2 ↔ p3 negates the result
- **Orientation reversal**: swapping p2 ↔ p3 reverses CCW↔CW
- **Translation invariance**: shifting all points preserves orientation
- **Degenerate cases**: p2=p1 or p3=p1 gives collinear

A formal `orientation` type (`CCW | CW | Collinear`) connects the cross product
sign to geometric meaning.

### Verification
- ✅ NO admits, NO assumes
- ✅ All proofs automatic (no manual lemma invocations in Pulse)

---

## Module: CLRS.Ch33.JarvisMarch

Implements Jarvis's March (gift-wrapping) convex hull algorithm from CLRS §33.3.

### Pulse Functions

| Function | Spec | Description |
|---|---|---|
| `find_leftmost` | `find_leftmost_spec` | Find leftmost point (min x, then min y) |
| `find_next` | `find_next_spec` | Find next hull vertex (most clockwise turn) |
| `jarvis_march` | `jarvis_march_spec` | Complete convex hull computation |

### Algorithm
1. Start from the leftmost point (guaranteed on the hull)
2. At each step, find the point making the most clockwise turn
3. Repeat until returning to the start

### Proved Properties
- `find_leftmost_is_leftmost`: the starting point is the lexicographic minimum (x,y)
- `find_next_all_left_of`: all points lie to the left of each hull edge (**core Jarvis march correctness**, CLRS §33.3)
  - Uses `half_plane_transitivity`: algebraic proof that cross-product comparison is transitive in the upper half-plane
  - Preconditions: strict upper half-plane (all y[k] > y[current]) + general position (no collinear triples)
- `find_next_spec_not_current`: the next vertex is always distinct from current
- Result bounded: `1 <= h <= n` (`jarvis_march_spec_bounded`)
- Step lemma: `jarvis_loop_step` (single-step unfolding)

**Complexity:** O(nh) where n = input points, h = hull vertices. Proven: `jarvis_march_ops n h <= n * n`.

### Verification
- ✅ NO admits, NO assumes
- ✅ Complete Pulse implementation (outer loop + building blocks)
- ✅ `jarvis_march` proven equivalent to `jarvis_march_spec`

---

## Module: CLRS.Ch33.GrahamScan

Implements Graham's Scan convex hull algorithm from CLRS §33.3.

### Pulse Functions

| Function | Spec | Description |
|---|---|---|
| `find_bottom` | `find_bottom_spec` | Find bottom-most point (min y, then min x) |
| `polar_cmp` | `polar_cmp_spec` | Compare polar angles of two points w.r.t. pivot |
| `pop_while` | `pop_while_spec` | Pop hull stack while non-left turn |

### Pure Specifications

Complete pure specs for the full algorithm:
- `pop_non_left`: Pop stack while top elements don't make a left turn
- `scan_step`: One step of the scan (pop then push)
- `graham_loop`: Full scan loop over sorted points
- `graham_scan_sorted`: Complete algorithm given pre-sorted indices

### Algorithm
1. Find bottom-most point as pivot
2. Sort remaining points by polar angle w.r.t. pivot
3. Process sorted points: for each, pop non-left turns from stack, then push

### Proved Properties
- `find_bottom_is_bottommost`: the starting point is the lexicographic minimum (y,x)
- `pop_while_ensures_left_turn`: after popping, the top of the stack makes a left turn with the new point (**CLRS Theorem 33.1 maintenance step**)
- `all_left_turns` predicate: formalizes the Graham scan invariant (consecutive triples are all left turns)

**Complexity:** O(n lg n) dominated by sorting; scan loop is O(n) amortized.

### Verification
- ✅ NO admits, NO assumes
- ✅ Pulse: `find_bottom`, `polar_cmp`, `pop_while` proven equivalent to specs
- ✅ Pure specs: complete algorithm specified and type-checked
- ✅ Correctness: key loop invariant from CLRS Theorem 33.1 formally proven
- ⏳ Full Pulse scan loop and polar insertion sort: deferred (pure specs complete)

---

## Summary

| CLRS Algorithm | Section | Status |
|---|---|---|
| Cross product / Direction / On-segment | §33.1 | ✅ Fully verified |
| SEGMENTS-INTERSECT | §33.1 | ✅ Fully verified |
| Geometric orientation lemmas | §33.1 | ✅ Proved |
| Jarvis's March (gift wrapping) | §33.3 | ✅ Fully verified (complete Pulse) |
| Graham Scan | §33.3 | ✅ Specs + building blocks verified |
| ANY-SEGMENTS-INTERSECT | §33.2 | ❌ Requires balanced BST |
| Closest pair of points | §33.4 | ❌ Requires divide-and-conquer |
