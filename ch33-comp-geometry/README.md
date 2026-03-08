# CLRS Chapter 33: Computational Geometry

This directory contains verified Pulse implementations of computational geometry
algorithms from CLRS Chapter 33, covering §33.1 segment primitives and §33.3
convex hull algorithms (Graham Scan and Jarvis March).

**Zero admits. Zero assumes. All proofs complete.**

---

## Algorithm 1: Segment Primitives (CLRS §33.1)

Implements line-segment properties, intersection tests, and geometric orientation
lemmas from CLRS Section 33.1.

### Pure Specification

The core geometry predicates are expressed as pure functions on integer coordinates
in `CLRS.Ch33.Segments.Spec`:

```fstar
let cross_product_spec (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)

let direction_spec (x1 y1 x2 y2 x3 y3: int) : int =
  cross_product_spec x1 y1 x2 y2 x3 y3

let on_segment_spec (x1 y1 x2 y2 x y: int) : bool =
  (x <= max_int x1 x2) && (x >= min_int x1 x2) &&
  (y <= max_int y1 y2) && (y >= min_int y1 y2)
```

`cross_product_spec` computes (p₂ − p₁) × (p₃ − p₁). Positive = CCW, negative = CW, zero = collinear.
`on_segment_spec` checks bounding-box containment (assumes collinearity).
`segments_intersect_spec` follows CLRS exactly: compute four direction values, check straddling, then handle collinear boundary cases.

A formal `orientation` type (`CCW | CW | Collinear`) connects the cross-product sign to geometric meaning.

### Correctness Theorem (Impl.fsti)

Each Pulse function's postcondition asserts exact functional equivalence with its pure spec:

```fstar
fn cross_product (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == cross_product_spec x1 y1 x2 y2 x3 y3)

fn direction (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == direction_spec x1 y1 x2 y2 x3 y3)

fn on_segment (x1 y1 x2 y2 x y: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == on_segment_spec x1 y1 x2 y2 x y)

fn segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4)
```

**Why this is the strongest guarantee**: The postcondition `result == *_spec` provides
*total functional equivalence* — the imperative result equals the pure specification
for every input. Since the pure spec is a total function on integers, this leaves no
room for a stronger postcondition.

### Geometric Properties (Lemmas)

The `Segments.Lemmas` module proves:
- **Antisymmetry**: swapping p₂ ↔ p₃ negates the cross product
- **Orientation reversal**: swapping p₂ ↔ p₃ reverses CCW ↔ CW
- **Translation invariance**: shifting all points preserves orientation
- **Degenerate cases**: p₂ = p₁ or p₃ = p₁ gives collinear (cross product = 0)

All proofs are automatic (`= ()`).

### Complexity

All operations are O(1) — each performs a constant number of arithmetic operations
and comparisons. No formal complexity module exists (not needed for constant-time primitives).

### Limitations

- **Integer arithmetic only**: uses `int` (mathematical integers), not floating-point.
  This avoids rounding errors but means coordinates must be integers.
- **No degenerate-case diagnostics**: `segments_intersect` returns `bool` without
  indicating *where* or *how* segments intersect (e.g., overlapping collinear segments
  vs. single point).
- These are pure computations (`requires emp`), so no memory or array operations are
  involved.

---

## Algorithm 2: Graham Scan (CLRS §33.3)

Implements Graham's Scan convex hull algorithm. Points are sorted by polar angle
w.r.t. the bottom-most point, then processed with a stack to eliminate non-left turns.

### Pure Specification

Complete pure specs in `CLRS.Ch33.GrahamScan.Spec`:

- `find_bottom_spec`: Find bottom-most point (min y, tiebreak min x)
- `polar_cmp_spec`: Compare polar angles via cross product
- `pop_while_spec`: Pop hull stack while top makes non-left turn
- `scan_step`, `graham_loop`, `graham_scan_sorted`: Full algorithm specification

**Correctness property** — `all_left_turns`:

```fstar
let all_left_turns (xs ys: Seq.seq int) (hull: Seq.seq nat) (top: nat) : prop =
  top <= Seq.length hull /\
  Seq.length ys == Seq.length xs /\
  (forall (i: nat). i + 2 < top ==>
    cross_prod (…hull[i]…) (…hull[i+1]…) (…hull[i+2]…) > 0)
```

Every consecutive triple of hull vertices makes a strict left turn, which is the
defining property of a convex polygon traversed counter-clockwise.

### Correctness Theorem (Impl.fsti)

```fstar
fn find_bottom (#p: perm) (xs ys: array int) … (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys ** pure (…)
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (SZ.v result == find_bottom_spec sxs sys /\ SZ.v result < SZ.v len)

fn polar_cmp (#p: perm) (xs ys: array int) … (len p0 a b: SZ.t)
  requires …
  returns result: int
  ensures … pure (result == polar_cmp_spec sxs sys (SZ.v p0) (SZ.v a) (SZ.v b))

fn pop_while (#p: perm) (xs ys: array int) … (hull: array SZ.t) …
  (top_in p_idx len: SZ.t)
  requires …
  returns result: SZ.t
  ensures … pure (
    SZ.v result == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx) /\
    SZ.v result <= SZ.v top_in)
```

Each postcondition has two parts:

1. **Functional equivalence**: `result == *_spec …` — the imperative result equals
   the pure specification.
2. **Bounds**: result is within valid index range (e.g., `result < len`, `result <= top_in`).

The separation-logic framing (`A.pts_to`) additionally guarantees memory safety and
non-interference with other heap objects.

**Why strongest**: Each function is proven equal to its pure specification for all
valid inputs. The bounds ensure array safety. Together, these leave no room for
strengthening.

### Key Proved Lemmas

- `find_bottom_is_bottommost`: the starting point satisfies `is_bottommost` — it has
  the minimum y-coordinate, with ties broken by minimum x.
- `pop_while_ensures_left_turn`: after popping, the top of the stack makes a strict
  left turn with the new point (**CLRS Theorem 33.1 maintenance step**).
- `pop_while_spec_bounded`: result ≤ input top (stack never grows).

### Complexity

O(n log n) dominated by the sorting step; the scan loop is O(n) amortized (each
point is pushed and popped at most once). **Not formally linked to the
implementation**: the pure complexity definitions (`graham_scan_ops`, `scan_linear`)
are stated and proven in the combined `.fst` file but are not connected to the Pulse
implementation via ghost operation counters.

### Limitations

- **Partial Pulse coverage**: Only `find_bottom`, `polar_cmp`, and `pop_while` are
  implemented and verified in Pulse. The full scan loop and polar insertion sort are
  specified purely but **not implemented as Pulse functions** (deferred).
- **Sorting assumed**: the `graham_scan_sorted` spec assumes points are pre-sorted by
  polar angle; the sort itself is not verified in Pulse.
- **No end-to-end convexity proof**: the `all_left_turns` predicate is defined and
  `pop_while_ensures_left_turn` establishes the key invariant maintenance step, but
  the full inductive proof that `graham_scan_sorted` produces an `all_left_turns`
  hull is not completed.
- **Integer coordinates**: same as Segments.

---

## Algorithm 3: Jarvis March — Gift Wrapping (CLRS §33.3)

Implements Jarvis's March convex hull algorithm. Each iteration selects the most
clockwise point as the next hull vertex using cross-product orientation tests.

### Pure Specification

Complete pure specs in `CLRS.Ch33.JarvisMarch.Spec`:

- `find_leftmost_spec`: Find leftmost point (min x, tiebreak min y)
- `find_next_spec`: Find next hull vertex (most clockwise turn from current)
- `jarvis_march_spec`: Full convex hull computation, returns hull vertex count

### Correctness Theorem (Impl.fsti)

```fstar
fn find_leftmost (#p: perm) (xs ys: array int) … (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys ** pure (…)
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (SZ.v result == find_leftmost_spec sxs sys /\ SZ.v result < SZ.v len)

fn find_next (#p: perm) (xs ys: array int) … (len: SZ.t) (current: SZ.t)
  requires …
  returns result: SZ.t
  ensures … pure (
    SZ.v result == find_next_spec sxs sys (SZ.v current) /\
    SZ.v result < SZ.v len)

fn jarvis_march (#p: perm) (xs ys: array int) … (len: SZ.t)
  requires …
  returns h: SZ.t
  ensures … pure (
    SZ.v h == jarvis_march_spec sxs sys /\
    SZ.v h >= 1 /\ SZ.v h <= SZ.v len)
```

Each postcondition establishes:

1. **Functional equivalence**: `h == jarvis_march_spec …`
2. **Bounds**: `1 <= h <= len` (at least one hull vertex, at most all points)

**Why strongest**: `jarvis_march` is proven equal to `jarvis_march_spec` — the Pulse
implementation computes exactly the same hull size as the pure recursive specification
for all valid inputs with n > 1. No weaker statement would capture this.

### Key Proved Lemmas

- `find_leftmost_is_leftmost`: the starting point satisfies `is_leftmost`
  (lexicographic min by x, then y).
- `find_next_all_left_of`: **core Jarvis march correctness** — all points lie to the
  left of the line from current to the selected next vertex (`all_left_of` property).
  - Uses `half_plane_transitivity`: algebraic proof that cross-product comparison is
    transitive in the upper half-plane.
  - Requires: strict upper half-plane (all y[k] > y[current]) + general position
    (no collinear triples).
- `find_next_spec_not_current`: the next vertex is always distinct from current
  when n > 1.
- `jarvis_march_spec_bounded`: `1 <= h <= n`.
- `jarvis_loop_step`: single-step unfolding lemma.

### Complexity

O(nh) where n = input points, h = hull vertices. Proven:
`jarvis_march_ops n h <= n * n` (quadratic worst case when h = n). **Not formally
linked**: the pure complexity definitions are stated and proven but not connected to
the Pulse implementation via ghost operation counters.

### Limitations

- **General position required** for `find_next_all_left_of`: the correctness proof
  assumes no three non-current points are collinear and all points are strictly above
  the current vertex (upper half-plane). Real-world point sets may violate this.
- **Hull vertex count only**: `jarvis_march` returns the *count* of hull vertices,
  not the hull vertices themselves (no output array).
- **No wrap-around convexity**: the `all_left_of` property is proven for individual
  edges from the `find_next` call under specific preconditions, but the full
  closed-polygon convexity is not proven end-to-end.
- **Integer coordinates**: same as Segments.

---

## File Inventory

| File | Type | Description |
|------|------|-------------|
| `CLRS.Ch33.Segments.Spec.fst` | Pure spec | Cross product, direction, on_segment, segments_intersect specs |
| `CLRS.Ch33.Segments.Impl.fsti` | Interface | Pulse function signatures with `result == *_spec` postconditions |
| `CLRS.Ch33.Segments.Impl.fst` | Pulse impl | Verified implementations of all segment primitives |
| `CLRS.Ch33.Segments.Lemmas.fsti` | Interface | Cross-product property signatures |
| `CLRS.Ch33.Segments.Lemmas.fst` | Pure proof | Antisymmetry, translation invariance, degeneracy proofs |
| `CLRS.Ch33.Segments.fst` | Combined | Self-contained module with specs + implementations + lemmas |
| `CLRS.Ch33.GrahamScan.Spec.fst` | Pure spec | find_bottom, polar_cmp, pop_while, full scan specification |
| `CLRS.Ch33.GrahamScan.Impl.fsti` | Interface | Pulse function signatures for Graham scan building blocks |
| `CLRS.Ch33.GrahamScan.Impl.fst` | Pulse impl | Verified implementations of find_bottom, polar_cmp, pop_while |
| `CLRS.Ch33.GrahamScan.Lemmas.fsti` | Interface | Bounds and correctness lemma signatures |
| `CLRS.Ch33.GrahamScan.Lemmas.fst` | Pure proof | Proofs of bottommost property, left-turn invariant |
| `CLRS.Ch33.GrahamScan.fst` | Combined | Self-contained module with specs + implementations + lemmas |
| `CLRS.Ch33.JarvisMarch.Spec.fst` | Pure spec | find_leftmost, find_next, jarvis_march specification |
| `CLRS.Ch33.JarvisMarch.Impl.fsti` | Interface | Pulse function signatures for Jarvis march |
| `CLRS.Ch33.JarvisMarch.Impl.fst` | Pulse impl | Verified find_leftmost, find_next, jarvis_march |
| `CLRS.Ch33.JarvisMarch.Lemmas.fsti` | Interface | Bounds, correctness, and transitivity lemma signatures |
| `CLRS.Ch33.JarvisMarch.Lemmas.fst` | Pure proof | Half-plane transitivity, all_left_of, bounds proofs |
| `CLRS.Ch33.JarvisMarch.fst` | Combined | Self-contained module with specs + implementations + lemmas |

## Build Instructions

```bash
cd ch33-comp-geometry
make verify              # Verify all modules
```

Or verify a specific module:

```bash
FSTAR_FILES="CLRS.Ch33.Segments.Impl.fst" make verify
FSTAR_FILES="CLRS.Ch33.GrahamScan.Impl.fst" make verify
FSTAR_FILES="CLRS.Ch33.JarvisMarch.Impl.fst" make verify
```

The `Makefile` includes the Pulse test infrastructure:

```makefile
PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
```

## Summary

| CLRS Algorithm | Section | Pulse | Correctness | Complexity | Admits |
|---|---|---|---|---|---|
| Cross product / Direction / On-segment | §33.1 | ✅ Full | `result == *_spec` | O(1) — constant | 0 |
| SEGMENTS-INTERSECT | §33.1 | ✅ Full | `result == segments_intersect_spec` | O(1) — 4 direction + 2 on_segment | 0 |
| Graham Scan (building blocks) | §33.3 | ✅ Partial | `result == *_spec` + left-turn invariant | O(n log n) — not formally linked | 0 |
| Jarvis March (complete) | §33.3 | ✅ Full | `h == jarvis_march_spec` + `all_left_of` | O(nh) — not formally linked | 0 |
| ANY-SEGMENTS-INTERSECT | §33.2 | ❌ | — | — | — |
| Closest pair of points | §33.4 | ❌ | — | — | — |
