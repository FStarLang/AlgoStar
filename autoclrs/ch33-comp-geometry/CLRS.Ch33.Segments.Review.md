# Segment Primitives (CLRS §33.1)

## Top-Level Signatures

Here are the top-level signatures proven about the segment primitives in
`CLRS.Ch33.Segments.Impl.fsti`:

### `cross_product`

```fstar
fn cross_product (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == cross_product_spec x1 y1 x2 y2 x3 y3)
```

### `direction`

```fstar
fn direction (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == direction_spec x1 y1 x2 y2 x3 y3)
```

### `on_segment`

```fstar
fn on_segment (x1 y1 x2 y2 x y: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == on_segment_spec x1 y1 x2 y2 x y)
```

### `segments_intersect`

```fstar
fn segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4)
```

### Parameters

All four functions take point coordinates as unbounded `int` values. Points
are represented as (x, y) pairs passed as separate arguments — there is no
point type.

### Preconditions

All functions require only `emp` — no heap resources, no size constraints.
These are pure computations lifted into Pulse.

### Postconditions

Each function's result is proven equal to its pure specification counterpart.
The `emp` resource is returned unchanged (no heap mutation).

## Auxiliary Definitions

### `cross_product_spec` (from `CLRS.Ch33.Segments.Spec`)

```fstar
let cross_product_spec (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)
```

This computes the cross product (p2−p1) × (p3−p1). A positive result means
p3 is to the left of line p1→p2 (counter-clockwise), negative means right
(clockwise), zero means collinear. This is the standard CLRS formula from
Section 33.1.

### `direction_spec` (from `CLRS.Ch33.Segments.Spec`)

```fstar
let direction_spec (x1 y1 x2 y2 x3 y3: int) : int =
  cross_product_spec x1 y1 x2 y2 x3 y3
```

`direction_spec` is a direct alias for `cross_product_spec`. The two
functions are intensionally equal.

### `on_segment_spec` (from `CLRS.Ch33.Segments.Spec`)

```fstar
let on_segment_spec (x1 y1 x2 y2 x y: int) : bool =
  (x <= max_int x1 x2) && (x >= min_int x1 x2) &&
  (y <= max_int y1 y2) && (y >= min_int y1 y2)
```

This checks whether point (x, y) lies within the bounding box of the segment
from (x1, y1) to (x2, y2). It is only meaningful when the three points are
known to be collinear (direction = 0), matching the CLRS usage.

### `segments_intersect_spec` (from `CLRS.Ch33.Segments.Spec`)

```fstar
let segments_intersect_spec (x1 y1 x2 y2 x3 y3 x4 y4: int) : bool =
  let d1 = direction_spec x3 y3 x4 y4 x1 y1 in
  let d2 = direction_spec x3 y3 x4 y4 x2 y2 in
  let d3 = direction_spec x1 y1 x2 y2 x3 y3 in
  let d4 = direction_spec x1 y1 x2 y2 x4 y4 in
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
      ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)))
  then true
  else if (d1 = 0 && on_segment_spec x3 y3 x4 y4 x1 y1) then true
  else if (d2 = 0 && on_segment_spec x3 y3 x4 y4 x2 y2) then true
  else if (d3 = 0 && on_segment_spec x1 y1 x2 y2 x3 y3) then true
  else if (d4 = 0 && on_segment_spec x1 y1 x2 y2 x4 y4) then true
  else false
```

This is the standard orientation-based segment intersection test from CLRS
Section 33.1. It first checks the general case (segments straddle each
other via opposite orientation signs), then handles the four collinear
special cases.

### `orientation` type (from `CLRS.Ch33.Segments.Spec`)

```fstar
type orientation = | CCW | CW | Collinear

let orient (x1 y1 x2 y2 x3 y3: int) : orientation =
  let cp = cross_product_spec x1 y1 x2 y2 x3 y3 in
  if cp > 0 then CCW
  else if cp < 0 then CW
  else Collinear
```

A convenience wrapper that classifies the cross product sign into a named
orientation. Used by other modules (Graham Scan, Jarvis March) but not
directly by the Pulse implementations in this module.

## What Is Proven

Each Pulse function is proven to return exactly the same value as its pure
specification. Since the functions are pure (no heap, no state), this is
**total functional equivalence**: the Pulse code is a verified translation
of the mathematical specification.

The specifications themselves are direct transcriptions of the CLRS
algorithms from Section 33.1:

* **Cross product** computes the standard 2D cross product formula.
* **Direction** is the orientation test.
* **On-segment** is the bounding-box check for collinear points.
* **Segments-intersect** is the full four-orientation + four-collinear-case
  algorithm from CLRS.

Five algebraic lemmas are proven in `CLRS.Ch33.Segments.Lemmas`:

* `cross_product_antisymmetric`: Swapping p2 ↔ p3 negates the cross product.
* `orient_antisymmetric`: Swapping p2 ↔ p3 reverses CCW ↔ CW.
* `cross_product_translation`: Translating all points preserves the cross product.
* `cross_product_degenerate_p2`: p2 = p1 implies cross product is 0.
* `cross_product_degenerate_p3`: p3 = p1 implies cross product is 0.

All lemma proofs are trivial (`= ()`), discharged entirely by SMT.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **No geometric correctness theorem.** The specification proves that the
   imperative code matches the pure formulas, but does not prove that the
   formulas correctly characterize geometric intersection. For example,
   there is no theorem stating "if `segments_intersect_spec` returns true,
   then the two line segments share a point in ℝ²." The correctness of the
   formulas is assumed from CLRS.

2. **Unbounded integers only.** All coordinates are F\*'s `int` type
   (mathematical, unbounded). There is no machine-integer overflow concern,
   but the functions cannot be directly compiled to fixed-width arithmetic.
   The cross product involves products of differences, which can overflow
   in practice for large coordinates.

3. **`on_segment_spec` assumes collinearity.** The bounding-box check is
   correct only when the three points are collinear. The specification does
   not enforce this as a precondition — it is the caller's responsibility
   (and `segments_intersect_spec` does check `d = 0` before calling it).

4. **No complexity tracking.** All four operations are O(1), performing a
   constant number of arithmetic operations. No ghost counter is used,
   which is appropriate given the trivial complexity.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| All operations | O(1) | N/A (constant) | N/A |

All four functions perform a fixed number of arithmetic operations and
comparisons. No complexity tracking is needed or provided.

## Proof Structure

The proofs are trivial: each Pulse function body mirrors the pure
specification exactly (same arithmetic, same control flow), so F\*'s
type-checker verifies the postcondition without any auxiliary lemmas.
The lemma module proves algebraic properties of the cross product
(antisymmetry, translation invariance, degeneracy) by SMT alone.

## Proof Robustness

All proofs use default settings (no `#push-options`, no rlimit increases,
no fuel/ifuel adjustments). All lemma proofs are trivial `= ()`.

**Verification time**: < 5 seconds (all files combined).

## Files

| File | Role |
|------|------|
| `CLRS.Ch33.Segments.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch33.Segments.Impl.fst` | Pulse implementation |
| `CLRS.Ch33.Segments.Spec.fst` | Pure specifications and orientation type |
| `CLRS.Ch33.Segments.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch33.Segments.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch33.Segments.Complexity.fsti` | Complexity interface |
| `CLRS.Ch33.Segments.Complexity.fst` | Formal O(1) op counts and bounds |
| `CLRS.Ch33.Segments.fst` | Standalone module (specs + proofs + Pulse, all-in-one) |

## Checklist (Priority Order)

- [x] Pure specification matching CLRS §33.1
- [x] Pulse implementation with `result == *_spec` postconditions
- [x] Impl.fsti interface file
- [x] Lemmas module with algebraic properties (antisymmetry, translation, degeneracy)
- [x] Lemmas.fsti interface file
- [x] Complexity module with formal O(1) op counts
- [x] Complexity.fsti interface file
- [x] Zero admits, zero assumes
- [x] Proof stability — all proofs use default solver settings
- [ ] Geometric correctness theorem (intersection ↔ ∃ shared point in ℝ²) — **deferred** (would need real-number geometry formalization)
- [ ] Enforce collinearity precondition on `on_segment_spec` — **low priority** (callers already check `d = 0`)
- [ ] Introduce `type point = { x: int; y: int }` record — **low priority** (cross-cutting refactor)
