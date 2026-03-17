# Vertex Cover 2-Approximation — Spec Validation Test

**File:** `CLRS.Ch35.VertexCover.ImplTest.fst`
**Source:** Adapted from [microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
**Status:** ✅ Fully verified — zero admits, zero assumes

## What Is Tested

The test calls `approx_vertex_cover` on the complete graph K₃ (triangle on
3 vertices) and proves that the postcondition (`is_cover + binary + 2-approx`)
is:

1. **Satisfiable** — the function can be called with a valid 3×3 symmetric
   adjacency matrix.
2. **Precise** — the postcondition constrains the output to exactly 4
   admissible covers out of 8 possible binary vectors.

### Test Instance

| Property | Value |
|----------|-------|
| Graph | K₃ (complete graph on 3 vertices) |
| Vertices | {0, 1, 2} |
| Edges | {(0,1), (0,2), (1,2)} |
| Adjacency matrix | `[0,1,1, 1,0,1, 1,1,0]` |
| OPT (minimum vertex cover) | 2 |
| Algorithm output | One of: `[1,1,0]`, `[1,0,1]`, `[0,1,1]`, `[1,1,1]` |

## What Is Proven

### 1. Precondition Satisfiability

The test constructs a concrete 3×3 symmetric adjacency matrix and proves
all four preconditions of `approx_vertex_cover`:

- `SZ.v n > 0` (n = 3 > 0)
- `SZ.fits (SZ.v n * SZ.v n)` (fits 9)
- `Seq.length s_adj == SZ.v n * SZ.v n` (9 = 3 × 3)
- `Spec.is_symmetric_adj s_adj (SZ.v n)` (adjacency matrix is symmetric)

Z3 verifies the symmetry condition from the concrete array values without
any auxiliary lemmas.

### 2. Postcondition Precision

From the postcondition's `is_cover` and `binary` properties, the test proves:

**`triangle_cover_at_least_two`**: At least 2 of the 3 cover values must be 1.
This follows from the 3 edge constraints:
- Edge (0,1): `cover[0] = 1 ∨ cover[1] = 1`
- Edge (0,2): `cover[0] = 1 ∨ cover[2] = 1`
- Edge (1,2): `cover[1] = 1 ∨ cover[2] = 1`

**`triangle_cover_enumeration`**: The output must be one of exactly 4 valid covers:
- `[1,1,0]` (vertices 0,1) ✓
- `[1,0,1]` (vertices 0,2) ✓
- `[0,1,1]` (vertices 1,2) ✓
- `[1,1,1]` (all vertices) ✓

And the postcondition correctly **excludes** all 4 invalid covers:
- `[0,0,0]` — fails `is_cover` for edge (0,1)
- `[1,0,0]` — fails `is_cover` for edge (1,2)
- `[0,1,0]` — fails `is_cover` for edge (0,2)
- `[0,0,1]` — fails `is_cover` for edge (0,1)

### 3. 2-Approximation Bound Assessment

For K₃, OPT = 2. The 2-approximation bound gives `count ≤ 2 × 2 = 4`.
Since `n = 3`, the count is at most 3. Thus for this instance, the
`is_cover + binary` constraints are strictly stronger than the 2-approx
bound.

The 2-approximation bound becomes more discriminating on sparser graphs
(e.g., a star graph where OPT = 1 gives count ≤ 2, ruling out covers with
3+ vertices).

## Key Lemmas

### `is_cover_edge`

Extracts a single edge constraint from the universal quantifier in `is_cover`.
For specific `(u, v)` with `adj[u*n+v] ≠ 0`, derives `cover[u] ≠ 0 ∨ cover[v] ≠ 0`.
This helper is needed because Z3's E-matching may not automatically instantiate
the quantifier in `is_cover` for the non-linear index expression `u * n + v`.

### `triangle_cover_at_least_two`

Applies `is_cover_edge` for all three edges of K₃ to derive the 3 disjunctive
constraints on cover values.

### `triangle_cover_enumeration`

Uses `triangle_cover_at_least_two` to establish the 4-way disjunction. The
proof is by case analysis: with 3 binary variables constrained by 3 pairwise
disjunctions, exactly 4 of 8 assignments are valid.

## Spec Issues Found and Fixed

### Fixed: Missing `V.is_full_vec` in postcondition

**Problem:** The original `Impl.fsti` postcondition did not expose
`V.is_full_vec cover`, even though the implementation allocates the Vec
with `V.alloc` (which guarantees `is_full_vec`). This prevented callers
from freeing the returned Vec via `V.free`.

**Fix:** Added `V.is_full_vec cover` to:
- The `pure(...)` clause in `Impl.fsti` postcondition
- Both loop invariants in `Impl.fst` (outer and inner)

The fix is verified with zero admits and no increase in solver limits.

## Spec Precision Result

**The postcondition is relational but correct for a 2-approximation algorithm.**

The specification captures three essential properties (valid cover, binary
output, 2-approximation bound) without pinning down a specific output.
This is appropriate because different edge orderings lead to different valid
covers. For K₃:

- The postcondition admits 4 of 8 possible binary covers (50% precision)
- All 4 admissible covers are indeed valid vertex covers
- The specific output depends on edge scanning order (the algorithm
  with lexicographic order produces `[1,1,0]`)
- No admits or assumes were needed
