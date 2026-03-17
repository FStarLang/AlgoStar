# Vertex Cover 2-Approximation — Spec Validation Test

**File:** `CLRS.Ch35.VertexCover.ImplTest.fst`
**Source:** Adapted from [microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
**Status:** ✅ Fully verified — zero admits, zero assumes

## What Is Tested

The test calls `approx_vertex_cover` on the complete graph K₃ (triangle on
3 vertices) and proves that the postcondition (`is_cover + binary + 2-approx
+ even count`) is:

1. **Satisfiable** — the function can be called with a valid 3×3 symmetric
   adjacency matrix.
2. **Precise** — the postcondition constrains the output to exactly 3
   admissible covers out of 8 possible binary vectors.

### Test Instance

| Property | Value |
|----------|-------|
| Graph | K₃ (complete graph on 3 vertices) |
| Vertices | {0, 1, 2} |
| Edges | {(0,1), (0,2), (1,2)} |
| Adjacency matrix | `[0,1,1, 1,0,1, 1,1,0]` |
| OPT (minimum vertex cover) | 2 |
| Algorithm output | One of: `[1,1,0]`, `[1,0,1]`, `[0,1,1]` |

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

From the postcondition's `is_cover`, `binary`, and `even count` properties,
the test proves:

**`triangle_cover_at_least_two`**: At least 2 of the 3 cover values must be 1.
This follows from the 3 edge constraints:
- Edge (0,1): `cover[0] = 1 ∨ cover[1] = 1`
- Edge (0,2): `cover[0] = 1 ∨ cover[2] = 1`
- Edge (1,2): `cover[1] = 1 ∨ cover[2] = 1`

**`triangle_cover_enumeration`**: The output must be one of exactly 3 valid covers:
- `[1,1,0]` (vertices 0,1) ✓
- `[1,0,1]` (vertices 0,2) ✓
- `[0,1,1]` (vertices 1,2) ✓

And the postcondition correctly **excludes** all 5 invalid covers:
- `[0,0,0]` — fails `is_cover` for edge (0,1)
- `[1,0,0]` — fails `is_cover` for edge (1,2)
- `[0,1,0]` — fails `is_cover` for edge (0,2)
- `[0,0,1]` — fails `is_cover` for edge (0,1)
- `[1,1,1]` — has count 3, which is odd; contradicts even count property

### 3. Even Count Property

The strengthened postcondition includes:
```
∃ k : nat. count_cover(cover) = 2 * k
```

This captures the algorithmic invariant that the 2-approximation algorithm
adds vertices in pairs (both endpoints of each uncovered edge). For K₃:
- The only even values in {2, 3} (at least 2 from is_cover, at most 3) is 2
- Therefore the cover has exactly 2 vertices
- This rules out `[1,1,1]`, narrowing from 4 to 3 admissible covers

### 4. 2-Approximation Bound Assessment

For K₃, OPT = 2. The 2-approximation bound gives `count ≤ 2 × 2 = 4`.
Since `n = 3`, the count is at most 3. Thus for this instance, the
`is_cover + binary + even count` constraints are strictly stronger than
the 2-approx bound.

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

Uses `triangle_cover_at_least_two` plus the even count property to establish
the 3-way disjunction. The proof rules out `[1,1,1]` because
`count_cover([1,1,1]) = 3` is odd, contradicting `∃ k. count = 2*k`.

## Spec Issues Found and Fixed

### Fixed: Missing `V.is_full_vec` in postcondition (prior round)

**Problem:** The original `Impl.fsti` postcondition did not expose
`V.is_full_vec cover`, even though the implementation allocates the Vec
with `V.alloc` (which guarantees `is_full_vec`). This prevented callers
from freeing the returned Vec via `V.free`.

**Fix:** Added `V.is_full_vec cover` to:
- The `pure(...)` clause in `Impl.fsti` postcondition
- Both loop invariants in `Impl.fst` (outer and inner)

### Fixed: Missing even count property in postcondition

**Problem:** The postcondition did not expose that the cover size is always
even. The algorithm adds vertices in pairs (both endpoints of each uncovered
edge), so `count_cover(cover) = 2 * |matching|`. Without this, the test could
not rule out `[1,1,1]` for K₃ (which has odd count 3 and is never produced).

**Fix:** Added `(exists (k: nat). count_cover(cover) = 2 * k)` to:
- The `Impl.fsti` postcondition
- The `Impl.fst` function signature
- Proved via `derive_even_count` lemma using `matching_cover_size` and
  `count_cover_ext` from the ghost matching

The fix narrows the K₃ test from 4 to 3 admissible covers (62.5% → 37.5%
of 8 binary vectors), improving spec precision.

## Spec Precision Result

**The postcondition is relational but maximally precise for a 2-approximation
algorithm.**

The specification captures four essential properties (valid cover, binary
output, 2-approximation bound, even count) without pinning down a specific
output. This is appropriate because different edge orderings lead to
different valid covers. For K₃:

- The postcondition admits 3 of 8 possible binary covers (37.5% precision)
- All 3 admissible covers are indeed valid 2-vertex covers (optimal for K₃)
- The specific output depends on edge scanning order (the algorithm
  with lexicographic order produces `[1,1,0]`)
- No admits or assumes were needed
