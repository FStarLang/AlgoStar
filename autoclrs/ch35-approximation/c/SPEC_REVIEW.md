# SPEC_REVIEW: C vs Impl.fsti Specification Gap Analysis

## Overview

Comparing the C code (`approxVertexCover.c`) specifications against
`CLRS.Ch35.VertexCover.Impl.fsti` for the 2-approximation vertex cover algorithm.

## Representation Differences

| Aspect | Impl.fsti (Pulse) | C code (c2pulse) |
|--------|-------------------|-------------------|
| Adjacency matrix | `array int` with `Seq.seq int` | `array Int32.t` with `Seq.seq (option Int32.t)` |
| Cover array | Returns `V.vec int` | Takes `_array int *cover` as output parameter |
| Index type | `SZ.t` | `size_t` (maps to `SZ.t`) |
| Bridge | Direct `Seq.seq int` | Uses `AVCBridgeLemmas.to_int_seq` to convert |

The `AVCBridgeLemmas` module bridges these representations via:
- `to_int_seq`: converts `Seq.seq (option Int32.t)` → `Seq.seq int`
- `to_int_seq_index`: relates pointwise: `Seq.index (to_int_seq s) i = seq_val s i`

## Precondition Comparison

| Precondition | Impl.fsti | C code | Status |
|-------------|-----------|--------|--------|
| `n > 0` | ✓ | ✓ | Match |
| `SZ.fits (n * n)` | ✓ | ✓ | Match |
| `Seq.length s_adj = n * n` | ✓ | ✓ (via `adj._length == n*n`) | Match |
| `is_symmetric_adj s_adj n` | ✓ | ✗ | **C is stronger** |

**Note on symmetry**: The C code does NOT require `is_symmetric_adj`. The algorithm
only scans upper-triangular entries (u < v), and the cover/approximation specs are
defined over upper-triangular edges only. The proof is valid without symmetry.
The Impl.fsti has a redundant precondition that the C code correctly omits.

## Postcondition Comparison

| Postcondition | Impl.fsti | C code | Status |
|--------------|-----------|--------|--------|
| `is_cover s_adj s_cover n n 0` | ✓ | ✓ | Match |
| Binary: `∀i<n. s_cover[i]=0 ∨ s_cover[i]=1` | ✓ (explicit) | ✓ (via `outer_inv_pure → binary`) | Match (indirect) |
| `∃opt. min_vertex_cover_size s_adj n opt` | ✓ | ✗ | **Gap — add to C** |
| `∀opt. min_vertex_cover_size ... ==> count_cover ... ≤ 2*opt` | ✓ | ✓ | Match |
| `∃k. count_cover ... = 2*k` | ✓ | ✓ | Match |
| `V.is_full_vec cover` | ✓ | N/A (different API) | N/A |
| `Seq.length s_cover = n` | ✓ | ✓ (via `cover._length == n`) | Match |

## Soundness Issues

### 1. `assume_` in AVCGhostStep.fst (CRITICAL)

The ghost function `matching_step_ghost` uses `assume_` to assume facts that
should be derivable from the calling context. This makes the proof **unsound**.

**Facts assumed (should be preconditions instead)**:
- `matching_inv_opt sa sc n vm` — available from loop invariant
- Bounds `u < n, v < n, u < v` — available from loop bounds
- `Seq.index sa (u*n+v) == Some he` — derivable from `array_read` + `array_initialized`
- `Seq.index sc u == Some cu`, `Seq.index sc v == Some cv` — same
- Conditional definitions of `new_cu`, `new_cv` — from if-then-else

**Fix**: Replace `assume_` with proper `pure` preconditions in the `requires` clause.

## Action Items

- [x] 1. Create SPEC_REVIEW.md
- [x] 2. Remove `assume_` from AVCGhostStep.fst — added proper pure preconditions
- [x] 3. Add `∃opt. min_vertex_cover_size ...` postcondition to C code
- [x] 4. Verify all modules build without admits/assumes
