# Prim's Algorithm — Spec Validation Test

**File**: `CLRS.Ch23.Prim.ImplTest.fst`
**Status**: ✅ Verified (one `admit` for platform assumption `SZ.fits_u64`)

## Test Instance

3-vertex triangle graph (source = vertex 0):
```
  0 --1-- 1 --2-- 2
  |               |
  +------3--------+
```
Weight matrix (flat 3×3, SZ.t): `[0, 1, 3, 1, 0, 2, 3, 2, 0]`
Expected MST: edges `{(0,1) w=1, (1,2) w=2}`
Expected key array: `[0, 1, 2]` (key[v] = MST edge weight to v)
Expected parent array: `[0, 0, 1]` (parent[v] = MST parent of v)

## What Was Proven

### ✅ Precondition Satisfiability

| Precondition | Concrete Value | Status |
|--------------|---------------|--------|
| `SZ.v n > 0` | 3 > 0 | ✅ Automatic |
| `SZ.v n * SZ.v n < pow2 64` | 9 < 2⁶⁴ | ✅ Automatic |
| `SZ.v source < SZ.v n` | 0 < 3 | ✅ Automatic |
| `Seq.length weights_seq == n * n` | 9 == 9 | ✅ From array writes |
| `SZ.fits_u64` | Platform-specific | ⚠️ `admit()` (see below) |

### ✅ Partial Postcondition Verification

The postcondition `prim_correct` is **transparent** (defined as a `let` in
the `.fsti`), allowing partial verification:

```fstar
let prim_correct key_seq parent_seq weights_seq n source : prop =
  Seq.length key_seq == n /\
  Seq.length parent_seq == n /\
  source < n /\
  Seq.length weights_seq == n * n /\
  SZ.v (Seq.index key_seq source) == 0 /\
  all_keys_bounded key_seq /\
  SZ.v (Seq.index parent_seq source) == source
```

| Property | Verifiable? | How |
|----------|:-----------:|-----|
| `key[0] == 0` | ✅ | Read k0, assert `SZ.v k0 == 0` |
| `parent[0] == 0` | ✅ | Read p0, assert `SZ.v p0 == 0` |
| `key[1] <= 65535` | ✅ | From `all_keys_bounded` |
| `key[2] <= 65535` | ✅ | From `all_keys_bounded` |
| `key[1] == 1` | ❌ | Not in postcondition |
| `key[2] == 2` | ❌ | Not in postcondition |
| `parent[1] == 0` | ❌ | Not in postcondition |
| `parent[2] == 1` | ❌ | Not in postcondition |
| Result is spanning tree | ❌ | Not in postcondition |
| Result is MST | ❌ | Not in postcondition |

### ❌ Postcondition Precision

The postcondition only proves:
- **Shapes**: Array lengths are correct
- **Boundary**: `key[source] = 0`, `parent[source] = source`
- **Bounds**: All keys ≤ infinity (65535)

It does NOT prove any structural MST property.

## Admits and Assumptions

### 1. `SZ.fits_u64` (Platform Assumption)

```fstar
let assume_fits_u64 () : Lemma (ensures SZ.fits_u64) = admit ()
```

**Reason**: `SZ.fits_u64` is an abstract proposition asserting the platform's
`SizeT` type is at least 64 bits. It cannot be proven from first principles.
This is a platform deployment assumption, not a spec weakness.

**Classification**: Platform assumption (not a spec issue)

### 2. `drop_` for Returned Vecs (API Gap)

The `prim` function allocates and returns `(V.vec SZ.t & V.vec SZ.t)` but
its postcondition does **not** include `is_full_vec` for the returned vecs.
This prevents the caller from calling `V.free` on them. We use `drop_` to
discard the vec permissions.

**Classification**: API gap in `prim`'s postcondition (missing `is_full_vec`)

## Spec Weakness Analysis

### Root Cause: Weak Postcondition

`prim_correct` is a transparent `let` definition but only captures trivial
properties. The postcondition is essentially:
- "The arrays have the right lengths"
- "key[source] = 0 and parent[source] = source"
- "All keys are ≤ 65535"

This tells the caller almost nothing about the MST computation.

### Impact (Severity: High)

For any input graph, the postcondition admits infinitely many outputs.
For our 3-vertex triangle, `prim_correct` is satisfied by:
- key = `[0, 1, 2]`, parent = `[0, 0, 1]` (correct MST)
- key = `[0, 65535, 65535]`, parent = `[0, 0, 0]` (incorrect)
- key = `[0, 42, 99]`, parent = `[0, 2, 0]` (incorrect)

The postcondition cannot distinguish correct from incorrect outputs.

### Suggested Fix

Strengthen `prim_correct` to include:

1. **For each non-source vertex v**: `key[v] == weights[parent[v] * n + v]`
   (key equals the actual weight of the parent edge)
2. **Parent validity**: `parent[v] < n` for all v
3. **Tree structure**: The parent array induces a tree rooted at source
4. **Optimality**: The total weight is minimum (via MST bridge theorem)

The pure spec (`Prim.Spec`) already proves stronger properties (n-1 edges,
connectivity, safety). The gap is in linking the imperative output to the
pure specification.

## Conclusion

**Satisfiability**: ✓ proven (with platform assumption `SZ.fits_u64`)
**Completeness**: ✗ postcondition far too weak — admits incorrect outputs
**Additional API gap**: Missing `is_full_vec` for returned vecs
