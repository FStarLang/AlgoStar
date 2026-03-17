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

### ✅ Postcondition Verification

The postcondition `prim_correct` is **transparent** (defined as a `let` in
the `.fsti`), allowing verification of its conjuncts:

| Property | Verifiable? | How |
|----------|:-----------:|-----|
| `key[0] == 0` | ✅ | Read k0, assert `SZ.v k0 == 0` |
| `parent[0] == 0` | ✅ | Read p0, assert `SZ.v p0 == 0` |
| `key[i] <= 65535` for all i | ✅ | From `all_keys_bounded` |
| `parent[0] < 3` | ✅ | From `parent_valid` |
| `parent[1] < 3` | ✅ | From `parent_valid` |
| `parent[2] < 3` | ✅ | From `parent_valid` |
| `key[1] == 1` | ❌ | Not in postcondition |
| `key[2] == 2` | ❌ | Not in postcondition |
| `parent[1] == 0` | ❌ | Not in postcondition |
| `parent[2] == 1` | ❌ | Not in postcondition |
| Result is spanning tree | ❌ | Not in postcondition |
| Result is MST | ❌ | Not in postcondition |

## Spec Improvement Made

### Added: `parent_valid` to `prim_correct` (Impl.fsti)

```fstar
let parent_valid (parent_seq: Seq.seq SZ.t) (n: nat) : prop =
  forall (v:nat). v < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq v) < n
```

This ensures all parent array entries are valid vertex indices (< n).
Previously, the postcondition said nothing about parent values for
non-source vertices — they could be arbitrary. Now they are constrained
to be valid vertices, ruling out many incorrect outputs.

### Also defined (not yet tracked through Pulse loops): `key_parent_consistent`

```fstar
let key_parent_consistent
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  forall (v:nat). (v < n /\ v <> source /\ ... /\
    SZ.v (Seq.index key_seq v) < SZ.v infinity) ==>
    SZ.v (Seq.index key_seq v) ==
      SZ.v (Seq.index weights_seq (SZ.v (Seq.index parent_seq v) * n + v))
```

This property (key[v] equals the weight of the edge to parent[v]) is
defined in the `.fsti` but cannot currently be tracked through Pulse loop
invariants due to Pulse VC generation limitations with nested `Seq.index`
on the weights array.

## Admits and Assumptions

### 1. `SZ.fits_u64` (Platform Assumption)

```fstar
let assume_fits_u64 () : Lemma (ensures SZ.fits_u64) = admit ()
```

**Classification**: Platform assumption (not a spec issue)

### 2. `drop_` for Returned Vecs (API Gap)

The `prim` function allocates and returns `(V.vec SZ.t & V.vec SZ.t)` but
its postcondition does **not** include `is_full_vec` for the returned vecs.
We use `drop_` to discard the vec permissions.

**Classification**: API gap in `prim`'s postcondition (missing `is_full_vec`)

## Remaining Spec Weakness

The postcondition now constrains parent values to valid vertices but still
does not capture the MST structural properties (spanning, acyclic, minimum
weight). Specifically:
- Cannot determine which vertices have finite keys (connected to MST)
- Cannot verify specific key values or parent relationships
- The `key_parent_consistent` property would link key values to edge weights
  but is not yet provable through Pulse loops

## Conclusion

**Satisfiability**: ✓ proven (with platform assumption `SZ.fits_u64`)
**Parent validity**: ✓ proven (all parent[v] < n)
**Completeness**: ✗ postcondition still too weak for MST verification
**Additional API gap**: Missing `is_full_vec` for returned vecs
