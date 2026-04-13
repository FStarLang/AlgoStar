# Ch09 C Code Specification Review

Systematic comparison of C code specifications vs. `CLRS.Ch09.*.Impl.fsti` specs.

Complexity-related specifications are intentionally omitted from the C code,
as c2pulse does not support ghost counters. Full complexity proofs are in
the Pulse implementations (Impl.fst files).

## 1. MinMax (find_minimum, find_maximum)

### Impl.fsti Specs
- **Existential witness**: ∃k. k < len ∧ s[k] == result
- **Universal bound**: ∀k. k < len ⟹ result ≤ s[k] (min) / result ≥ s[k] (max)
- **Complexity**: `complexity_bounded_min` / `complexity_bounded_max` — omitted

### C Code Status: **COMPLETE** ✅
- All functional-correctness properties match Impl.fsti
- No `_include_pulse` with computationally relevant code
- No complexity instrumentation (intentional)

---

## 2. SimultaneousMinMax (find_minmax, find_minmax_pairs)

### Impl.fsti Specs
- **Min existential**: ∃k. s[k] == min_val
- **Min bound**: ∀k. min_val ≤ s[k]
- **Max existential**: ∃k. s[k] == max_val
- **Max bound**: ∀k. max_val ≥ s[k]
- **Complexity**: `complexity_bounded_minmax` / `complexity_bounded_minmax_pairs` — omitted

### C Code Status: **COMPLETE** ✅
- All functional-correctness properties match Impl.fsti
- Uses `_out` parameters instead of struct return (idiomatic C)
- No `_include_pulse` with computationally relevant code

---

## 3. PartialSelectionSort (find_min_index_from, pss_select)

### find_min_index_from

| Property | Impl.fsti | C Code | Status |
|----------|-----------|--------|--------|
| Range: start ≤ result < len | ✓ | ✓ | ✅ |
| is_min_in_range (universal bound) | ✓ | ✓ | ✅ |
| Complexity: cf − c0 == len − start − 1 | ✓ | omitted | Intentional |
| Array unchanged (bonus) | — | ✓ | Extra ✅ |
| Sorted prefix forwarding (bonus) | — | ✓ | Extra ✅ |

### pss_select

| Property | Impl.fsti | C Code | Status |
|----------|-----------|--------|--------|
| result == a[k−1] | ✓ | ✓ | ✅ |
| sorted_prefix (adj. pair form) | ✓ | ✓ | ✅ (bridge exists) |
| prefix_leq_suffix (boundary) | ✓ | ✓ | ✅ (bridge exists) |
| Forward no-fabrication | — | ✓ | ✅ |
| permutation s0 s_final | ✓ | ✗ | **GAP** (see below) |
| result == select_spec s0 (k−1) | ✓ | ✗ | **GAP** (see below) |
| Complexity | ✓ | omitted | Intentional |

### Gap Analysis

**permutation**: Requires tracking `Seq.Properties.permutation` through the loop.
The Pulse implementation does this via ghost sequences. At the C level, the
forward no-fabrication property (∀p. ∃m. a[p] == old(a[m])) is proven but
is strictly weaker than permutation (it does not ensure each original
value appears with the same multiplicity). Backward no-fabrication
(∀p. ∃m. old(a[p]) == a[m]) was attempted but Z3 cannot synthesize
existential witnesses through the swap chain within the rlimit. Even
combined, forward+backward no-fabrication does not imply permutation
for multisets. Ghost state would be required.

**select_spec**: Requires permutation as input to the bridge lemma
`select_correctness_bridge`. Without permutation, cannot be derived.

**Bridge lemmas exist** in `CLRS.Ch09.PartialSelectionSort.C.BridgeLemmas`:
- `swap_extract_permutation`: individual swap → permutation
- `c_sorted_prefix_implies_sorted_prefix`: adj-pair → sorted_prefix
- `c_sorted_boundary_implies_prefix_leq_suffix`: boundary → prefix_leq_suffix
- `select_correctness_bridge`: permutation + ordering → select_spec

These bridge lemmas are verified and available for a Pulse-level caller
to connect the C-level postconditions to the full Impl.fsti spec.

---

## 4. Quickselect (partition_in_range, quickselect_rec, quickselect)

### partition_in_range

| Property | Impl.fsti | C Code | Status |
|----------|-----------|--------|--------|
| pivot_pos ∈ [lo, hi) | ✓ | ✓ | ✅ |
| Partition ordering (left ≤ pivot) | ✓ | ✓ | ✅ |
| Partition ordering (right ≥ pivot) | ✓ | ✓ | ✅ |
| unchanged_outside | ✓ | ✓ | ✅ |
| Forward no-fabrication in [lo,hi) | — | ✓ | ✅ |
| Bounds tracking (lb, rb) | — | ✓ | Extra ✅ |
| permutation s0 s1 | ✓ | ✗ | **GAP** |
| Complexity | ✓ | omitted | Intentional |

### quickselect_rec

| Property | Impl.fsti | C Code | Status |
|----------|-----------|--------|--------|
| result == a[k] | ✓ | ✓ | ✅ |
| Full ordering (a[i<k] ≤ result) | ✓ | ✓ | ✅ |
| Full ordering (a[i>k] ≥ result) | ✓ | ✓ | ✅ |
| unchanged_outside [lo,hi) | ✓ | ✓ | ✅ |
| Forward no-fabrication in [lo,hi) | — | ✓ | ✅ (NEW) |
| Bounds tracking (lb, rb) | — | ✓ | Extra ✅ |

### quickselect (wrapper)

| Property | Impl.fsti | C Code | Status |
|----------|-----------|--------|--------|
| result == a[k] | ✓ | ✓ | ✅ |
| Full ordering (a[i<k] ≤ result) | ✓ | ✓ | ✅ |
| Full ordering (a[i>k] ≥ result) | ✓ | ✓ | ✅ |
| Forward no-fabrication | — | ✓ | ✅ (NEW) |
| permutation s0 s_final | ✓ | ✗ | **GAP** |
| result == select_spec s0 k | ✓ | ✗ | **GAP** |
| Complexity | ✓ | omitted | Intentional |

### Gap Analysis

Same as PartialSelectionSort: permutation and select_spec require ghost
state tracking that c2pulse does not support. Bridge lemmas exist in
`CLRS.Ch09.Quickselect.C.BridgeLemmas`:
- `swap_extract_permutation`: individual swap → QSpec.permutation
- `select_correctness_bridge_qs`: permutation + ordering → select_spec

---

## Summary

| Algorithm | Functional Correctness | Permutation | select_spec | Complexity |
|-----------|----------------------|-------------|-------------|------------|
| MinMax | ✅ Complete | N/A | N/A | Omitted |
| SimultaneousMinMax | ✅ Complete | N/A | N/A | Omitted |
| PartialSelectionSort | ✅ Ordering + no-fab | ✗ Needs ghost | ✗ Needs perm | Omitted |
| Quickselect | ✅ Ordering + no-fab | ✗ Needs ghost | ✗ Needs perm | Omitted |

**Improvements made in this review:**
- Added forward no-fabrication to `quickselect_rec` and `quickselect`
  (previously only `partition_in_range` had it)
- All C files verified clean with no admits or assumes

**Remaining gaps** (permutation, select_spec) are fundamental to the
c2pulse approach without ghost references. The full proofs exist in
the Pulse implementations (Impl.fst), and bridge lemmas connect
the C-level properties to the Pulse-level specs.
