# Ch33 C Code Specification Review

## Overview

Comparison of specifications proven in `ch33/*.Impl.fsti` versus what is
currently proven in `ch33/c/*.c` files. The C code uses Int32.t instead of
unbounded int, requiring bridge lemmas for representation changes.

## Issue 1: Computationally relevant code in `_include_pulse`

**Status: ✅ No issues.** All three C files only have `open` statements in
their `_include_pulse` blocks (opens for spec modules, bridge lemma modules,
and `FStar.Mul`). No implementation code is in these blocks.

## Issue 2: Complexity-related instrumentation

**Status: ✅ No issues.** None of the C files contain complexity tracking or
instrumentation.

## Issue 3: Specification gaps — Final Status

### Representation Bridge Approach

The `_c` wrapper functions in the bridge modules are defined directly on
`Seq.seq (option Int32.t)` using `ival` (element accessor matching c2pulse's
`array_read` pattern) rather than going through `to_int_seq`/`Seq.init`.
This allows Z3 to directly match C loop body computations against spec
function unfoldings.

### Segments (`segments.c`)

All four functions fully connected to spec. **✅ No changes needed.**

### Graham Scan (`graham_scan.c`)

| Function | Spec Connection | Status |
|----------|----------------|--------|
| `find_bottom` | `find_bottom_spec_c` postcondition + `find_bottom_aux_c` loop invariant | ✅ Verified |
| `polar_cmp` | `polar_cmp_spec_c` postcondition | ✅ Verified |
| `pop_while` | `pop_while_spec_c` + `ensures_left_turn_c` postconditions | ✅ Verified |
| `graham_scan_step` | Operational postconditions only (hull write, prefix preservation) | ⚠️ `scan_step_sz_spec_c` not connected — requires proving `pop_while` result chains through `scan_step_sz_spec`, too deep for Z3 |

### Jarvis March (`jarvis_march.c`)

| Function | Spec Connection | Status |
|----------|----------------|--------|
| `find_leftmost` | `find_leftmost_spec_c` postcondition + `find_leftmost_aux_c` loop invariant | ✅ Verified |
| `find_next` | Operational postconditions (`return < len ∧ return ≠ current`) | ⚠️ `find_next_spec_c` not connected — `find_next_aux_c` has 4-way branching (j=current, next=current, cp<0, else) causing Z3 timeout |
| `jarvis_march` | Operational bounds only (`1 ≤ return ≤ len`) | ⚠️ Depends on `find_next_spec_c` postcondition |
| `jarvis_march_with_hull` | Operational bounds only | ⚠️ Same dependency |

### Summary

- **6 of 12 functions** now have full spec-level connections (up from 4)
- **Bridge modules** provide `_c` wrappers and unfolding lemmas, ready for future use
- **Key limitation**: `find_next_aux_c` loop invariant causes Z3 timeout due to
  complex branching. All Jarvis march outer loop specs depend on this.
- **No admits, no assumes** — all verification is complete
