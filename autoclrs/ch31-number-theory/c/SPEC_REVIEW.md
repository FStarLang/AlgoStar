# Spec Review: ch31 C Code vs Impl.fsti

## Overview

This document compares the specifications proven in the C code (via c2pulse)
against the full specifications in the `CLRS.Ch31.*.Impl.fsti` files.

Per task requirements:
- **Complexity-related specs are being removed** from the C code entirely.
- The focus is on ensuring all **functional correctness** properties from
  the Impl.fsti files are proven in the C code.

---

## 1. GCD (`gcd.c` vs `CLRS.Ch31.GCD.Impl.fsti`)

### Impl.fsti functional correctness properties:
- `SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init)`
- `SZ.v result > 0`
- `divides (SZ.v result) (SZ.v a_init)`
- `divides (SZ.v result) (SZ.v b_init)`

### Current C code proves:
- ✅ `result = gcd_spec(a, b)`
- ✅ `result > 0`
- ✅ `divides result a`
- ✅ `divides result b`
- ❌ Complexity bound (gcd_steps...) — **to be removed**

### Action items:
- [x] Remove complexity bound from ensures
- [x] Remove `open CLRS.Ch31.GCD.Complexity`
- [x] Remove `lemma_gcd_steps_log` ghost call

### Status: **COMPLETE** — all functional correctness properties match after cleanup.

---

## 2. Extended GCD (`extended_gcd.c` vs `CLRS.Ch31.ExtendedGCD.Impl.fsti`)

### Impl.fsti functional correctness properties:
- `SZ.v result == d` where `(|d, x, y|) = extended_gcd a b`
- `SZ.v result > 0`
- `a * x + b * y == result` (Bézout identity)
- `divides result a`
- `divides result b`

### Current C code proves:
- ✅ `result = egcd_d(a, b)` (same as d from extended_gcd tuple)
- ✅ `result > 0`
- ✅ Bézout identity via egcd_x/egcd_y helpers
- ✅ `divides result a`
- ✅ `divides result b`
- ❌ Complexity bound (gcd_steps...) — **to be removed**

### Action items:
- [x] Remove complexity bound from ensures
- [x] Remove `open CLRS.Ch31.GCD.Complexity`
- [x] Remove `lemma_gcd_steps_log` ghost call

### Status: **COMPLETE** — all functional correctness properties match after cleanup.

---

## 3. ModExp Right-to-Left (`mod_exp.c` vs `CLRS.Ch31.ModExp.Impl.fsti`)

### Impl.fsti functional correctness properties:
- `mod_exp_spec b e m == result`
- `result >= 0`
- `result < m`

### Current C code proves:
- ✅ `mod_exp_spec(b, e, m) = result`
- ✅ `result >= 0`
- ✅ `result < m`
- ❌ Complexity: `steps` variable, `log2f` invariants — **to be removed**

### Action items:
- [x] Remove `steps` variable and all invariant clauses mentioning it
- [x] Remove `lemma_log2f_lt` from `_include_pulse`
- [x] Remove `open CLRS.Ch31.ModExp.Complexity`
- [x] Remove `lemma_log2f_halve_le` and `lemma_log2f_lt` ghost calls

### Status: **COMPLETE** — all functional correctness properties match after cleanup.

---

## 4. ModExp Left-to-Right (`mod_exp_lr.c` vs `CLRS.Ch31.ModExpLR.Impl.fsti`)

### Impl.fsti functional correctness properties:
- `mod_exp_spec b e m == result`
- `result >= 0`
- `result < m`

### Current C code proves:
- ✅ `mod_exp_spec(b, e, m) = result`
- ✅ `result >= 0`
- ✅ `result < m`
- ❌ Complexity: `steps` variable, `num_bits` invariants — **to be removed**

### Action items:
- [x] Remove `steps` variable and all invariant clauses mentioning it/num_bits
- [x] Remove `mask_loop_done` and `lemma_num_bits_le` from `_include_pulse`
- [x] Remove `open CLRS.Ch31.ModExpLR.Complexity`
- [x] Remove `mask_loop_done` and `lemma_num_bits_le` ghost calls
- [x] Keep `k` variable — needed for `mask == pow2(k)` invariant (functional correctness)
- [x] Keep `lemma_k_le_pow2`, `pow2_half`, `pow2_even`, `lemma_bit_decompose_div` — functional correctness

### Status: **COMPLETE** — all functional correctness properties match after cleanup.

---

## Summary

All four algorithms already prove the correct functional correctness properties
matching their Impl.fsti interfaces. The only gap was complexity instrumentation
(`steps` counters, `gcd_steps`, `log2f`, `num_bits` bounds) which has been removed.

No `_include_pulse` blocks contain computationally relevant code — they contain
only spec-level pure functions, lemmas, and ghost helpers, which is correct.
