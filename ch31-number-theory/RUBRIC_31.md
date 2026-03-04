# Chapter 31: Number-Theoretic Algorithms — Rubric Compliance

> Generated from `RUBRIC.md` (canonical rubric), `AUDIT_CH31.md`, and inspection
> of the four `.fst` files in `ch31-number-theory/`.

---

## 1  Current File Inventory

| # | File | Lines | Language | Content (monolithic) | Verified | Admits |
|---|------|------:|----------|----------------------|----------|--------|
| 1 | `CLRS.Ch31.GCD.fst` | 235 | Pulse | Spec + Lemmas + Complexity + Impl | ✅ | 0 |
| 2 | `CLRS.Ch31.ExtendedGCD.fst` | 188 | Pure F\* | Spec + Lemmas + Complexity (reuses `GCD.gcd_steps`) + Examples | ✅ | 0 |
| 3 | `CLRS.Ch31.ModExp.fst` | 224 | Pulse | Spec + Lemmas + Complexity + Impl (right-to-left, Ex 31.6-2) | ✅ | 0 |
| 4 | `CLRS.Ch31.ModExpLR.fst` | 144 | Pulse | Impl (left-to-right, primary CLRS p. 957); imports `ModExp` spec | ✅ | 0 |

**Total:** 791 lines, 0 admits, 0 assumes across all files.

---

## 2  Algorithms Covered

| Algorithm | CLRS Reference | Primary File | Variant |
|-----------|---------------|--------------|---------|
| EUCLID (GCD) | p. 935, Alg 31.2 | `CLRS.Ch31.GCD.fst` | Iterative (tail-call transform) |
| EXTENDED-EUCLID | p. 937, Alg 31.3 | `CLRS.Ch31.ExtendedGCD.fst` | Recursive (verbatim CLRS) |
| MODULAR-EXPONENTIATION (R→L) | Exercise 31.6-2 | `CLRS.Ch31.ModExp.fst` | Right-to-left (LSB→MSB) |
| MODULAR-EXPONENTIATION (L→R) | p. 957, Alg 31.6 | `CLRS.Ch31.ModExpLR.fst` | Left-to-right (MSB→LSB, primary) |

---

## 3  Rubric Compliance Matrix

The canonical rubric (`RUBRIC.md`) requires **seven files per algorithm**:

| | Spec.fst | Lemmas.fst | Lemmas.fsti | Complexity.fst | Complexity.fsti | Impl.fst | Impl.fsti |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **GCD** | ❌ inline | ❌ inline | ❌ missing | ❌ inline | ❌ missing | ❌ inline | ❌ missing |
| **ExtendedGCD** | ❌ inline | ❌ inline | ❌ missing | 🔶 inline¹ | ❌ missing | N/A² | N/A² |
| **ModExp (R→L)** | ❌ inline | ❌ inline | ❌ missing | ❌ inline | ❌ missing | ❌ inline | ❌ missing |
| **ModExpLR** | 🔶 imports³ | ❌ inline | ❌ missing | ❌ inline | ❌ missing | ❌ inline | ❌ missing |

Legend:
- ✅ = rubric-compliant separate file exists
- 🔶 = partially addressed (content present but not in a separate file)
- ❌ = missing / monolithically inlined

¹ ExtendedGCD reuses `gcd_steps`/`num_bits`/`lemma_gcd_steps_log` from `GCD.fst`, with a thin wrapper `extended_gcd_complexity`.
² ExtendedGCD is pure F\*, so a Pulse Impl is not required. The pure function *is* the implementation.
³ ModExpLR imports `mod_exp_spec` and `pow` from `ModExp`, so it shares the spec rather than duplicating it.

### Summary Counts

| Criterion | Required | Present | Gap |
|-----------|:--------:|:-------:|:---:|
| Separate `Spec.fst` files | 3–4 | 0 | 3–4 |
| Separate `Lemmas.fst` files | 3–4 | 0 | 3–4 |
| `Lemmas.fsti` interfaces | 3–4 | 0 | 3–4 |
| Separate `Complexity.fst` files | 3–4 | 0 | 3–4 |
| `Complexity.fsti` interfaces | 3–4 | 0 | 3–4 |
| Separate `Impl.fst` files | 3 | 0 | 3 |
| `Impl.fsti` interfaces | 3 | 0 | 3 |

**Chapter 31 is the least rubric-compliant chapter: every file is monolithic
with zero structural separation.**

---

## 4  Detailed Action Items

### 4.1  Structural Refactor (High Priority)

Each monolithic file needs to be split per the rubric. Below is the target
file layout.

#### GCD

| Target File | Contents to Extract |
|-------------|-------------------|
| `CLRS.Ch31.GCD.Spec.fst` | `gcd_spec`, `gcd_spec_comm` |
| `CLRS.Ch31.GCD.Lemmas.fst` | `gcd_spec_divides`, `gcd_spec_comm` (if not in Spec) |
| `CLRS.Ch31.GCD.Lemmas.fsti` | Signatures: `gcd_spec_divides`, `gcd_spec_comm` |
| `CLRS.Ch31.GCD.Complexity.fst` | `gcd_steps`, `num_bits`, `lemma_*` helpers, `lemma_gcd_steps_log`, `gcd_steps_log_min`, `gcd_complexity_bounded` |
| `CLRS.Ch31.GCD.Complexity.fsti` | Signatures for the above |
| `CLRS.Ch31.GCD.Impl.fst` | `gcd_impl`, ghost tick infrastructure |
| `CLRS.Ch31.GCD.Impl.fsti` | Signature of `gcd_impl` |

#### ExtendedGCD

| Target File | Contents to Extract |
|-------------|-------------------|
| `CLRS.Ch31.ExtendedGCD.Spec.fst` | `extended_gcd_result`, `extended_gcd` |
| `CLRS.Ch31.ExtendedGCD.Lemmas.fst` | `extended_gcd_computes_gcd`, `extended_gcd_divides_both`, `bezout_identity`, `extended_gcd_is_greatest`, `extended_gcd_correctness`, tests |
| `CLRS.Ch31.ExtendedGCD.Lemmas.fsti` | Signatures for the above |
| `CLRS.Ch31.ExtendedGCD.Complexity.fst` | `extended_gcd_complexity_bounded`, `extended_gcd_complexity` |
| `CLRS.Ch31.ExtendedGCD.Complexity.fsti` | Signature for the above |

No `Impl.fst`/`.fsti` needed — the algorithm is pure-functional.

#### ModExp (right-to-left)

| Target File | Contents to Extract |
|-------------|-------------------|
| `CLRS.Ch31.ModExp.Spec.fst` | `pow`, `mod_exp_spec` |
| `CLRS.Ch31.ModExp.Lemmas.fst` | `pow_add`, `pow_pow`, `pow_square`, `pow_even`, `pow_odd`, `pow_mod_base`, `mod_exp_step*` |
| `CLRS.Ch31.ModExp.Lemmas.fsti` | Signatures for the above |
| `CLRS.Ch31.ModExp.Complexity.fst` | `log2f`, `lemma_log2f_*`, `modexp_complexity_bounded` |
| `CLRS.Ch31.ModExp.Complexity.fsti` | Signatures for the above |
| `CLRS.Ch31.ModExp.Impl.fst` | `mod_exp_impl` + ghost tick |
| `CLRS.Ch31.ModExp.Impl.fsti` | Signature of `mod_exp_impl` |

#### ModExpLR (left-to-right)

| Target File | Contents to Extract |
|-------------|-------------------|
| `CLRS.Ch31.ModExpLR.Lemmas.fst` | `lemma_div_pow2_succ`, `lemma_bit_decompose`, `lemma_prefix_zero`, `lemma_mod_mul_both`, `mod_exp_lr_step` |
| `CLRS.Ch31.ModExpLR.Lemmas.fsti` | Signatures for the above |
| `CLRS.Ch31.ModExpLR.Complexity.fst` | `modexp_lr_complexity_bounded` |
| `CLRS.Ch31.ModExpLR.Complexity.fsti` | Signature for the above |
| `CLRS.Ch31.ModExpLR.Impl.fst` | `mod_exp_lr_impl` |
| `CLRS.Ch31.ModExpLR.Impl.fsti` | Signature of `mod_exp_lr_impl` |

ModExpLR shares `Spec.fst` with `ModExp` — no separate spec needed.

### 4.2  Content Gaps (from Audit)

| # | Item | Effort | Files |
|---|------|--------|-------|
| 1 | Factor ghost-tick (`incr_nat`, `tick`) into a shared module (duplicated in GCD + ModExp) | Small | New `common/GhostTick.fst` |
| 2 | Add concrete test cases for GCD and ModExp (ExtendedGCD already has them) | Trivial | GCD Lemmas, ModExp Lemmas |
| 3 | Prove `O(log min(a,b))` as a standalone lemma (currently derivable but not stated) | Trivial | GCD Complexity |

### 4.3  Documentation Corrections (from Audit)

All documentation issues from the audit have already been addressed in the
current file headers:
- ModExp header now notes the right-to-left variant.
- GCD header uses "direct mod-halving argument" instead of "Lamé's theorem".
- ExtendedGCD header now references `gcd_steps` from `CLRS.Ch31.GCD`.

---

## 5  Quality Checks

| Check | Status | Notes |
|-------|--------|-------|
| Zero admits | ✅ | All 4 files fully verified |
| Zero assumes | ✅ | Confirmed by audit |
| CLRS fidelity | ✅ | GCD/ExtGCD verbatim; ModExp = Ex 31.6-2; ModExpLR = primary CLRS |
| Functional correctness specs | ✅ | All algorithms: `result == spec(...)` |
| Bézout's identity | ✅ | ExtendedGCD only |
| Divisibility properties | ✅ | GCD (`gcd_spec_divides`) + ExtendedGCD |
| Greatest-divisor property | ✅ | ExtendedGCD (`extended_gcd_is_greatest`) |
| Complexity: GCD | ✅ | `O(log b)` via mod-halving + `O(log min(a,b))` stated |
| Complexity: ExtendedGCD | ✅ | Reuses GCD's `gcd_steps`/`lemma_gcd_steps_log` |
| Complexity: ModExp (R→L) | ✅ | `⌊log₂ e⌋ + 1` iterations |
| Complexity: ModExpLR | ✅ | `num_bits(e)` iterations |
| Solver limits reasonable | ✅ | Max `z3rlimit 150` in one proof; all others ≤ 30 |
| No code duplication | 🔶 | `gcd` alias in ExtendedGCD (now just `let gcd = gcd_spec`); ghost tick duplicated in GCD + ModExp |
| Separate Spec files | ❌ | 0 of 3–4 required |
| Separate Lemma files + `.fsti` | ❌ | 0 of 3–4 required |
| Separate Complexity files + `.fsti` | ❌ | 0 of 3–4 required |
| Separate Impl files + `.fsti` | ❌ | 0 of 3 required |

### Overall Rubric Score

| Dimension | Score |
|-----------|-------|
| **Correctness & Verification** | 10 / 10 |
| **Specification Strength** | 9 / 10 |
| **Complexity Analysis** | 9 / 10 |
| **File Structure (rubric compliance)** | 1 / 10 |
| **Documentation** | 9 / 10 |

**Chapter 31 is one of the strongest chapters in proof quality and one of the
weakest in structural rubric compliance.** The primary remediation is a
mechanical refactor: splitting each monolithic file into the 5–7 file layout
prescribed by `RUBRIC.md`.
