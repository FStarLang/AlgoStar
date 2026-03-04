# Chapter 32: String Matching — Rubric Compliance

**Rubric source**: `RUBRIC.md` (repo root)
**Audit source**: `AUDIT_CH32.md` (repo root)
**Date**: 2025-07-18

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch32.NaiveStringMatch.fst` | 240 | Impl + Spec + Complexity (all-in-one) | Naive |
| 2 | `CLRS.Ch32.RabinKarp.Spec.fst` | 368 | Spec | Rabin-Karp |
| 3 | `CLRS.Ch32.RabinKarp.fst` | 326 | Impl | Rabin-Karp |
| 4 | `CLRS.Ch32.RabinKarp.Complexity.fst` | 113 | Complexity | Rabin-Karp |
| 5 | `CLRS.Ch32.KMP.PureDefs.fst` | 112 | **Spec** (≈ `Spec.fst`) | KMP |
| 6 | `CLRS.Ch32.KMP.Spec.fst` | 623 | Lemmas (completeness proof) | KMP |
| 7 | `CLRS.Ch32.KMP.Bridge.fst` | 383 | **Lemmas** (≈ `Lemmas.fst`) | KMP |
| 8 | `CLRS.Ch32.KMP.fst` | 486 | Impl + Complexity (inline) | KMP |
| 9 | `CLRS.Ch32.KMP.Test.fst` | 77 | Test harness | KMP |

Ancillary (in `reference/` subdirectory): `reference.fst`, `test_without_lemma.fst` — not part of the verified library.

**Admits / Assumes**: Zero in all 9 production files (confirmed by grep).

---

## Algorithms Covered

### 1. Naive String Matching (CLRS §32.1)

Single file `NaiveStringMatch.fst` contains the pure spec (`matches_at`, `count_matches_up_to`), the Pulse implementation, and the complexity proof — all inline.

- **Correctness**: `count == count_matches_up_to` — finds ALL matches. ✅
- **Complexity**: O((n−m+1)·m) via ghost tick counter. ✅
- **CLRS fidelity**: Fully faithful (0-indexed adaptation). ✅

### 2. Rabin-Karp (CLRS §32.2)

Three files following rubric separation:

| File | Content |
|------|---------|
| `RabinKarp.Spec.fst` | Polynomial hash (Horner's rule), rolling hash step, `matches_at_dec`, bidirectional correctness (`no_false_positives` + `no_false_negatives`). |
| `RabinKarp.fst` | Pulse implementation using the CLRS polynomial hash from `RKSpec`. Proves `count == count_matches_up_to`. |
| `RabinKarp.Complexity.fst` | Pure analysis: O(n+m) best case, O(nm) worst case. |

- **Correctness**: Full (Pulse impl + Spec both prove all matches). ✅
- **Complexity**: Proven in pure F*; no ghost ticks in Pulse impl. 🔶
- **CLRS fidelity**: Now uses CLRS polynomial hash (audit P1.1 is closed). ✅

### 3. KMP (CLRS §32.4)

Five files with non-standard naming:

| File | Rubric equivalent | Content |
|------|-------------------|---------|
| `KMP.PureDefs.fst` | **Spec** | Shared pure definitions: `is_prefix_suffix`, `extends_to`, `prefix_suffix_extend`, `failure_chain`. |
| `KMP.Spec.fst` | Lemmas (completeness) | Full completeness proof: `kmp_step_maximal`, `kmp_match_iff`, `kmp_count_step`, `count_before_eq_spec`. |
| `KMP.Bridge.fst` | **Lemmas** (bridging) | Connects Pulse `pi_correct` to `Spec.pi_max` via `pi_optimal_extension`. |
| `KMP.fst` | **Impl** | Pulse `compute_prefix_function` + `kmp_matcher` + `kmp_string_match`. |
| `KMP.Test.fst` | Test | Pulse test cases for prefix function and matcher. |

- **Correctness**: `count == count_matches_spec` (line 274 of KMP.fst). End-to-end via Bridge → Spec chain. ✅
- **Prefix maximality**: `pi_max_sz` proven (line 92 of KMP.fst, via Bridge). ✅
- **Complexity**: O(n+m) via amortized analysis with Φ = k/q. ✅
- **CLRS fidelity**: Fully faithful (0-indexed). ✅

---

## Rubric Compliance Matrix

The rubric requires 7 files per algorithm. Status key: ✅ = present & conforming, 🔶 = present but named/structured differently, ❌ = missing.

| Rubric File | Naive | Rabin-Karp | KMP |
|-------------|:-----:|:----------:|:---:|
| **Spec.fst** | 🔶 inline in `NaiveStringMatch.fst` | ✅ `RabinKarp.Spec.fst` | 🔶 `KMP.PureDefs.fst` |
| **Lemmas.fst** | 🔶 inline (correctness proved with impl) | 🔶 inline in `RabinKarp.Spec.fst` | 🔶 `KMP.Bridge.fst` + `KMP.Spec.fst` |
| **Lemmas.fsti** | ❌ missing | ❌ missing | ❌ missing |
| **Complexity.fst** | 🔶 inline in `NaiveStringMatch.fst` | ✅ `RabinKarp.Complexity.fst` | 🔶 inline in `KMP.fst` |
| **Complexity.fsti** | ❌ missing | ❌ missing | ❌ missing |
| **Impl.fst** | 🔶 `NaiveStringMatch.fst` (no `.Impl` suffix) | 🔶 `RabinKarp.fst` (no `.Impl` suffix) | 🔶 `KMP.fst` (no `.Impl` suffix) |
| **Impl.fsti** | ❌ missing | ❌ missing | ❌ missing |

**Summary**: 3/21 fully conforming, 12/21 present but non-conforming names/structure, 6/21 missing.

---

## Detailed Action Items

### High — Structural conformance

| ID | Action | Files affected | Notes |
|----|--------|----------------|-------|
| R1 | **Add `.fsti` interface files** for Lemmas, Complexity, and Impl for all three algorithms (6 files). | New files | The rubric requires `.fsti` files exposing public signatures. Currently zero `.fsti` files exist. |
| R2 | **Factor Naive into separate files**: extract spec (`NaiveStringMatch.Spec.fst`) and complexity proof from the monolithic `NaiveStringMatch.fst`. | Split 1 → 3+ files | Aligns Naive with the rubric's multi-file structure. |
| R3 | **Rename KMP files to rubric names**: `PureDefs` → `Spec`, `Bridge` → `Lemmas`. | `KMP.PureDefs.fst` → `KMP.Spec.fst`; current `KMP.Spec.fst` needs a new name (e.g., `KMP.Completeness.fst` or fold into `KMP.Lemmas.fst`). | Requires updating all `open`/`module` aliases across KMP files. |
| R4 | **Add `.Impl` suffix** to Pulse implementation files, or document the naming deviation. | `NaiveStringMatch.fst`, `RabinKarp.fst`, `KMP.fst` | Alternatively, amend the rubric to permit the current naming if it is the project convention. |
| R5 | **Extract KMP complexity** into a separate `KMP.Complexity.fst` (and `.fsti`). | New file; slim `KMP.fst` | Amortized analysis is currently woven into the Pulse loop invariants, so full extraction may not be practical — inline may be acceptable with a note. |

### Medium — Content gaps

| ID | Action | Notes |
|----|--------|-------|
| R6 | **Add ghost tick counter to `RabinKarp.fst`** and prove O(nm) worst-case inline. | Currently complexity is pure-only (`RabinKarp.Complexity.fst`); the Pulse impl has no runtime bound in its postcondition. |
| R7 | **Factor Rabin-Karp correctness lemmas** out of `RabinKarp.Spec.fst` into a dedicated `RabinKarp.Lemmas.fst`. | `Spec.fst` currently contains both definitions and proofs (bidirectional correctness, rolling hash correctness). |

### Low — Cleanup

| ID | Action | Notes |
|----|--------|-------|
| R8 | **Update `README.md`** to list all 9 files and describe the rubric mapping. | README is outdated (still lists only 3 files per the audit). |
| R9 | **Decide fate of `reference/`** subdirectory. | Contains `reference.fst` and `test_without_lemma.fst` — useful as reference material but not part of the verified library. Document or remove. |

---

## Quality Checks

| Check | Naive | Rabin-Karp | KMP |
|-------|:-----:|:----------:|:---:|
| Zero admits / assumes | ✅ | ✅ | ✅ |
| Functional correctness (count == spec) | ✅ | ✅ | ✅ |
| Complexity proven | ✅ O((n−m+1)m) | 🔶 Pure only | ✅ O(n+m) |
| CLRS-faithful algorithm | ✅ | ✅ | ✅ |
| Spec/Impl separation | 🔶 monolithic | ✅ | ✅ (non-standard names) |
| Interface (`.fsti`) files | ❌ | ❌ | ❌ |
| Tests | ❌ | ❌ | ✅ `KMP.Test.fst` |

### Changes since AUDIT_CH32.md

The audit (dated 2025-02-26) identified several critical gaps. Current status:

| Audit ID | Issue | Status |
|----------|-------|--------|
| P0.1 | KMP matcher postcondition — count == spec | ✅ **Closed** — `KMP.fst` line 274 now proves `count == count_matches_spec`. |
| P0.2 | Prove `pi_max` in Pulse | ✅ **Closed** — `KMP.Bridge.fst` bridges `pi_correct` → `pi_max_sz` → `Spec.pi_max`. KMP.fst line 92 proves `pi_max_sz`. |
| P0.3 | KMP.Spec module coherence | ✅ **Closed** — `KMP.PureDefs.fst` factored out shared definitions; `KMP.Spec.fst` imports it cleanly. |
| P1.1 | Unify Rabin-Karp hash | ✅ **Closed** — `RabinKarp.fst` now uses CLRS polynomial hash from `RKSpec`. |
| P1.2 | Fix KMP.StrengthenedSpec | ✅ **Closed** — file removed from directory. |
| P2.3 | Delete backup files | ✅ **Closed** — no backup files in directory. |
| P2.1 | Extract shared spec module | 🔶 Partial — `KMP.PureDefs.fst` shares KMP definitions; Naive/RK still have independent `matches_at`/`count_matches_up_to`. |
| P2.4 | Add complexity to RabinKarp Pulse | ❌ Open — no ghost ticks in `RabinKarp.fst`. |
| P3.1 | Update README.md | ❌ Open. |
