# Chapter 08: Linear-Time Sorting — Rubric Compliance

**Updated:** 2026-03-16
**Source files:** 19 `.fst`/`.fsti` files — all verified ✅
**Canonical rubric:** `RUBRIC.md` (root)

---

## Current File Inventory

| # | File | Lang | Status |
|---|------|------|--------|
| 1 | `CLRS.Ch08.CountingSort.Spec.fst` | F* | ✅ Core spec: sorted, sorted_prefix, permutation (opaque), in_range |
| 2 | `CLRS.Ch08.CountingSort.Lemmas.fst` | F* | ✅ Proof helpers + lemma proofs; imports Spec |
| 3 | `CLRS.Ch08.CountingSort.Lemmas.fsti` | F* | ✅ Interface: `let` defs + `val` lemma sigs |
| 4 | `CLRS.Ch08.CountingSort.StableLemmas.fst` | F* | ✅ Phase-specific lemmas for CLRS stable variant |
| 5 | `CLRS.Ch08.CountingSort.DigitSortLemmas.fst` | F* | ✅ Digit-keyed counting sort lemmas (all phases verified) |
| 6 | `CLRS.Ch08.CountingSort.Impl.fst` | Pulse | ✅ CLRS-faithful 4-phase stable + in-place + digit-keyed variant |
| 7 | `CLRS.Ch08.CountingSort.Impl.fsti` | Pulse | ✅ Interface: counting_sort_impl, counting_sort_inplace, counting_sort_by_digit |
| 8 | `CLRS.Ch08.RadixSort.Spec.fst` | F* | ✅ Abstract multi-digit correctness |
| 9 | `CLRS.Ch08.RadixSort.Lemmas.fsti` | F* | ✅ Interface: key lemma signatures (new) |
| 10 | `CLRS.Ch08.RadixSort.Lemmas.fst` | F* | ✅ Aggregates Stability + FullSort |
| 11 | `CLRS.Ch08.RadixSort.Base.fst` | F* | ✅ Shared definitions |
| 12 | `CLRS.Ch08.RadixSort.Stability.fst` | F* | ✅ Core CLRS Lemma 8.3 stability proof + pack_is_stable |
| 13 | `CLRS.Ch08.RadixSort.FullSort.fst` | F* | ✅ Digit decomposition → numeric bridge |
| 14 | `CLRS.Ch08.RadixSort.Bridge.fst` | F* | ✅ CountingSort ↔ RadixSort.Base equivalences (both directions) |
| 15 | `CLRS.Ch08.RadixSort.MultiDigit.fst` | F* | ✅ Pure multi-digit radix sort spec |
| 16 | `CLRS.Ch08.RadixSort.fst` | Pulse | ✅ **Multi-digit radix sort** + single-digit variant |
| 17 | `CLRS.Ch08.BucketSort.Spec.fst` | F* | ✅ Actual definitions: sorted, insert, bucket fns |
| 18 | `CLRS.Ch08.BucketSort.Lemmas.fsti` | F* | ✅ Interface: correctness lemma sigs + bucket_sort (new) |
| 19 | `CLRS.Ch08.BucketSort.Lemmas.fst` | F* | ✅ Actual proofs + bucket_sort main fn |

---

## Rubric Compliance Matrix

### CountingSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `CountingSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `CountingSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `CountingSort.Lemmas.fsti` | ✅ |
| `Impl.fst` | `CountingSort.Impl.fst` | ✅ |
| `Impl.fsti` | `CountingSort.Impl.fsti` | ✅ |

**5/5 core slots filled**

Extra: `StableLemmas.fst`, `DigitSortLemmas.fst` — support modules.

### RadixSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `RadixSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `RadixSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `RadixSort.Lemmas.fsti` | ✅ |
| `Impl.fst` | `RadixSort.fst` | ✅ **Multi-digit** loop + single-digit variant |

**4/4 core slots filled** (Impl.fsti blocked by Pulse limitation)

Extra: `Base.fst`, `Bridge.fst`, `Stability.fst`, `FullSort.fst`, `MultiDigit.fst`.

### BucketSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `BucketSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `BucketSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `BucketSort.Lemmas.fsti` | ✅ |

**3/3 core slots filled** (no Pulse impl)

---

## Proof Integrity

| Check | Result |
|-------|--------|
| `admit()` calls | **0** across all verified files ✅ |
| `assume` calls | **0** across all verified files ✅ |
| `make -j4` | **✅** All 19 modules pass |
| DigitSortLemmas verified | ✅ All phase4 lemmas verified (~281s) |
| Impl.fst verified | ✅ All 3 Pulse fns: counting_sort_impl, inplace, by_digit |
| RadixSort.fst verified | ✅ Multi-digit: radix_sort + radix_sort_single_digit |
| Bridge.fst verified | ✅ Both directions: S↔B sorted/permutation |

---

## Dependency Structure

```
CountingSort.Spec ←── CountingSort.Lemmas ←── CountingSort.StableLemmas ←── CountingSort.Impl
                                                DigitSortLemmas ──────────┘   (stable + inplace + by_digit)

RadixSort.Base ←── RadixSort.Stability ←── RadixSort.FullSort
       │                    │
       │           RadixSort.Bridge ──→ CountingSort.Spec/Lemmas
       │
       ├── RadixSort.Spec
       └── RadixSort.MultiDigit

RadixSort.fst ──→ CountingSort.Impl.fsti (counting_sort_by_digit)
              ──→ RadixSort.Stability (lemma_stable_pass_preserves_ordering)
              ──→ RadixSort.FullSort (lemma_sorted_up_to_all_digits_implies_sorted)
              ──→ RadixSort.Bridge (base_sorted_implies_l_sorted, base_perm_implies_s_perm)

BucketSort.Spec ←── BucketSort.Lemmas
```

---

## Overall Score

| Dimension | Score |
|-----------|:-----:|
| Proof completeness | **10/10** Zero admits, zero assumes, all modules verified |
| CLRS fidelity | **10/10** CountingSort + **multi-digit RadixSort** in Pulse |
| Code quality | **9/10** No duplication, proper Spec/Lemmas/Impl split |
