# Chapter 02: Getting Started — Rubric Compliance

**Date:** 2025-07-17
**Source files:** `ch02-getting-started/`
**Rubric:** `RUBRIC.md` (canonical naming: `CLRS.ChXX.AlgoName.{Spec,Lemmas,Complexity,Impl}.{fst,fsti}`)

---

## Current File Inventory

| File | Role | Rubric Category | Pulse/F\* | Lines |
|------|------|-----------------|-----------|-------|
| `CLRS.Ch02.InsertionSort.fst` | Monolithic: spec defs + lemmas + complexity + Pulse impl | Mixed (should be split into Spec, Lemmas, Complexity, Impl) | Pulse | 227 |
| `CLRS.Ch02.MergeSort.fst` | Monolithic: pure merge spec + lemmas + helpers + Pulse merge/sort impl + complexity bridging | Mixed (should be split into Spec, Lemmas, Impl) | Pulse | 640 |
| `CLRS.Ch02.MergeSort.Complexity.fst` | Pure recurrence + O(n log n) bound + monotonicity/split | Complexity ✅ | Pure F\* | 268 |

---

## Algorithms Covered

| # | Algorithm | CLRS Section | CLRS Name | Current Module |
|---|-----------|-------------|-----------|----------------|
| 1 | Insertion Sort | §2.1, p. 18 | INSERTION-SORT | `CLRS.Ch02.InsertionSort` |
| 2 | Merge | §2.3.1, p. 31 | MERGE | `CLRS.Ch02.MergeSort` (fn `merge`) |
| 3 | Merge Sort | §2.3.1, p. 34 | MERGE-SORT | `CLRS.Ch02.MergeSort` (fn `merge_sort`, `merge_sort_aux`) |

Note: Merge and Merge Sort share a single module (`CLRS.Ch02.MergeSort`). Per the rubric they could stay together as "MergeSort" since merge is an integral sub-procedure of merge sort, not a standalone CLRS algorithm. The rubric compliance matrix below treats them as one algorithm unit: **MergeSort**.

---

## Rubric Compliance Matrix

### Insertion Sort (`CLRS.Ch02.InsertionSort`)

| Rubric File | Status | Current Location | Notes |
|-------------|--------|------------------|-------|
| `Spec.fst` | ❌ Missing | `complexity_bounded` (L86-88), `incr_nat` (L31) in `InsertionSort.fst` | No pure spec function exists; the "spec" is implicit in the postcondition |
| `Lemmas.fst` | ❌ Missing | `lemma_prefix_le_key` (L43-60), `lemma_combine_sorted_regions` (L62-73), `lemma_triangle_step` (L78-81) in `InsertionSort.fst` | Three lemmas inlined in the monolithic file |
| `Lemmas.fsti` | ❌ Missing | — | No interface for lemmas |
| `Complexity.fst` | ❌ Missing | `complexity_bounded` (L86-88), `lemma_triangle_step` (L78-81), `tick` (L33-39) in `InsertionSort.fst` | Complexity defs/proofs are inlined |
| `Complexity.fsti` | ❌ Missing | — | No interface for complexity |
| `Impl.fst` | 🔶 Exists, needs refactor | `insertion_sort` (L91-226) in `InsertionSort.fst` | File has correct impl but also contains spec, lemmas, and complexity mixed in |
| `Impl.fsti` | ❌ Missing | — | No public interface exposing `insertion_sort` signature |

### Merge Sort (`CLRS.Ch02.MergeSort`)

| Rubric File | Status | Current Location | Notes |
|-------------|--------|------------------|-------|
| `Spec.fst` | ❌ Missing | `seq_merge` (L42-51), `all_ge` (L118-119) in `MergeSort.fst` | Pure merge spec exists but is inlined; no pure sort spec |
| `Lemmas.fst` | ❌ Missing | 14 lemmas inlined in `MergeSort.fst` (see detailed list below) | Large body of lemma work not separated |
| `Lemmas.fsti` | ❌ Missing | — | No interface for lemmas |
| `Complexity.fst` | ✅ Conformant | `CLRS.Ch02.MergeSort.Complexity.fst` (268 lines) | Correctly named, standalone, well-structured |
| `Complexity.fsti` | ❌ Missing | — | `merge_sort_ops`, `merge_sort_bound`, `merge_sort_is_n_log_n`, `merge_sort_ops_monotone`, `merge_sort_ops_split` all lack an interface |
| `Impl.fst` | 🔶 Exists, needs refactor | `merge` (L392-531), `merge_sort_aux` (L541-591), `merge_sort` (L600-639), `copy_range` (L298-336), bridging defs `ms_cost`/`ms_cost_split`/`merge_complexity_bounded`/`sort_complexity_bounded` (L355-366), duplicate `tick`/`incr_nat` (L344-352) in `MergeSort.fst` | Impl is correct but monolithic; also contains spec + all lemmas |
| `Impl.fsti` | ❌ Missing | — | No public interface exposing `merge_sort` or `merge` signatures |

---

## Detailed Action Items

### A. Insertion Sort

#### A1. [CREATE] `CLRS.Ch02.InsertionSort.Spec.fst`
Create a pure-F\* specification module containing:
- `complexity_bounded` (currently L86-88 of `InsertionSort.fst`): `let complexity_bounded (cf c0: nat) (n: nat) : prop = cf >= c0 /\ cf - c0 <= op_Multiply n (n - 1) / 2`
- `incr_nat` (currently L31): `let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)`

*Rationale:* These are pure definitions used by both the lemmas and the implementation. Separating them allows `Lemmas.fst` and `Impl.fst` to depend on a shared spec.

#### A2. [CREATE] `CLRS.Ch02.InsertionSort.Lemmas.fst`
Extract from `InsertionSort.fst`:
- `lemma_prefix_le_key` (L43-60)
- `lemma_combine_sorted_regions` (L62-73)
- `lemma_triangle_step` (L78-81)

These are pure F\* lemmas. They depend on `CLRS.Common.SortSpec` (`prefix_sorted`, `sorted`) and standard FStar modules.

#### A3. [CREATE] `CLRS.Ch02.InsertionSort.Lemmas.fsti`
Expose `val` declarations for:
```fstar
val lemma_prefix_le_key (s s_outer: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma (requires vi <= vj /\ vj < Seq.length s /\ Seq.length s == Seq.length s_outer /\
                    prefix_sorted s_outer vj /\ prefix_sorted s vi /\
                    (forall (k: nat). k < vi ==> Seq.index s k == Seq.index s_outer k) /\
                    (forall (k: nat). k + 1 == vi ==> Seq.index s_outer k <= key))
          (ensures forall (k: nat). k < vi ==> Seq.index s k <= key)

val lemma_combine_sorted_regions (s: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma (requires vi <= vj /\ vj < Seq.length s /\
                    prefix_sorted s vi /\ Seq.index s vi == key /\
                    (forall (k: nat). k < vi ==> Seq.index s k <= key) /\
                    (forall (k: nat). vi < k /\ k <= vj ==> Seq.index s k > key) /\
                    (forall (k1 k2: nat). vi < k1 /\ k1 <= k2 /\ k2 <= vj ==>
                      Seq.index s k1 <= Seq.index s k2))
          (ensures prefix_sorted s (vj + 1))

val lemma_triangle_step (vj: nat)
  : Lemma (requires vj >= 1)
          (ensures op_Multiply vj (vj - 1) / 2 + vj == op_Multiply (vj + 1) vj / 2)
```

#### A4. [CREATE] `CLRS.Ch02.InsertionSort.Complexity.fst`
Extract from `InsertionSort.fst`:
- `complexity_bounded` definition (L86-88) — or re-export from Spec
- `lemma_triangle_step` (L78-81) — complexity-specific arithmetic
- `tick` ghost function (L33-39) — shared complexity instrumentation

*Note:* `tick` and `incr_nat` are duplicated in `MergeSort.fst` (L344-352). This module should be the single source. Alternatively, move `tick`/`incr_nat` to `CLRS.Common.Complexity.fst` (which already exists but uses `R.ref nat` instead of `GR.ref nat`). The common module should be updated to use `GR.ref nat` and both chapters should import from there.

#### A5. [CREATE] `CLRS.Ch02.InsertionSort.Complexity.fsti`
Expose:
```fstar
val complexity_bounded (cf c0: nat) (n: nat) : prop
val lemma_triangle_step (vj: nat) : Lemma (requires vj >= 1) (ensures ...)
```

#### A6. [RENAME] `CLRS.Ch02.InsertionSort.fst` → `CLRS.Ch02.InsertionSort.Impl.fst`
After extracting spec, lemmas, and complexity definitions, the remaining file should contain only:
- `insertion_sort` function (L91-226)
- Module opens/imports updated to reference the new `.Spec`, `.Lemmas`, `.Complexity` modules

#### A7. [CREATE] `CLRS.Ch02.InsertionSort.Impl.fsti`
Expose the public signature:
```fstar
val insertion_sort (a: array int) (#s0: Ghost.erased (Seq.seq int)) (len: SZ.t)
                   (ctr: GR.ref nat) (#c0: erased nat)
  : stt unit
    (requires A.pts_to a s0 ** GR.pts_to ctr c0 **
              pure (SZ.v len == Seq.length s0 /\ Seq.length s0 <= A.length a /\ SZ.v len > 0))
    (ensures fun _ -> exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf **
              pure (Seq.length s == Seq.length s0 /\ sorted s /\ permutation s0 s /\
                    complexity_bounded cf (reveal c0) (SZ.v len)))
```

---

### B. Merge Sort

#### B1. [CREATE] `CLRS.Ch02.MergeSort.Spec.fst`
Extract from `MergeSort.fst`:
- `seq_merge` (L42-51) — pure merge specification
- `all_ge` (L118-119) — helper predicate used in lemmas and impl
- `ms_cost` (L355) — complexity cost function (bridges to `Complexity.fst`)
- `merge_complexity_bounded` (L362-363) — predicate for merge postcondition
- `sort_complexity_bounded` (L365-366) — predicate for sort postcondition

These are all pure definitions. `ms_cost` depends on `CLRS.Ch02.MergeSort.Complexity.merge_sort_ops`.

#### B2. [CREATE] `CLRS.Ch02.MergeSort.Lemmas.fst`
Extract from `MergeSort.fst` — all pure lemmas about `seq_merge`:
- `seq_merge_length` (L57-64) — with SMTPat
- `count_empty` (L72-75)
- `count_cons` (L77-80)
- `seq_merge_count` (L82-102)
- `seq_merge_permutation` (L104-108)
- `seq_merge_all_ge` (L121-128)
- `sorted_all_ge_head` (L130-133)
- `sorted_tail` (L135-138)
- `seq_merge_sorted` (L140-167)
- `seq_merge_head_right` (L178-183)
- `seq_merge_head_left` (L186-191)
- `seq_merge_take_left` (L194-202)
- `seq_merge_take_right` (L205-213)
- `slice_cons` (L216-221)
- `suffix_step_left` (L230-251)
- `suffix_step_right` (L253-274)
- `slice_full` (L277-280) — with SMTPat
- `suffix_gives_index` (L283-288)
- `ms_cost_split` (L357-359)

Total: 19 lemmas + helpers to extract.

#### B3. [CREATE] `CLRS.Ch02.MergeSort.Lemmas.fsti`
Expose `val` declarations for the key public lemmas (at minimum):
```fstar
val seq_merge_length (s1 s2: Seq.seq int)
  : Lemma (ensures Seq.length (seq_merge s1 s2) == Seq.length s1 + Seq.length s2)
          [SMTPat (Seq.length (seq_merge s1 s2))]

val seq_merge_permutation (s1 s2: Seq.seq int)
  : Lemma (ensures permutation (Seq.append s1 s2) (seq_merge s1 s2))

val seq_merge_sorted (s1 s2: Seq.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (seq_merge s1 s2))

val suffix_step_left (s1 s2: Seq.seq int) (i l1 j l2: nat) : Lemma (...)
val suffix_step_right (s1 s2: Seq.seq int) (i l1 j l2: nat) : Lemma (...)
val ms_cost_split (n: pos{n > 1}) : Lemma (ensures ...)
```

Internal helpers (`count_empty`, `count_cons`, `sorted_tail`, etc.) may remain private (no `val` in `.fsti`).

#### B4. [CREATE] `CLRS.Ch02.MergeSort.Complexity.fsti`
The existing `Complexity.fst` lacks an interface. Create one exposing:
```fstar
val log2_ceil (n: pos) : nat
val ceil_div2 (n: pos) : pos
val merge_sort_ops (n: pos) : nat
val merge_sort_bound (n: pos) : nat

val merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_ops n <= merge_sort_bound n)

val merge_sort_ops_monotone (m n: pos)
  : Lemma (requires m <= n) (ensures merge_sort_ops m <= merge_sort_ops n)

val merge_sort_ops_split (n: pos{n > 1})
  : Lemma (ensures merge_sort_ops (n / 2) + merge_sort_ops (n - n / 2) + n <= merge_sort_ops n)
```

Internal helpers (`ceil_div2_decreases`, `ceil_div2_lower`, `ceil_div2_upper`, `log2_ceil_recurrence`, `log2_ceil_bounded`, `log_linear_bound`, `arithmetic_step`, `merge_sort_n_log_n_bound`) should stay private.

#### B5. [RENAME] `CLRS.Ch02.MergeSort.fst` → `CLRS.Ch02.MergeSort.Impl.fst`
After extracting spec and lemmas, the remaining file should contain only:
- `copy_range` (L298-336) — Pulse helper
- `tick` / `incr_nat` (L344-352) — **remove**, import from shared module (see C1 below)
- `merge` (L392-531) — Pulse impl
- `merge_sort_aux` (L541-591) — Pulse impl
- `merge_sort` (L600-639) — Pulse entry point

Update imports to reference `MergeSort.Spec`, `MergeSort.Lemmas`, `MergeSort.Complexity`.

#### B6. [CREATE] `CLRS.Ch02.MergeSort.Impl.fsti`
Expose public signatures for:
```fstar
val merge (a: array int) (lo mid hi: SZ.t)
          (ctr: GR.ref nat) (#c0: erased nat)
          (#s1 #s2: Ghost.erased (Seq.seq int))
  : stt unit (requires ...) (ensures ...)

val merge_sort (a: A.array int) (len: SZ.t)
               (ctr: GR.ref nat) (#c0: erased nat)
               (#s0: erased (Seq.seq int))
  : stt unit (requires ...) (ensures ...)
```

`merge_sort_aux` should remain private (not in `.fsti`).

---

### C. Cross-Cutting Issues

#### C1. [REFACTOR] Deduplicate `tick` / `incr_nat`
`incr_nat` and `tick` appear identically in both `InsertionSort.fst` (L31, L33-39) and `MergeSort.fst` (L344, L346-352). Move to a shared location:
- **Option A (preferred):** Update `CLRS.Common.Complexity.fst` to use `GR.ref nat` (ghost-erased) instead of `R.ref nat` (runtime). Both chapters import from there.
- **Option B:** Create `CLRS.Ch02.Common.fst` with the shared ghost tick.

Current `CLRS.Common.Complexity.fst` uses `R.ref nat` (non-erased, has runtime cost). The ghost variant (`GR.ref nat`) used by InsertionSort and MergeSort is superior. The common module should be updated to match.

#### C2. [VERIFY] While loop decreases clauses
All four while loops have explicit `decreases` clauses — no action needed:

| File | Loop | Line | Decreases |
|------|------|------|-----------|
| `InsertionSort.fst` | outer `while` | L113 | `SZ.v len - SZ.v !j` ✅ |
| `InsertionSort.fst` | inner `while` | L148 | `SZ.v !i` ✅ |
| `MergeSort.fst` | `copy_range` | L312 | `SZ.v len - SZ.v !i` ✅ |
| `MergeSort.fst` | merge loop | L452 | `(l1 - !i) + (l2 - !j)` ✅ |

---

## Quality Checks

### Admits / Assumes Count

| File | `admit` | `assume` | `assume val` | `sorry` |
|------|---------|----------|--------------|---------|
| `CLRS.Ch02.InsertionSort.fst` | 0 | 0 | 0 | 0 |
| `CLRS.Ch02.MergeSort.fst` | 0 | 0 | 0 | 0 |
| `CLRS.Ch02.MergeSort.Complexity.fst` | 0 | 0 | 0 | 0 |
| **Total** | **0** | **0** | **0** | **0** |

### Max z3rlimit Used

| File | Line | Setting | Scope |
|------|------|---------|-------|
| `MergeSort.fst` | 372 | `--z3rlimit 100 --fuel 2 --ifuel 1` | `merge` function (highest in ch02) |
| `MergeSort.fst` | 539 | `--z3rlimit 60 --fuel 1 --ifuel 1` | `merge_sort_aux` |
| `MergeSort.fst` | 70 | `--z3rlimit 50 --fuel 3 --ifuel 2` | `seq_merge_count` / `seq_merge_permutation` (fuel 3 is elevated) |
| `MergeSort.fst` | 116 | `--z3rlimit 40 --fuel 2 --ifuel 1` | `seq_merge_sorted` and helpers |
| `MergeSort.fst` | 175 | `--z3rlimit 50 --fuel 2 --ifuel 1` | suffix lemmas |
| `MergeSort.fst` | 296 | `--z3rlimit 40 --fuel 0 --ifuel 0` | `copy_range` |
| `MergeSort.Complexity.fst` | 167 | `--z3rlimit 10 --fuel 1 --ifuel 0` | `merge_sort_n_log_n_bound` |
| `MergeSort.Complexity.fst` | 235 | `--z3rlimit 20 --fuel 1 --ifuel 0` | `merge_sort_ops_monotone`, `merge_sort_ops_split` |
| `InsertionSort.fst` | — | defaults only | No `#push-options` anywhere |

**Peak:** z3rlimit 100 (merge impl). No `--retry` or `--z3seed` flags.

### While Loops — Decreases Clauses

All 4 while loops have explicit `decreases` — **fully covered** (see table in C2 above).

### Postcondition Coverage

| Function | Sorted | Permutation | Length preserved | Complexity bound | Overall |
|----------|--------|-------------|------------------|------------------|---------|
| `insertion_sort` | ✅ `sorted s` | ✅ `permutation s0 s` | ✅ `Seq.length s == Seq.length s0` | ✅ `complexity_bounded cf c0 n` (≤ n(n-1)/2) | **Strong** |
| `merge` | ✅ `sorted s_out` | ✅ `permutation (append s1 s2) s_out` | ✅ (via `pts_to_range` length) | ✅ `merge_complexity_bounded cf c0 lo hi` (≤ hi-lo) | **Strong** |
| `merge_sort_aux` | ✅ `sorted s'` | ✅ `permutation s s'` | ✅ (via `pts_to_range` length) | ✅ `sort_complexity_bounded cf c0 lo hi` (≤ ms_cost(hi-lo)) | **Strong** |
| `merge_sort` | ✅ `sorted s` | ✅ `permutation s0 s` | ✅ `Seq.length s == Seq.length s0` | ✅ `sort_complexity_bounded cf c0 0 len` | **Strong** |
| `copy_range` | — | — | ✅ (output == input) | — | **N/A** (helper) |

### Summary of Missing Rubric Artifacts

| Missing Artifact | Priority | Blocking? |
|-----------------|----------|-----------|
| `InsertionSort.Spec.fst` | Medium | No — spec is small |
| `InsertionSort.Lemmas.fst` + `.fsti` | Medium | No |
| `InsertionSort.Complexity.fst` + `.fsti` | Medium | No |
| `InsertionSort.Impl.fst` (rename) | Medium | No |
| `InsertionSort.Impl.fsti` | High | Yes — no public API |
| `MergeSort.Spec.fst` | Medium | No |
| `MergeSort.Lemmas.fst` + `.fsti` | Medium | No — largest extraction (19 lemmas) |
| `MergeSort.Complexity.fsti` | High | Yes — no public API for complexity |
| `MergeSort.Impl.fst` (rename) | Medium | No |
| `MergeSort.Impl.fsti` | High | Yes — no public API |
| Deduplicate `tick`/`incr_nat` | Medium | No — functional duplication |

**Total new files to create:** 11 (5 for InsertionSort, 5 for MergeSort, 1 Complexity.fsti)
**Total files to rename/refactor:** 2 (`InsertionSort.fst` → `Impl.fst`, `MergeSort.fst` → `Impl.fst`)
