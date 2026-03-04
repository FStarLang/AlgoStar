# Chapter 09: Order Statistics — Rubric Compliance

**Generated:** 2025-07-16
**Source files:** 12 `.fst` files, 3,463 total lines
**Canonical rubric:** `RUBRIC.md` — 7-file structure per algorithm
**Audit reference:** `AUDIT_CH09.md`

---

## 1. Current File Inventory

| # | File | Lines | Role |
|---|------|------:|------|
| 1 | `CLRS.Ch09.MinMax.fst` | 174 | Pulse impl — `find_minimum`, `find_maximum` with ghost-tick complexity |
| 2 | `CLRS.Ch09.SimultaneousMinMax.fst` | 441 | Pulse impl — `find_minmax` (simple), `find_minmax_pairs` (CLRS pair-processing), plus complexity variants |
| 3 | `CLRS.Ch09.PartialSelectionSort.fst` | 443 | Pulse impl — `select`, `find_min_index_from`, plus complexity variants |
| 4 | `CLRS.Ch09.PartialSelectionSort.Spec.fst` | 674 | Pure F* spec — `is_sorted`, `is_permutation`, `count_occ`, `count_lt`, `count_le`, `pure_sort`, `select_spec` |
| 5 | `CLRS.Ch09.PartialSelectionSort.SortedPerm.fst` | 89 | Pure F* lemma — `sorted_permutation_equal` (isolated for Z3 hygiene) |
| 6 | `CLRS.Ch09.PartialSelectionSort.Correctness.fst` | 252 | Pure F* lemmas — `partition_pivot_is_kth`, `pulse_correctness_hint`, `select_spec_has_partition_property` |
| 7 | `CLRS.Ch09.PartialSelectionSort.Complexity.fst` | 178 | Pure F* — `select_comparisons`, `select_bound`, `select_comparisons_exact` |
| 8 | `CLRS.Ch09.PartialSelectionSort.Complexity.Enhanced.fst` | 263 | Pure F* — `select_with_ticks`, `select_complexity_bound`, `quickselect_worst_case_cost` |
| 9 | `CLRS.Ch09.PartialSelectionSort.Complexity.Test.fst` | 124 | Pure F* — concrete instantiations (`test_minimum_complexity`, `test_median_complexity`, etc.) |
| 10 | `CLRS.Ch09.Quickselect.fst` | 541 | Pulse impl — `partition_in_range`, `quickselect`, plus complexity variants |
| 11 | `CLRS.Ch09.Quickselect.Complexity.fst` | 62 | Pure F* — `qs_cost`, `qs_bound`, `qs_quadratic`, `qs_cost_monotone` |
| 12 | `CLRS.Ch09.Quickselect.Helpers.fst` | 222 | Pure F* — `seq_perm_implies_is_perm`, `perm_unchanged_lower_bound_forall`, `count_range_eq` |

---

## 2. Algorithms Covered

### 2.1 MinMax (CLRS §9.1 — MINIMUM / MAXIMUM)

| Function | Type | Description |
|----------|------|-------------|
| `find_minimum` | Pulse `fn` | Linear scan, returns min; proves result exists in array & is universal minimum |
| `find_maximum` | Pulse `fn` | Linear scan, returns max; proves result exists in array & is universal maximum |
| `tick` | Pulse `ghost fn` | Increments `GhostReference.ref nat` counter |
| `complexity_bounded_min` | `let` predicate | `cf - c0 == n - 1` (exactly n−1 comparisons) |

### 2.2 SimultaneousMinMax (CLRS §9.1 — Simultaneous Min and Max)

| Function | Type | Description |
|----------|------|-------------|
| `find_minmax` | Pulse `fn` | Simple linear scan; finds both min and max in one pass |
| `find_minmax_pairs` | Pulse `fn` | **CLRS pair-processing**: compare pair, then smaller vs min, larger vs max |
| `find_minmax_complexity` | Pulse `fn` | `find_minmax` with ghost ticks; proves 2(n−1) comparisons |
| `find_minmax_pairs_complexity` | Pulse `fn` | `find_minmax_pairs` with ghost ticks; proves `2*(cf-c0) ≤ 3*n` (i.e., ≤ ⌊3n/2⌋) |
| `complexity_bounded_minmax` | `let` predicate | `cf - c0 <= 2*(n-1)` |
| `complexity_bounded_minmax_pairs` | `let` predicate | `2*(cf - c0) <= 3*n` |

### 2.3 PartialSelectionSort (Custom — not in CLRS)

| Function | Type | Description |
|----------|------|-------------|
| `find_min_index_from` | Pulse `fn` | Returns index of minimum in `a[start..n)` |
| `select` | Pulse `fn` | k rounds of selection sort; returns k-th smallest |
| `find_min_index_from_complexity` | Pulse `fn` | `find_min_index_from` with ghost tick counter |
| `select_complexity` | Pulse `fn` | `select` with ghost tick counter |
| `is_min_in_range` | `let` predicate | Element at index `i` is minimum of `a[start..start+len)` |
| `sorted_prefix` | `let` predicate | `s[0..bound)` is sorted |
| `prefix_leq_suffix` | `let` predicate | All elements in `[0,bound)` ≤ all in `[bound,n)` |
| `complexity_bounded_select` | `let` predicate | `cf - c0 <= k * (n - 1)` |

**Spec module (`PartialSelectionSort.Spec.fst`):**

| Function | Type | Description |
|----------|------|-------------|
| `is_sorted` | `let` predicate | Sequence is sorted |
| `count_occ` | `let rec` | Count occurrences of value in sequence |
| `is_permutation` | `let` predicate | Same multiset (via `count_occ`) |
| `count_lt` / `count_le` | `let rec` | Count elements strictly less / at most v |
| `pure_sort` | `let rec` | Insertion sort on sequences |
| `select_spec` | `let` | `(pure_sort s)[k]` — the k-th order statistic |
| `pure_sort_sorted` | `let rec` Lemma | `pure_sort` output is sorted |
| `pure_sort_permutation` | `let rec` Lemma | `pure_sort` output is a permutation |

**Correctness module (`PartialSelectionSort.Correctness.fst`):**

| Function | Type | Description |
|----------|------|-------------|
| `partition_left_part_correct` | Lemma | Elements `[lo,p)` all ≤ pivot |
| `partition_right_part_correct` | Lemma | Elements `(p,hi)` all ≥ pivot |
| `partition_pivot_is_kth` | Lemma | If partitioned correctly, pivot = `select_spec` for the slice |
| `pulse_correctness_hint` | Lemma | Bridge: partition ordering + `is_permutation` ⟹ `result == select_spec` |
| `select_spec_has_partition_property` | Lemma | `select_spec` satisfies the partition property |

**Complexity modules:**

| Function | Module | Description |
|----------|--------|-------------|
| `select_comparisons` | `Complexity.fst` | `k * (n - 1)` comparisons (overestimate) |
| `select_bound` | `Complexity.fst` | Proves `select_comparisons n k ≤ k * n` |
| `select_comparisons_exact` | `Complexity.fst` | Proves `select_comparisons n k == k * (n - 1)` |
| `select_comparisons_tight` | `Complexity.fst` | Tighter model: `Σ(n-i-1)` for `i=0..k-1` |
| `select_with_ticks` | `Complexity.Enhanced.fst` | Pure function returning `(result, tick_count)` |
| `select_complexity_bound` | `Complexity.Enhanced.fst` | Proves `ticks ≤ n²` |
| `quickselect_worst_case_cost` | `Complexity.Enhanced.fst` | Recurrence `T(n) = n + T(n-1)` |
| `quickselect_closed_form` | `Complexity.Enhanced.fst` | Proves `T(n) = n(n+1)/2 - 1` |

### 2.4 Quickselect (CLRS §9.2 — RANDOMIZED-SELECT, deterministic variant)

| Function | Type | Description |
|----------|------|-------------|
| `partition_in_range` | Pulse `fn` | Lomuto partition on `a[lo..hi)` with last-element pivot |
| `quickselect` | Pulse `fn` | Iterative quickselect; returns k-th smallest |
| `quickselect_correctness` | Lemma | Bridge: `permutation` + partition ordering ⟹ `select_spec` |
| `perm_lower_bound_forall` | Lemma | Propagates lower-bound across permutation with unchanged-outside |
| `perm_upper_bound_forall` | Lemma | Propagates upper-bound across permutation with unchanged-outside |
| `partition_in_range_complexity` | Pulse `fn` | `partition_in_range` with ghost tick counter |
| `quickselect_complexity` | Pulse `fn` | `quickselect` with ghost ticks; proves `complexity_bounded_quickselect` |
| `complexity_bounded_quickselect` | `let` predicate | `cf - c0 ≤ qs_cost(n)` |
| `partition_ordered` | `let` predicate | Elements `[lo,p)` ≤ pivot, elements `(p,hi)` ≥ pivot |
| `unchanged_outside` | `let` predicate | `s1` and `s2` agree outside `[lo,hi)` |

**Quickselect.Complexity.fst:**

| Function | Type | Description |
|----------|------|-------------|
| `qs_cost` | `let rec` | Recurrence: `T(n) = n + T(n-1)` |
| `qs_bound` | Lemma | `qs_cost(n) ≤ n(n+1)/2` |
| `qs_quadratic` | Lemma | `qs_cost(n) ≤ n²` |
| `qs_cost_monotone` | Lemma | `a ≤ b ⟹ qs_cost(a) ≤ qs_cost(b)` |

**Quickselect.Helpers.fst:**

| Function | Type | Description |
|----------|------|-------------|
| `seq_perm_implies_is_perm` | Lemma | Bridges `Seq.Properties.permutation` → `is_permutation` |
| `count_range_eq` | Lemma | Count in range is invariant when outside is unchanged |
| `perm_unchanged_lower_bound` | Lemma | Lower bound propagation through partition |
| `perm_unchanged_upper_bound` | Lemma | Upper bound propagation through partition |
| `perm_unchanged_lower_bound_forall` | Lemma | Universal lower bound after partition |
| `perm_unchanged_upper_bound_forall` | Lemma | Universal upper bound after partition |

---

## 3. Rubric Compliance Matrix

The canonical rubric requires **7 files per algorithm**: `Spec.fst`, `Lemmas.fst`, `Lemmas.fsti`, `Complexity.fst`, `Complexity.fsti`, `Impl.fst`, `Impl.fsti`.

### 3.1 MinMax

| Rubric File | Expected Name | Status | Actual File(s) |
|-------------|---------------|--------|-----------------|
| `Spec.fst` | `CLRS.Ch09.MinMax.Spec.fst` | ❌ Missing | Spec is inline in `MinMax.fst` (predicates `complexity_bounded_min`) |
| `Lemmas.fst` | `CLRS.Ch09.MinMax.Lemmas.fst` | ❌ Missing | No separate lemma module |
| `Lemmas.fsti` | `CLRS.Ch09.MinMax.Lemmas.fsti` | ❌ Missing | — |
| `Complexity.fst` | `CLRS.Ch09.MinMax.Complexity.fst` | 🔶 Inline | Ghost-tick proof is inside `MinMax.fst`, not separated |
| `Complexity.fsti` | `CLRS.Ch09.MinMax.Complexity.fsti` | ❌ Missing | — |
| `Impl.fst` | `CLRS.Ch09.MinMax.Impl.fst` | 🔶 Renamed | Implementation is `MinMax.fst` (not `.Impl.fst`) |
| `Impl.fsti` | `CLRS.Ch09.MinMax.Impl.fsti` | ❌ Missing | No interface file |

### 3.2 SimultaneousMinMax

| Rubric File | Expected Name | Status | Actual File(s) |
|-------------|---------------|--------|-----------------|
| `Spec.fst` | `CLRS.Ch09.SimultaneousMinMax.Spec.fst` | ❌ Missing | Spec predicates inline |
| `Lemmas.fst` | `CLRS.Ch09.SimultaneousMinMax.Lemmas.fst` | ❌ Missing | — |
| `Lemmas.fsti` | `CLRS.Ch09.SimultaneousMinMax.Lemmas.fsti` | ❌ Missing | — |
| `Complexity.fst` | `CLRS.Ch09.SimultaneousMinMax.Complexity.fst` | 🔶 Inline | Ghost-tick proof in `SimultaneousMinMax.fst` |
| `Complexity.fsti` | `CLRS.Ch09.SimultaneousMinMax.Complexity.fsti` | ❌ Missing | — |
| `Impl.fst` | `CLRS.Ch09.SimultaneousMinMax.Impl.fst` | 🔶 Renamed | Implementation is `SimultaneousMinMax.fst` |
| `Impl.fsti` | `CLRS.Ch09.SimultaneousMinMax.Impl.fsti` | ❌ Missing | — |

### 3.3 PartialSelectionSort (Custom)

| Rubric File | Expected Name | Status | Actual File(s) |
|-------------|---------------|--------|-----------------|
| `Spec.fst` | `CLRS.Ch09.PartialSelectionSort.Spec.fst` | ✅ Present | 674 lines; defines `select_spec`, `is_permutation`, `pure_sort` |
| `Lemmas.fst` | `CLRS.Ch09.PartialSelectionSort.Lemmas.fst` | 🔶 Split | Split across `SortedPerm.fst` (89 lines) + `Correctness.fst` (252 lines) |
| `Lemmas.fsti` | `CLRS.Ch09.PartialSelectionSort.Lemmas.fsti` | ❌ Missing | — |
| `Complexity.fst` | `CLRS.Ch09.PartialSelectionSort.Complexity.fst` | ✅ Present | 178 lines + `Enhanced.fst` (263 lines) + `Test.fst` (124 lines) |
| `Complexity.fsti` | `CLRS.Ch09.PartialSelectionSort.Complexity.fsti` | ❌ Missing | — |
| `Impl.fst` | `CLRS.Ch09.PartialSelectionSort.Impl.fst` | 🔶 Renamed | Implementation is `PartialSelectionSort.fst` (not `.Impl.fst`) |
| `Impl.fsti` | `CLRS.Ch09.PartialSelectionSort.Impl.fsti` | ❌ Missing | — |

### 3.4 Quickselect

| Rubric File | Expected Name | Status | Actual File(s) |
|-------------|---------------|--------|-----------------|
| `Spec.fst` | `CLRS.Ch09.Quickselect.Spec.fst` | 🔶 Shared | Uses `PartialSelectionSort.Spec.fst` (shared spec) |
| `Lemmas.fst` | `CLRS.Ch09.Quickselect.Lemmas.fst` | 🔶 Renamed | `Quickselect.Helpers.fst` (222 lines) serves this role |
| `Lemmas.fsti` | `CLRS.Ch09.Quickselect.Lemmas.fsti` | ❌ Missing | — |
| `Complexity.fst` | `CLRS.Ch09.Quickselect.Complexity.fst` | ✅ Present | 62 lines; `qs_cost`, `qs_bound`, `qs_quadratic` |
| `Complexity.fsti` | `CLRS.Ch09.Quickselect.Complexity.fsti` | ❌ Missing | — |
| `Impl.fst` | `CLRS.Ch09.Quickselect.Impl.fst` | 🔶 Renamed | Implementation is `Quickselect.fst` (not `.Impl.fst`) |
| `Impl.fsti` | `CLRS.Ch09.Quickselect.Impl.fsti` | ❌ Missing | — |

### Summary

| | Spec | Lemmas | Lemmas.fsti | Complexity | Complexity.fsti | Impl | Impl.fsti |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **MinMax** | ❌ | ❌ | ❌ | 🔶 | ❌ | 🔶 | ❌ |
| **SimultaneousMinMax** | ❌ | ❌ | ❌ | 🔶 | ❌ | 🔶 | ❌ |
| **PartialSelectionSort** | ✅ | 🔶 | ❌ | ✅ | ❌ | 🔶 | ❌ |
| **Quickselect** | 🔶 | 🔶 | ❌ | ✅ | ❌ | 🔶 | ❌ |

**Legend:** ✅ = fully compliant, 🔶 = present but naming/structure differs, ❌ = missing

---

## 4. Detailed Action Items

### 4.1 Structural / Rubric Compliance

| # | Priority | Action | Details |
|---|----------|--------|---------|
| S1 | P2 | Create `MinMax.Spec.fst` | Extract pure spec predicates (`complexity_bounded_min`) from `MinMax.fst` |
| S2 | P2 | Create `SimultaneousMinMax.Spec.fst` | Extract `complexity_bounded_minmax`, `complexity_bounded_minmax_pairs` |
| S3 | P3 | Rename `Quickselect.Helpers.fst` → `Quickselect.Lemmas.fst` | Aligns with rubric; currently serves the Lemmas role |
| S4 | P3 | Rename or alias `PartialSelectionSort.fst` → `PartialSelectionSort.Impl.fst` | Rubric expects `.Impl.fst` for Pulse implementations |
| S5 | P3 | Rename or alias `Quickselect.fst` → `Quickselect.Impl.fst` | Same as S4 |
| S6 | P3 | Rename or alias `MinMax.fst` → `MinMax.Impl.fst` | Same as S4 |
| S7 | P3 | Rename or alias `SimultaneousMinMax.fst` → `SimultaneousMinMax.Impl.fst` | Same as S4 |
| S8 | P3 | Create `.fsti` interface files | Rubric requires `Lemmas.fsti`, `Complexity.fsti`, `Impl.fsti` for each algorithm |

### 4.2 Specification & Correctness

| # | Priority | Action | Details |
|---|----------|--------|---------|
| C1 | ✅ DONE | Quickselect postcondition proves k-th order statistic | `quickselect` now has `result == Spec.select_spec s0 (SZ.v k)` (line 300) |
| C2 | ✅ DONE | Bridge permutation notions | `Quickselect.Helpers.seq_perm_implies_is_perm` bridges `Seq.Properties.permutation` → `is_permutation` |
| C3 | ✅ DONE | Wire correctness into quickselect | `quickselect_correctness` (line 259) calls `Helpers.seq_perm_implies_is_perm` then `Correctness.pulse_correctness_hint` |
| C4 | ✅ DONE | Partition ordering in postcondition | `quickselect` postcondition includes `∀i < k. s_final[i] ≤ result` and `∀i > k. result ≤ s_final[i]` (lines 295–298) |
| C5 | P2 | `PartialSelectionSort.select` doesn't prove `result == select_spec` | Postcondition has `sorted_prefix` + `prefix_leq_suffix` + `permutation` but doesn't explicitly state `result == select_spec s0 (k-1)`. The theoretical tools exist in `Correctness.fst` but aren't wired in. |

### 4.3 Complexity

| # | Priority | Action | Details |
|---|----------|--------|---------|
| X1 | ✅ DONE | Ghost-tick counter for quickselect | `quickselect_complexity` (line 444) proves `complexity_bounded_quickselect cf c0 n` via ghost ticks |
| X2 | ✅ DONE | Ghost-tick counter for PartialSelectionSort | `select_complexity` (line 374) proves `complexity_bounded_select cf c0 n k` |
| X3 | P2 | Tighten PartialSelectionSort complexity model | Model uses `n−1` comps/round; actual code uses `n−i−1`. Tight sum is `k*n − k*(k+1)/2`. `select_comparisons_tight` in `Complexity.fst` defines this but it is not connected to the Pulse ghost-tick proof |
| X4 | P3 | Create `MinMax.Complexity.fst` | Currently ghost ticks are inline in `MinMax.fst`; rubric wants a separate module |
| X5 | P3 | Create `SimultaneousMinMax.Complexity.fst` | Same as X4; currently inline |

### 4.4 CLRS Fidelity

| # | Priority | Action | Details |
|---|----------|--------|---------|
| F1 | ✅ DONE | CLRS pair-processing SimultaneousMinMax | `find_minmax_pairs` implements the pair-processing algorithm; `find_minmax_pairs_complexity` proves `2*(cf-c0) ≤ 3*n` |
| F2 | P3 | Quickselect uses deterministic pivot | Uses `a[hi-1]` not random pivot; comment on line 7 now correctly says "O(n²) worst case (deterministic pivot; O(n) expected requires randomized pivot, which is not implemented here)" |
| F3 | P3 | PartialSelectionSort is custom | Not a CLRS algorithm; well-documented as such; serves as verified baseline |

### 4.5 Code Quality

| # | Priority | Action | Details |
|---|----------|--------|---------|
| Q1 | P2 | Extract shared permutation infrastructure | ~65 lines duplicated between `Quickselect.fst` (33–85) and `PartialSelectionSort.fst` (55–138): `permutation`, `permutation_same_length`, `permutation_refl`, `compose_permutations`, `swap_is_permutation` |
| Q2 | P2 | Unify ghost tick infrastructure | `incr_nat` + `tick` duplicated in `MinMax.fst` (33–41), `SimultaneousMinMax.fst` (39–61), `PartialSelectionSort.fst` (284–297), `Quickselect.fst` (370–398) — 4 copies |
| Q3 | ✅ DONE | Fix `complexity_bounded_min` naming | Added `complexity_bounded_max` predicate in `MinMax.fst`; `find_maximum` now uses `complexity_bounded_max` |
| Q4 | ✅ DONE | Dead code: `partition_preserves_permutation` | Removed trivial identity lemma from `Correctness.fst` |
| Q5 | ✅ DONE | Dead code: `select_partition_spec` | Removed unused alias from `Correctness.fst` |
| Q6 | P3 | Module naming: `PartialSelectionSort.Correctness` contains quickselect lemmas | `partition_pivot_is_kth`, `pulse_correctness_hint` are about quickselect, not partial selection sort |
| Q7 | P3 | `Complexity.Enhanced.fst` covers both algorithms | Blurs boundary between PartialSelectionSort and Quickselect complexity |

### 4.6 Documentation

| # | Priority | Action | Details |
|---|----------|--------|---------|
| D1 | ✅ DONE | Fix "O(n) expected" comment | `Quickselect.fst:7` now correctly states "O(n²) worst case (deterministic pivot; O(n) expected requires randomized pivot, which is not implemented here)" |
| D2 | ✅ DONE | Fix stale `Select.fst` reference | `Quickselect.fst:9` now references `PartialSelectionSort.fst` |
| D3 | ✅ DONE | SimultaneousMinMax header updated | Header (lines 1–21) now documents both simple scan and CLRS pair-processing implementations |
| D4 | ✅ DONE | `PartialSelectionSort.fst:33` claims randomization "not available" | Fixed: removed "(not available)" — randomization is available in Pulse |
| D5 | ✅ DONE | `Complexity.Enhanced.fst:25` header says "Quickselect" | Fixed: header now says "Partial Selection Sort and Quickselect" |

---

## 5. Quality Checks

### 5.1 Admits & Assumes

| Check | Result |
|-------|--------|
| `admit` in any `.fst` file | ✅ **None found** — all 12 files are admit-free |
| `assume` in any `.fst` file | ✅ **None found** |
| `sorry` in any `.fst` file | ✅ **None found** |

### 5.2 Proof Completeness

| Property | MinMax | SimultaneousMinMax | PartialSelectionSort | Quickselect |
|----------|:------:|:------------------:|:--------------------:|:-----------:|
| Functional correctness | ✅ min/max proved | ✅ min/max proved | ✅ `sorted_prefix` + `prefix_leq_suffix` | ✅ `result == select_spec` |
| Permutation preservation | n/a (read-only) | n/a (read-only) | ✅ `permutation s0 s_final` | ✅ `permutation s0 s_final` |
| k-th order statistic | n/a | n/a | 🔶 Implied but not explicit | ✅ Proved via `quickselect_correctness` |
| Complexity bound (ghost ticks) | ✅ n−1 exact | ✅ 2(n−1) and ⌊3n/2⌋ | ✅ k*(n−1) | ✅ qs_cost(n) ≤ n² |
| Complexity connected to impl | ✅ Same file | ✅ Same file | ✅ `select_complexity` | ✅ `quickselect_complexity` |

### 5.3 SMT Configuration

| File | z3rlimit | Notable Flags |
|------|:--------:|---------------|
| `MinMax.fst` | 20 | — |
| `SimultaneousMinMax.fst` | up to 500 | `--ifuel 3 --fuel 3` on `find_minmax_pairs_complexity` |
| `PartialSelectionSort.fst` | up to 200 | — |
| `PartialSelectionSort.Spec.fst` | 20–60 | `--warn_error -328` for `rec` annotation |
| `PartialSelectionSort.SortedPerm.fst` | 20 | `--z3refresh`, `#restart-solver`, `--split_queries always` |
| `PartialSelectionSort.Correctness.fst` | up to 80 | `#restart-solver` between lemmas |
| `PartialSelectionSort.Complexity.fst` | 20 | — |
| `PartialSelectionSort.Complexity.Enhanced.fst` | 20–30 | — |
| `Quickselect.fst` | up to 200 | `--ifuel 2 --fuel 2` |
| `Quickselect.Complexity.fst` | default | — |
| `Quickselect.Helpers.fst` | up to 80 | — |

**Concerns:** `--z3rlimit 500` in `SimultaneousMinMax.fst` and `200` in `Quickselect.fst` / `PartialSelectionSort.fst` are aggressive. The `#restart-solver` and `--z3refresh` in `SortedPerm.fst` indicate solver sensitivity.

### 5.4 SNIPPET Markers

Files with `SNIPPET_START`/`SNIPPET_END` markers (for documentation extraction):

| File | Snippets |
|------|:--------:|
| `MinMax.fst` | 3 |
| `PartialSelectionSort.fst` | 2 |
| `PartialSelectionSort.SortedPerm.fst` | 1 |
| `PartialSelectionSort.Spec.fst` | 1 |
| `Quickselect.fst` | 3 |
| `SimultaneousMinMax.fst` | 4 |

### 5.5 Overall Rubric Compliance Score

| Dimension | Score | Notes |
|-----------|:-----:|-------|
| **Rubric file structure** | 4/10 | No `.fsti` interfaces; Spec/Complexity often inline; naming doesn't follow `*.Impl.fst` convention |
| **CLRS fidelity** | 8/10 | MinMax faithful; SimultaneousMinMax now has pair-processing ✅; Quickselect is deterministic variant; PartialSelectionSort is custom |
| **Specification strength** | 8/10 | Quickselect now proves k-th order statistic ✅; PartialSelectionSort strong but implicit; permutation bridge done ✅ |
| **Complexity proofs** | 8/10 | All four algorithms have ghost-tick proofs connected to Pulse implementations ✅; tight bound for PartialSelectionSort not wired in |
| **Proof quality** | 9/10 | Zero admits; permutation notions bridged ✅; solver sensitivity in SortedPerm |
| **Code quality** | 6/10 | ~65 lines permutation duplication × 2; ~30 lines ghost-tick duplication × 4; aggressive z3rlimits. Dead code removed ✅; naming fixed ✅ |
| **Documentation** | 9/10 | Honest about limitations; inaccurate comments fixed ✅ |
| **Overall** | 7.4/10 | Strong verification foundation; main gaps are rubric structural compliance and code deduplication |

### 5.6 Progress Since Audit

| Audit Finding | Status | Evidence |
|---------------|:------:|---------|
| P0-1: Strengthen quickselect postcondition | ✅ Fixed | Lines 295–300 in `Quickselect.fst` |
| P0-2: Bridge permutation notions | ✅ Fixed | `seq_perm_implies_is_perm` in `Helpers.fst:214` |
| P0-3: Wire correctness into quickselect | ✅ Fixed | `quickselect_correctness` at line 259 |
| P1-1: CLRS pair-processing SimultaneousMinMax | ✅ Fixed | `find_minmax_pairs` + `find_minmax_pairs_complexity` in `SimultaneousMinMax.fst` |
| P1-2: Fix misleading "O(n) expected" comment | ✅ Fixed | Line 7 now says "O(n²) worst case (deterministic pivot)" |
| P2-3: Ghost-tick counter for Pulse quickselect | ✅ Fixed | `quickselect_complexity` at line 444 |
| P2-4: Ghost-tick counter for Pulse `select` | ✅ Fixed | `select_complexity` at line 374 |
| P2-5: Tighten PartialSelectionSort complexity | 🔶 Partial | `select_comparisons_tight` exists in pure F* but not connected to Pulse proof |
| P3-2: Fix `complexity_bounded_min` naming | ✅ Fixed | Added `complexity_bounded_max`; `find_maximum` now uses it |
| P3-3: Fix stale `Select.fst` reference | ✅ Fixed | Line 9 now references `PartialSelectionSort.fst` |
| P3-5: Fix D1 comment accuracy | ✅ Fixed | Comment updated |
| P2-1: Extract shared permutation infra | ❌ Open | Still duplicated |
| P2-2: Unify ghost-tick infrastructure | ❌ Open | Still duplicated in 4 files |
| P3-1: Remove dead code | ✅ Fixed | Removed `partition_preserves_permutation` and `select_partition_spec` from `Correctness.fst` |
| P3-4: Rename Correctness/Spec modules | ❌ Open | `PartialSelectionSort.Correctness` still contains quickselect lemmas |
| P3-6: Reduce z3rlimit 200 | ❌ Open | z3rlimit 200 still used; z3rlimit 500 added in `SimultaneousMinMax.fst` |
