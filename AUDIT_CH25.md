# Audit Report — Chapter 25: All-Pairs Shortest Paths (Floyd-Warshall)

**Directory:** `ch25-apsp/`
**Date:** 2025-07-15
**Files audited:**

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch25.FloydWarshall.fst` | 189 | Pulse implementation + pure mirror spec |
| `CLRS.Ch25.FloydWarshall.Spec.fst` | 388 | Correctness proof (fw_outer ≡ fw_entry) |
| `CLRS.Ch25.FloydWarshall.Complexity.fst` | 221 | O(n³) ghost-tick proof |
| `CLRS.Ch25.FloydWarshall.Test.fst` | 58 | 3×3 smoke test |
| **Total** | **856** | |

All four `.checked` files exist in `_cache/`, confirming successful prior verification.

---

## 1. CLRS Fidelity

### CLRS Reference
CLRS 3 ed., §25.2, p. 695, procedure FLOYD-WARSHALL(W) and recurrence (25.5):

```
d(0)[i][j] = w(i,j)
d(k)[i][j] = min( d(k−1)[i][j],  d(k−1)[i][k] + d(k−1)[k][j] )   for k ≥ 1
```

The pseudocode is (1-indexed):
```
for k = 1 to n
  for i = 1 to n
    for j = 1 to n
      d(k)[i][j] = min(d(k-1)[i][j], d(k-1)[i][k] + d(k-1)[k][j])
```

### Implementation mapping

| CLRS element | Code | Notes |
|---|---|---|
| 1-indexed vertices {1..n} | 0-indexed {0..n−1} | Standard; k in code = k−1 in CLRS |
| Separate D^(k) matrices | In-place single array | Correct: FW is safe to do in-place because d^(k)[i][k] = d^(k-1)[i][k] and d^(k)[k][j] = d^(k-1)[k][j] when there are no negative cycles. The Spec file proves row-k preservation (`lemma_fw_inner_i_preserves_row_k`). |
| w(i,j) ← edge weight | `inf = 1000000` sentinel | Finite sentinel, not ∞ — see issue below |
| Π predecessor matrix | Not implemented | CLRS §25.2 includes predecessor matrix construction — omitted here |
| Outer loop k | `fw_outer` / imperative `while` on `k` | ✅ Matches |
| Inner loops i, j | `fw_inner_i`, `fw_inner_j` | ✅ Matches |
| Relaxation | `new_val = if via_k < d_ij then via_k else d_ij` | ✅ Matches min operation |

### Fidelity verdict: **HIGH**

Loop structure and recurrence are faithfully implemented. The 0-indexing shift is handled correctly — `fw_entry` with `k=0` returns the raw adjacency entry, and the recurrence for `k ≥ 1` refers to intermediate vertex `k−1` (0-indexed), matching CLRS's 1-indexed vertex `k`.

**Notable gaps:**
- No predecessor (Π) matrix — path reconstruction not supported.
- Finite sentinel (`inf = 1000000`) instead of mathematical ∞ — could produce incorrect results if shortest paths exceed this value; no formal guard against this.

---

## 2. Specification Strength

### What is proven

The specification file proves a **two-level** correctness result:

1. **fw_outer ≡ fw_entry recurrence** (the main theorem):
   ```
   floyd_warshall_computes_shortest_paths:
     fw_outer(adj, n, 0)[qi*n+qj] == fw_entry(adj, n, qi, qj, n)
   ```
   This says the imperative loop output equals the closed-form DP recurrence evaluated through all n intermediate vertices.

2. **Imperative code ≡ pure spec** (in the main `.fst` file):
   ```
   ensures contents' == fw_outer contents (SZ.v n) 0
   ```
   The Pulse function's postcondition ties the mutable array to the pure functional spec.

### What is NOT proven

| Property | Status |
|---|---|
| `fw_entry(adj, n, i, j, n) == δ(i,j)` (true shortest-path distance) | ❌ Not proven — no graph/path formalism exists |
| No-negative-cycle detection | ❌ Assumed as precondition (`fw_entry adj n v v k >= 0` for all k, v) |
| Integer overflow safety for `int` additions | ❌ F* `int` is mathematical; no issue in spec, but `inf` sentinel could silently wrap around in a real extraction |
| Predecessor matrix correctness | ❌ Not implemented |

### fw_entry recurrence analysis

The `fw_entry` definition (Spec.fst:28–37):
```fstar
let rec fw_entry (adj: seq int) (n: nat) (i j k: nat) : Tot int (decreases k) =
  if i >= n || j >= n || length adj <> n * n then inf
  else if k = 0 then index adj (i * n + j)
  else
    let without = fw_entry adj n i j (k - 1) in
    let d_ik = fw_entry adj n i (k - 1) (k - 1) in
    let d_kj = fw_entry adj n (k - 1) j (k - 1) in
    if d_ik + d_kj < without then d_ik + d_kj else without
```

This precisely matches CLRS recurrence (25.5) with the 0-indexing shift:
- `k=0` → base case: direct edge weight
- `k≥1` → `min(d^(k-1)[i][j], d^(k-1)[i][k-1] + d^(k-1)[k-1][j])`

The `k-1` for vertex indices is correct because intermediate vertex set {0..k-1} with k vertices maps to CLRS's {1..k}.

### Spec strength verdict: **MEDIUM-HIGH**

The recurrence equivalence is solid and fully proven. The gap is the absence of a graph-path semantics connecting `fw_entry(adj, n, i, j, n)` to true `δ(i,j)`. The no-negative-cycle property is assumed rather than checked.

---

## 3. Complexity

### Proven bound

`CLRS.Ch25.FloydWarshall.Complexity.fst` uses a ghost counter (`GR.ref nat`) incremented once per relaxation step in the innermost loop (line 208). The postcondition states:

```fstar
fw_complexity_bounded cf (reveal c0) (SZ.v n)
  ≡ cf >= c0 /\ cf - c0 == n * n * n
```

This proves **exactly n³ relaxation operations**, matching CLRS's Θ(V³).

### Loop invariant structure

| Loop | Counter invariant |
|------|------------------|
| k-loop | `vc - c0 == vk * n * n` |
| i-loop | `vc_i - c0 == vk * n * n + vi * n` |
| j-loop | `vc_j - c0 == vk * n * n + vi * n + vj` |

At termination: `vk = n`, giving `cf - c0 = n * n * n = n³`. ✅

### Complexity verdict: **STRONG**

Exact operation count proven. Ghost counter is erased at extraction time.

---

## 4. Code Quality

### Strengths
- **Clean separation of concerns**: pure spec, imperative code, correctness proof, and complexity proof in separate files.
- **Pulse best practices**: explicit array ops (`op_Array_Access`/`op_Array_Assignment`), unconditional writes, clean `invariant exists*` patterns.
- **d_ik caching**: `d_ik` is read once before the j-loop (line 145 of main .fst), matching the pure spec which threads `d_ik` through `fw_inner_j`. This is a thoughtful optimization.
- **Low solver resource usage**: max `z3rlimit` is 40; only two `#push-options` blocks.
- **All `.checked` files present**: code verifies successfully.

### Weaknesses

| Issue | Severity | Location |
|-------|----------|----------|
| **Code duplication**: Complexity.fst re-declares `inf`, `fw_inner_j`, `fw_inner_i`, `fw_outer`, and all three `lemma_fw_*_len` functions verbatim instead of importing from the main module | Medium | Complexity.fst:47–99 |
| **Finite infinity sentinel**: `inf = 1000000` is a concrete value; if edge weights sum past this, results are silently wrong. No type-level guard. | Medium | FloydWarshall.fst:18 |
| **No bounds on element values**: The spec allows arbitrary `int` values in the adjacency matrix; no precondition guards against overflow when adding two large weights. Since F* `int` is unbounded this is sound in the spec, but extraction to C/machine ints would be unsound. | Low | FloydWarshall.fst:88–105 |
| **Test has no assertions**: `test_floyd_warshall` runs FW but never checks the output values. It is a compilation/type-check test, not a correctness test. | Medium | Test.fst:50–57 |
| **README inaccuracies**: States "rlimit 5" and "Max rlimit used: 0.134" but code uses `z3rlimit 20` and `z3rlimit 40`. Also states "Minimal invariants" but the invariants are quite involved (full functional correctness in each loop). | Low | README.md:53, 78–82 |

### Code quality verdict: **GOOD** — clean, well-structured; main issue is the duplication in Complexity.fst.

---

## 5. Proof Quality

### Admits and Assumes

**ZERO admits. ZERO assumes.** Confirmed by `grep -n "admit\|assume\|sorry"` across all four files (only matches are in comments stating "NO admits. NO assumes.").

### Proof architecture

The specification proof (388 lines) is structured in 6 sections:

1. **§1** `fw_entry` — recurrence definition (8 lines)
2. **§2** `lemma_fw_inner_j_*` — inner-j loop properties: other-pos preservation, earlier-col preservation, correctness (lines 60–151, ~90 lines)
3. **§3** `lemma_fw_inner_i_*` — inner-i loop properties: earlier-row preservation, row-k preservation (lines 157–240, ~80 lines)
4. **§4** `lemma_fw_inner_i_correct` — one full FW iteration correct (lines 247–302, ~55 lines)
5. **§5** `fw_outer_computes_entry` — inductive main theorem (lines 333–370, ~40 lines)
6. **§6** `floyd_warshall_computes_shortest_paths` — top-level corollary (lines 378–387, 10 lines)

### Key proof obligations discharged

| Lemma | What it proves |
|-------|---------------|
| `lemma_fw_inner_j_correct` | After j-loop, entry [i,j'] = min(old, d_ik + d[k,j']) |
| `lemma_fw_inner_j_preserves_row_k` | j-loop for row i≠k leaves row k unchanged |
| `lemma_fw_inner_i_preserves_row_k` | Full i-loop leaves row k unchanged (requires non-negative diagonal) |
| `lemma_fw_inner_i_correct` | After i-loop, all entries = min(old, d[i,k]+d[k,j]) with original d[k,*] values |
| `lemma_fw_step` | One FW iteration advances fw_entry level k → k+1 |
| `fw_outer_computes_entry` | Full FW computes fw_entry at level n |

### Solver options

| Location | Options |
|----------|---------|
| FloydWarshall.fst:9 | `--z3rlimit 20` (module-level) |
| Complexity.fst:23 | `--z3rlimit 40` (module-level) |
| Spec.fst:109 | `--split_queries always` (for `lemma_fw_inner_j_correct`) |
| Spec.fst:310 | `--z3rlimit 40` (for `lemma_fw_step`) |

All limits are modest. No `--z3seed` hacks or excessive fuel/ifuel settings.

### Proof quality verdict: **EXCELLENT** — zero admits, clean inductive structure, modest solver resources.

---

## 6. Documentation Accuracy

### README.md assessment

| Claim | Actual | Accurate? |
|-------|--------|-----------|
| "Fully verified" | Yes — all `.checked` present, zero admits | ✅ |
| "NO admits" | Confirmed | ✅ |
| "NO assumes" | Confirmed | ✅ |
| "Memory safe" | Array bounds are proven via index arithmetic + `SZ.fits` | ✅ |
| "Low rlimit — rlimit 5" | Code uses `z3rlimit 20` and `z3rlimit 40` | ❌ |
| "Max rlimit used: 0.134 (out of 5)" | Stale; limits are 20/40 now | ❌ |
| "Total queries: ~20" | Not independently verified | ⚠️ |
| "Minimal invariants" | Invariants encode full functional correctness | ❌ Misleading |
| Postcondition in README only shows `Seq.length contents' == ...` | Actual postcondition also includes `contents' == fw_outer ...` | ❌ Incomplete |
| "cd /home/nswamy/workspace/clrs/ch25-apsp" | Path should be `AutoCLRS/ch25-apsp` | ❌ Wrong path |

### Spec.fst header

| Claim | Actual | Accurate? |
|-------|--------|-----------|
| "CLRS Theorem 25.2" | Should be "CLRS Equation 25.5 / §25.2" — there is no "Theorem 25.2" in CLRS | ⚠️ Minor |
| "Connecting fw_entry to true shortest-path distances" (line 10) | Not actually done — fw_entry is NOT connected to δ(i,j) | ❌ Overstates |

### Documentation verdict: **FAIR** — structurally good but contains stale statistics and one material overstatement about connecting to true δ(i,j).

---

## 7. Task List

### Priority 1 — Correctness / Soundness

| # | Task | Rationale |
|---|------|-----------|
| P1-1 | **Connect fw_entry to graph-theoretic δ(i,j)**: Define path/walk types over the adjacency matrix, define `shortest_path_weight`, and prove `fw_entry adj n i j n == shortest_path_weight adj n i j` under the no-negative-cycle assumption. | Without this, the "shortest paths" claim is only about the recurrence, not the actual graph property. |
| P1-2 | **Guard the infinity sentinel**: Either (a) add a precondition bounding all edge weights so that path sums cannot reach `inf`, or (b) replace `inf` with an option type / extended-integer type. | Current code silently produces wrong results if weights are large. |
| P1-3 | **Add runtime assertions or preconditions for no-negative-cycle**: The Spec file assumes `fw_entry adj n v v k >= 0` for all k,v. The imperative code has no such check. At minimum, add a post-loop diagonal check, or strengthen the Floyd-Warshall precondition to require non-negative diagonal in the input. | Caller could pass a graph with negative cycles and get silently wrong results. |
| P2-1 | **Eliminate code duplication in Complexity.fst**: Import `fw_inner_j`, `fw_inner_i`, `fw_outer`, `inf`, and length lemmas from `CLRS.Ch25.FloydWarshall` instead of re-declaring them. | ~50 lines of exact duplication. Divergence risk if one copy is updated. |
| P2-2 | **Add output assertions to Test.fst**: After `floyd_warshall dist n`, read back entries and assert expected values (e.g., `d[0][2] == 20`, `d[1][0] == 45`). | Current test only checks that the code compiles and runs without crashing. |
| P3-1 | **Fix README statistics**: Update rlimit values (20/40, not 5), remove stale timing numbers, fix the build path. | Currently misleading. |
| P3-2 | **Fix Spec.fst header**: Change "CLRS Theorem 25.2" → "CLRS Equation 25.5, §25.2". Remove claim about connecting to true shortest-path distances (line 10) until P1-1 is done. | Overstatement. |
| P3-3 | **Update README postcondition snippet**: Show the full postcondition including `contents' == fw_outer contents (SZ.v n) 0`. | README currently omits the functional-correctness ensures clause. |

### Defer

| # | Task | Rationale |
|---|------|-----------|
| P2-3 | **Implement predecessor matrix (Π)**: Add optional path-reconstruction support per CLRS §25.2. | Needed for complete CLRS coverage. |

---

## Summary Scorecard

| Dimension | Rating | Notes |
|-----------|--------|-------|
| CLRS Fidelity | ★★★★☆ | Faithful loop/recurrence; no Π matrix |
| Specification Strength | ★★★★☆ | Recurrence proven; no δ(i,j) connection |
| Complexity | ★★★★★ | Exact n³ count, ghost-erased |
| Code Quality | ★★★★☆ | Clean Pulse; duplication in Complexity.fst |
| Proof Quality | ★★★★★ | Zero admits, modest solver resources |
| Documentation | ★★★☆☆ | Stale stats, one material overstatement |
| **Overall** | **★★★★☆** | Strong verified implementation with room to close the spec gap to δ(i,j) |
