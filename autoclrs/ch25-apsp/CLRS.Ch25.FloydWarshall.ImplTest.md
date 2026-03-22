# Floyd-Warshall ImplTest — Spec Validation Report

**File:** `CLRS.Ch25.FloydWarshall.ImplTest.fst`
**Algorithm:** Floyd-Warshall All-Pairs Shortest Paths (CLRS §25.2)
**API under test:** `floyd_warshall` from `CLRS.Ch25.FloydWarshall.Impl.fsti`,
  `check_no_negative_cycle` and `floyd_warshall_safe` from
  `CLRS.Ch25.FloydWarshall.NegCycleDetect`
**Status:** ✅ Fully proven — zero admits, zero assumes

---

## Methodology

Spec validation following the methodology of
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757). The test calls the
Pulse APIs on concrete inputs and proves that the postconditions are
precise enough to determine all output values exactly, including both
success and error cases.

---

## Test Instance

**Input** — 3×3 adjacency matrix (inf = 1000000):

```
    0   1   2
0 [ 0   5  inf ]
1 [ 50  0   15 ]
2 [ 30 inf  0  ]
```

**Expected output** — shortest-path distances:

```
    0   1   2
0 [ 0   5   20 ]
1 [ 45  0   15 ]
2 [ 30  35  0  ]
```

**Error-case input** — matrix with negative diagonal d[0][0] = -1:

```
    0   1   2
0 [-1   5  inf ]
1 [ 50  0   15 ]
2 [ 30 inf  0  ]
```

---

## What Is Proven

### 1. Precondition Satisfiability

The `floyd_warshall` function requires:
- `Seq.length contents == SZ.v n * SZ.v n` (array properly sized)
- `SZ.fits (SZ.v n * SZ.v n)` (no size_t overflow)

**Proven:** `precondition_satisfiable` — both conditions hold for n = 3
with the 9-element test adjacency matrix.

### 2. Postcondition Precision (All 9 Entries)

The postcondition states `contents' == fw_outer contents (SZ.v n) 0`.
This is proven to determine every output entry exactly:

| Entry | Lemma | Index | Value | Status |
|-------|-------|-------|-------|--------|
| d[0][0] | `post_entry_00` | 0 | 0 | ✅ |
| d[0][1] | `post_entry_01` | 1 | 5 | ✅ |
| d[0][2] | `post_entry_02` | 2 | 20 | ✅ |
| d[1][0] | `post_entry_10` | 3 | 45 | ✅ |
| d[1][1] | `post_entry_11` | 4 | 0 | ✅ |
| d[1][2] | `post_entry_12` | 5 | 15 | ✅ |
| d[2][0] | `post_entry_20` | 6 | 30 | ✅ |
| d[2][1] | `post_entry_21` | 7 | 35 | ✅ |
| d[2][2] | `post_entry_22` | 8 | 0 | ✅ |

**Proof strategy:** Two-step chain for each entry:
1. `fw_val_ij ()` — proves `fw_entry test_adj 3 i j 3 == expected`
   (SMT solver evaluates the recursive DP recurrence with `--fuel 8`)
2. `floyd_warshall_full_correctness test_adj 3 i j` — connects
   `fw_outer` to `fw_entry`, proving
   `Seq.index (fw_outer test_adj 3 0) (i*3+j) == fw_entry test_adj 3 i j 3`

These two facts together prove the exact output value at each position.

### 3. Complexity Bound

`complexity_bound` proves `fw_complexity_bounded 27 0 3`, confirming
the ghost tick counter records exactly n³ = 3³ = 27 relaxation operations.

The Pulse test function asserts `cf == 27` after the call, verifying
the complexity postcondition is precise enough to determine the exact
operation count.

### 4. Negative-Cycle Detection — Return Value Precision

The `check_no_negative_cycle` function's strengthened postcondition:

```
(b == true  ==>  non_negative_diagonal contents n) /\
(b == false ==> ~(non_negative_diagonal contents n))
```

fully characterizes the return value. Two tests verify this:

**4a. Success case** (`test_neg_cycle_check_true`):
- Input: `test_adj` with non-negative diagonal (0, 0, 0)
- `lemma_test_adj_non_negative_diagonal ()` proves `non_negative_diagonal test_adj 3`
- From the false-case conjunct: `ok == false` would imply
  `~(non_negative_diagonal ...)`, contradicting the lemma
- Therefore `ok == true` is provable ✅

**4b. Error case** (`test_neg_cycle_check_false`):
- Input: `neg_diag_adj` with d[0][0] = -1
- `lemma_neg_diag_not_nonneg ()` proves `~(non_negative_diagonal neg_diag_adj 3)`
- From the true-case conjunct: `ok == true` would imply
  `non_negative_diagonal ...`, contradicting the lemma
- Therefore `ok == false` is provable ✅

**Previous spec weakness:** Before strengthening, the postcondition only
constrained the `true` case. The `false` case was vacuously true,
making it impossible to prove `ok == false` from the spec alone.

### 5. Determinism

The postcondition `contents' == fw_outer contents n 0` is fully
deterministic — there is exactly one admissible output for any given
input. No enumeration of equivalent outputs is needed (unlike
algorithms with non-unique valid outputs such as sorting with equal
keys).

### 6. floyd_warshall_safe API

`test_floyd_warshall_safe_impl` tests the safe wrapper with full
preconditions (`weights_bounded` + `non_negative_diagonal`):

- `lemma_test_adj_weights_bounded ()` proves `weights_bounded test_adj 3`
- `lemma_test_adj_non_negative_diagonal ()` proves `non_negative_diagonal test_adj 3`
- Calls `floyd_warshall_safe` (requires both preconditions)
- Verifies 4 representative output entries using `fw_safe_entry_connection`
  (a helper lemma that connects `fw_outer` to `fw_entry` for callers
  of the safe API)
- Verifies complexity (cf == 27) ✅

### 7. End-to-End Pulse Tests

| Test | API Tested | What Is Proven | Status |
|------|-----------|----------------|--------|
| `test_floyd_warshall_impl` | `floyd_warshall` | All 9 outputs + complexity | ✅ |
| `test_neg_cycle_check_true` | `check_no_negative_cycle` | `ok == true` determined by spec | ✅ |
| `test_neg_cycle_check_false` | `check_no_negative_cycle` | `ok == false` determined by spec | ✅ |
| `test_floyd_warshall_safe_impl` | `floyd_warshall_safe` | 4 outputs + complexity via safe API | ✅ |

---

## Spec Quality Assessment

### Strengths

- **Postcondition is maximally precise:** `contents' == fw_outer contents n 0`
  gives full functional refinement — the output is definitionally equal to the
  pure specification, not merely "some correct answer."

- **Exact complexity:** `fw_complexity_bounded cf c0 n ≡ cf - c0 == n³`
  is an exact count, not asymptotic.

- **Precondition is minimal:** Only requires the array to be properly sized
  and `SZ.fits`. No unnecessary constraints.

- **Negative-cycle detection return value is fully determined:** The
  strengthened postcondition makes `b` a perfect characterization of
  `non_negative_diagonal`, enabling proofs of both success and error cases.

### Previous Spec Weakness (Now Resolved)

- **`check_no_negative_cycle` false case was unconstrained.** The original
  postcondition `(b == true ==> non_negative_diagonal ...)` said nothing
  when `b == false`. This made it impossible to prove that `false` correctly
  indicates a negative diagonal entry. The spec has been strengthened to
  include `(b == false ==> ~(non_negative_diagonal ...))`, making the
  return value fully determined by the input.

---

## Solver Settings

```
--fuel 8 --ifuel 2 --z3rlimit 80 --split_queries always
```

These are used for the `fw_entry` evaluation and `fw_outer` connection
lemmas. The Pulse test functions use default settings. The
`lemma_neg_diag_not_nonneg` and `lemma_test_adj_non_negative_diagonal`
lemmas use `--z3rlimit 40`.

---

## Concrete Execution (C Extraction)

The implementation modules (`Impl.fst`, `NegCycleDetect.fst`) are
extracted to C via KaRaMeL and compiled into an executable test.

**Extraction pipeline:**
1. F* `--codegen krml` extracts `Impl` and `NegCycleDetect` to `.krml`
2. KaRaMeL bundles them into `CLRS_Ch25_FloydWarshall.c` with
   `-bundle` to eliminate unreachable code (specs, lemmas, ghost state)
3. gcc compiles the bundled C + `test_main.c` driver
4. The test exercises the same 3×3 instance used in the Pulse proofs

**Note:** The verified Pulse test functions (`test_floyd_warshall_impl`,
etc.) are ghost-erased during extraction (their bodies become `()` after
erasing all separation-logic assertions, lemma calls, and ghost reference
operations). The C test driver calls the extracted `floyd_warshall`,
`check_no_negative_cycle`, and `floyd_warshall_safe` functions directly,
verifying the same expected outputs.

**Implementation change for extraction:** In `Impl.fst`, the inner-loop
arithmetic (`d_ik + d_kj`, `via_k < d_ij`) was changed from
`Pulse.Lib.BoundedIntegers` operators to explicit `Prims.op_Addition` /
`Prims.op_LessThan` calls. The `BoundedIntegers` typeclass record is
not recognized by KaRaMeL; the explicit Prims operators extract to
standard C integer operations. The proof obligations are unchanged.

**Build:** `make test-c` (from `autoclrs/ch25-apsp/`)

**Concrete execution results (2026-03-22):**

```
=== Ch25 Floyd-Warshall: Concrete Execution Tests ===

Test 1: floyd_warshall on 3x3 graph
  Input:
    [   0,   5, inf ]
    [  50,   0,  15 ]
    [  30, inf,   0 ]
  Output:
    [   0,   5,  20 ]
    [  45,   0,  15 ]
    [  30,  35,   0 ]
  => PASS

Test 2: check_no_negative_cycle (non-negative diagonal)
  Result: true (expected: true)
  => PASS

Test 3: check_no_negative_cycle (negative diagonal)
  Result: false (expected: false)
  => PASS

Test 4: floyd_warshall_safe on 3x3 graph
  Input:
    [   0,   5, inf ]
    [  50,   0,  15 ]
    [  30, inf,   0 ]
  Output:
    [   0,   5,  20 ]
    [  45,   0,  15 ]
    [  30,  35,   0 ]
  => PASS

=== Results: 4 passed, 0 failed ===
```

**Status:** ✅ All 4 concrete execution tests pass — the extracted C code
produces results identical to the proven specification values.
