# Floyd-Warshall ImplTest — Spec Validation Report

**File:** `CLRS.Ch25.FloydWarshall.ImplTest.fst`
**Algorithm:** Floyd-Warshall All-Pairs Shortest Paths (CLRS §25.2)
**API under test:** `floyd_warshall` from `CLRS.Ch25.FloydWarshall.Impl.fsti`
**Status:** ✅ Fully proven — zero admits, zero assumes

---

## Methodology

Spec validation following the methodology of
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757). The test calls the
Pulse API on a concrete 3×3 graph and proves that the postcondition is
precise enough to determine all output values exactly.

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

### 4. Determinism

The postcondition `contents' == fw_outer contents n 0` is fully
deterministic — there is exactly one admissible output for any given
input. No enumeration of equivalent outputs is needed (unlike
algorithms with non-unique valid outputs such as sorting with equal
keys).

### 5. End-to-End Pulse Test

The `test_floyd_warshall_impl` Pulse function:
1. Allocates and initializes the 3×3 matrix
2. Proves the concrete array equals `test_adj` (via `lemma_seq_eq_test_adj`)
3. Calls `floyd_warshall` (the Impl.fsti API)
4. Asserts all 9 output values using the precision lemmas
5. Asserts the complexity bound (cf == 27)
6. Cleans up all resources

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

### No Spec Weaknesses Found

- **Precondition:** Not too strong — satisfiable for all valid inputs.
- **Postcondition:** Not too weak — determines the output uniquely.
- **No admits or assumes needed** in the test.

The specification in `Impl.fsti` is well-designed for this algorithm.
The layered approach (Impl → Spec → Lemmas → Paths) cleanly separates
the imperative refinement from the graph-theoretic correctness.

---

## Solver Settings

```
--fuel 8 --ifuel 2 --z3rlimit 80 --split_queries always
```

These are used for the `fw_entry` evaluation and `fw_outer` connection
lemmas. The Pulse test function uses default settings.
