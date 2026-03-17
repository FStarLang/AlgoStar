# ModExp (R-to-L) Spec Validation Test

## Test: `2^10 mod 1000 = 24`

### Input
- `b = 2`, `e = 10`, `m = 1000`

### Expected Output
- `pow(2, 10) mod 1000 = 1024 mod 1000 = 24`

### What is Proven

1. **Precondition satisfiability**: The only precondition is the ghost counter
   (`GR.pts_to ctr c0`), which is trivially satisfiable via `GR.alloc`.

2. **Postcondition precision (functional correctness)**: The postcondition states
   `result == mod_exp_spec b e m`. Combined with the normalization lemma
   `mod_exp_spec 2 10 1000 == 24`, this uniquely determines `result == 24`.

3. **Postcondition precision (bounds)**: The postcondition states
   `result >= 0 /\ result < m`. For our input, this gives `0 ≤ 24 < 1000`,
   which is verified.

4. **No admits, no assumes.**

### Spec Assessment

The ModExp specification is **precise and complete**:
- The postcondition uniquely determines the output for any valid input.
- The bounds postcondition (`0 ≤ result < m`) is correct and useful.
- The complexity bound (`cf - c0 ≤ log2f(e) + 1`) is an upper bound, not exact,
  due to leading zero bits. This is acceptable for an O(log e) algorithm.
- No issues found with the specification.
