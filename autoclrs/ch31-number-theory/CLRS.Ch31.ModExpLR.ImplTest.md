# ModExpLR (L-to-R) Spec Validation Test

## Test: `3^5 mod 7 = 5`

### Input
- `b = 3`, `e = 5`, `m = 7`

### Expected Output
- `pow(3, 5) mod 7 = 243 mod 7 = 5`

### What is Proven

1. **Precondition satisfiability**: The only precondition is the ghost counter
   (`GR.pts_to ctr c0`), which is trivially satisfiable via `GR.alloc`.

2. **Postcondition precision (functional correctness)**: The postcondition states
   `result == mod_exp_spec b e m`. Combined with the normalization lemma
   `mod_exp_spec 3 5 7 == 5`, this uniquely determines `result == 5`.

3. **Postcondition precision (bounds)**: The postcondition states
   `result >= 0 /\ result < m`. For our input, this gives `0 ≤ 5 < 7`,
   which is verified.

4. **No admits, no assumes.**

### Spec Assessment

The ModExpLR specification is **precise and complete**:
- The postcondition uniquely determines the output for any valid input.
- The bounds postcondition (`0 ≤ result < m`) is correct and useful.
- The complexity bound (`cf - c0 ≤ num_bits(e)`) is a tight upper bound.
- No issues found with the specification.
