# GCD Spec Validation Test

## Test: `gcd(12, 8) = 4`

### Input
- `a = 12`, `b = 8`

### Expected Output
- `gcd(12, 8) = 4`

### What is Proven

1. **Precondition satisfiability**: The precondition `SZ.v a > 0 ∨ SZ.v b > 0`
   holds trivially for `(12, 8)` since `12 > 0`.

2. **Postcondition precision (functional correctness)**: The postcondition states
   `SZ.v result == gcd_spec (SZ.v a) (SZ.v b)`. Combined with the normalization
   lemma `gcd_spec 12 8 == 4`, this uniquely determines `SZ.v result == 4`.

3. **Postcondition precision (complexity)**: The postcondition provides the exact
   step count `cf - c0 == gcd_steps a b`. By normalization, `gcd_steps 12 8 == 2`,
   confirming the complexity spec is computable on concrete inputs.

4. **No admits, no assumes.**

### Spec Assessment

The GCD specification is **precise and complete**:
- The postcondition uniquely determines the output for any valid input.
- The complexity bound includes both exact step count and O(log b) upper bound.
- No issues found with the specification.
