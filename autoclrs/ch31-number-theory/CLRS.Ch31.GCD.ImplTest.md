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

3. **Result positivity**: The postcondition directly states `SZ.v result > 0`.
   This is verified without normalization, purely from the strengthened
   postcondition. This property is essential for callers that use the GCD
   result in division or as a modulus.

4. **Divisibility**: The postcondition directly states
   `divides (SZ.v result) (SZ.v a_init) /\ divides (SZ.v result) (SZ.v b_init)`.
   The test verifies `divides (SZ.v result) 12` and `divides (SZ.v result) 8`,
   confirming that the GCD result divides both inputs — the defining property
   of the greatest common divisor.

5. **Postcondition precision (complexity)**: The postcondition provides the exact
   step count `cf - c0 == gcd_steps a b`. By normalization, `gcd_steps 12 8 == 2`,
   confirming the complexity spec is computable on concrete inputs.

6. **No admits, no assumes.**

### Spec Assessment

The GCD specification is **precise and complete**:
- The postcondition uniquely determines the output for any valid input.
- Result positivity (`SZ.v result > 0`) is directly stated in the postcondition.
- Divisibility (`divides result a /\ divides result b`) is directly stated.
- The complexity bound includes both exact step count and O(log b) upper bound.
- No issues found with the specification.
