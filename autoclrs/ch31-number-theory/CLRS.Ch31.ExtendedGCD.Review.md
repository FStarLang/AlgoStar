# Extended Euclidean Algorithm (CLRS §31.2, Alg 31.3)

## Top-Level Signature

The extended GCD is a pure function (not a Pulse implementation). The main
entry point and correctness theorem are in `CLRS.Ch31.ExtendedGCD.Lemmas.fsti`:

```fstar
val extended_gcd_correctness (a b: nat)
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd a b in
      d == gcd a b /\
      a * x + b * y == d /\
      divides d a /\ divides d b /\
      (forall (c: pos). divides c a /\ divides c b ==> divides c d)
    ))
```

### Parameters

* `a` and `b` are natural numbers (unbounded `nat`).

### Postcondition (Correctness Theorem)

The combined theorem `extended_gcd_correctness` establishes five properties of
`extended_gcd a b = (| d, x, y |)`:

* `d == gcd a b` — The returned `d` equals the Euclidean GCD.

* `a * x + b * y == d` — **Bézout's identity**: the linear combination holds.

* `divides d a /\ divides d b` — `d` divides both inputs.

* `forall (c: pos). divides c a /\ divides c b ==> divides c d` — `d` is the
  **greatest** common divisor: any common divisor of `a` and `b` divides `d`.

## Auxiliary Definitions

### `extended_gcd` (from `CLRS.Ch31.ExtendedGCD.Spec`)

```fstar
type extended_gcd_result = (_: nat & _: int & int)

let rec extended_gcd (a b: nat)
  : Tot extended_gcd_result (decreases b)
  = if b = 0 then
      (| a, 1, 0 |)
    else
      let (| d', x', y' |) = extended_gcd b (a % b) in
      let q = a / b in
      let d = d' in
      let x = y' in
      let y = x' - q * y' in
      (| d, x, y |)
```

This is a direct translation of CLRS Algorithm 31.3 (EXTENDED-EUCLID). The
coefficients `x` and `y` are integers (they can be negative). The base case
returns `(a, 1, 0)` since `a * 1 + 0 * 0 = a`.

### `gcd` (alias in `CLRS.Ch31.ExtendedGCD.Spec`)

```fstar
let gcd = gcd_spec
```

Reuses the GCD specification from `CLRS.Ch31.GCD.Spec` to avoid duplication.

### `extended_gcd_complexity_bounded` (from `CLRS.Ch31.ExtendedGCD.Complexity`)

```fstar
let extended_gcd_complexity_bounded (a b: nat) : prop =
  b > 0 ==> gcd_steps a b <= op_Multiply 2 (num_bits b) + 1
```

Reuses `gcd_steps` and `num_bits` from `CLRS.Ch31.GCD.Complexity`. Since
`extended_gcd` has the same recursion structure as `gcd_spec` (both recurse on
`(b, a % b)` with base case `b = 0`), the step count is identical.

## What Is Proven

1. **Bézout's identity** (`bezout_identity`): For all `a, b : nat`, the
   returned coefficients satisfy `a * x + b * y == d`. This is proven by
   induction on `b`, tracking the algebraic transformations through each
   recursive call.

2. **Divisibility** (`extended_gcd_divides_both`): `d | a` and `d | b`.

3. **Greatest divisor** (`extended_gcd_is_greatest`): Any positive common
   divisor `c` of `a` and `b` divides `d`. The proof uses Bézout's identity:
   if `c | a` and `c | b`, then `c | (a*x + b*y) = d`.

4. **Equivalence to GCD** (`extended_gcd_computes_gcd`): `d == gcd_spec a b`.

5. **O(log b) complexity** (`extended_gcd_complexity`): Directly delegates to
   `lemma_gcd_steps_log` since the recursion structure is identical.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Pure function only — no Pulse implementation.** Unlike GCD, there is no
   imperative (Pulse) implementation of the extended Euclidean algorithm. The
   verified artifact is a pure recursive function with lemma proofs. There is
   no ghost counter threading or mutable state.

2. ~~**Coefficients not bounded.**~~ **Resolved.** The lemma
   `extended_gcd_coeff_bounds` proves that when `a > 0` and `b > 0`,
   `|x| ≤ b/gcd(a,b)` and `|y| ≤ a/gcd(a,b)`, formalizing CLRS Theorem 31.8.

3. **No uniqueness.** The specification does not prove that the Bézout
   coefficients are unique (they are not, in general — any solution
   `(x + kb/d, y - ka/d)` also works).

4. **Example tests only.** The file includes two test cases
   (`test_extended_gcd_30_21` and `test_extended_gcd_99_78`) that verify
   specific inputs by invoking `extended_gcd_correctness`. These are
   compile-time checks, not runtime tests.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Recursive calls | O(log b) = 2·num_bits(b) + 1 | ⚠️ Reuses GCD proof | Upper bound only |

The complexity is **not directly linked** to an imperative implementation
(there is no Pulse code). Instead, `extended_gcd_complexity` observes that
`extended_gcd` has the same recursion structure as `gcd_spec`, so
`gcd_steps` counts its recursive calls, and `lemma_gcd_steps_log` provides
the O(log b) bound.

## Proof Structure

The proofs proceed by structural induction on `b` (the decreasing argument),
mirroring the recursion of `extended_gcd`. The key algebraic step for Bézout's
identity is: if `b * x' + (a % b) * y' = d`, then `a * y' + b * (x' - q * y')
= d` where `q = a / b` and `a = q * b + (a % b)`.

The greatest-divisor proof is elegant: given Bézout's identity `a*x + b*y = d`
and that `c | a` and `c | b`, it follows that `c | (a*x)`, `c | (b*y)`, hence
`c | (a*x + b*y) = d`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch31.ExtendedGCD.Spec.fst` | `extended_gcd` definition |
| `CLRS.Ch31.ExtendedGCD.Lemmas.fsti` | Lemma signatures (main interface) |
| `CLRS.Ch31.ExtendedGCD.Lemmas.fst` | Correctness proofs (Bézout, divisibility, greatest) |
| `CLRS.Ch31.ExtendedGCD.Complexity.fsti` | `extended_gcd_complexity_bounded` |
| `CLRS.Ch31.ExtendedGCD.Complexity.fst` | Delegates to `lemma_gcd_steps_log` |
| `CLRS.Ch31.GCD.Spec.fst` | `gcd_spec` (reused as `gcd`) |
| `CLRS.Ch31.GCD.Complexity.fsti` | `gcd_steps`, `num_bits` (reused) |
