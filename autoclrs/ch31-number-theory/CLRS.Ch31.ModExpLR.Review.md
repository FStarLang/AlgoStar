# Modular Exponentiation — Left-to-Right (CLRS §31.6, Alg 31.6)

## Top-Level Signature

Here is the top-level signature proven about left-to-right modular
exponentiation in `CLRS.Ch31.ModExpLR.Impl.fsti`:

```fstar
val mod_exp_lr_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt int
    (GR.pts_to ctr c0)
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      result == mod_exp_spec b_init e_init m_init /\
      modexp_lr_complexity_bounded cf (reveal c0) e_init
    ))
```

### Parameters

* `b_init` is the base (an arbitrary integer).
* `e_init` is the exponent (a natural number).
* `m_init` is the modulus (a positive integer).
* `ctr` is a **ghost counter** for tracking loop iterations.

### Preconditions

* `GR.pts_to ctr c0` — the ghost counter exists with initial value `c0`.
* No additional preconditions beyond parameter types.

### Postcondition

* `result == mod_exp_spec b_init e_init m_init` — The result equals `b^e mod m`.

* `modexp_lr_complexity_bounded cf (reveal c0) e_init` — The number of loop
  iterations is at most `num_bits(e)`.

## Auxiliary Definitions

### `mod_exp_spec` (from `CLRS.Ch31.ModExp.Spec`)

```fstar
let mod_exp_spec (b: int) (e: nat) (m: pos) : int = pow b e % m
```

Reuses the same specification as the right-to-left variant.

### `modexp_lr_complexity_bounded` (from `CLRS.Ch31.ModExpLR.Complexity`)

```fstar
let modexp_lr_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= num_bits e_init
```

### `num_bits` (from `CLRS.Ch31.GCD.Complexity`)

```fstar
let rec num_bits (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else 1 + num_bits (n / 2)
```

The number of bits in the binary representation of `n`.

## What Is Proven

1. **Functional correctness**: `result == pow b e % m`. The left-to-right
   method, scanning bits from MSB to LSB, computes the same result as the
   mathematical definition.

2. **Complexity bound**: `cf - c0 ≤ num_bits(e)`. The loop iterates once per
   bit of the exponent, from the most significant bit down to bit 0.

The loop invariant maintains `d == pow b (e / pow2(i+1)) % m`, capturing
that `d` is `b` raised to the prefix of `e`'s binary representation processed
so far.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Shares spec with right-to-left variant.** This implementation reuses
   `mod_exp_spec` from `CLRS.Ch31.ModExp.Spec`, which is the same pure
   specification. The two variants differ only in bit-scanning direction.

2. **Tighter bound than R-to-L.** The bound here is `num_bits(e)`, while the
   R-to-L variant proves `log2f(e) + 1`. For `e > 0`, `num_bits(e) ==
   log2f(e) + 1`, so they are equivalent; for `e = 0`, `num_bits(0) = 0` and
   `log2f(0) + 1 = 1`, so the L-to-R bound is tighter.

3. **Uses `pow2` from F\* stdlib.** The loop invariant references `pow2` (the
   F\* standard library power-of-two function), which is different from the
   `pow` defined in `ModExp.Spec`. The bridge between them is handled by
   lemmas in `ModExpLR.Lemmas`.

4. **No lower bound on result.** Same limitation as the R-to-L variant.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Loop iterations | O(log e) = num_bits(e) | ✅ Ghost counter | Upper bound only |

The complexity is **fully linked**: `tick ctr` is called once per iteration of
the main while loop, and the postcondition constrains `cf - c0 ≤ num_bits(e)`.
The loop counter `i` decrements from `num_bits(e) - 1` down to `-1`.

## Proof Structure

The implementation scans bits from MSB to LSB. At each step:

1. Square `d` (doubling the prefix exponent).
2. If the current bit is 1, multiply by `b` (incrementing the prefix exponent).

The loop invariant tracks `d == pow b (e / pow2(i+1)) % m` and the cost
identity `(vc - c0) + (i + 1) == num_bits(e)`.

Key lemmas from `CLRS.Ch31.ModExpLR.Lemmas`:

* `lemma_bit_decompose`: `e / pow2(i) == 2 * (e / pow2(i+1)) + (e / pow2(i)) % 2`
* `lemma_prefix_zero`: `e / pow2(num_bits(e)) == 0`
* `mod_exp_lr_step`: The algebraic step combining squaring and optional
  multiplication.

## Files

| File | Role |
|------|------|
| `CLRS.Ch31.ModExpLR.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch31.ModExpLR.Impl.fst` | Pulse implementation (left-to-right loop) |
| `CLRS.Ch31.ModExp.Spec.fst` | `pow`, `mod_exp_spec` (shared with R-to-L) |
| `CLRS.Ch31.ModExpLR.Complexity.fsti` | `modexp_lr_complexity_bounded` |
| `CLRS.Ch31.ModExpLR.Complexity.fst` | (empty — bound fully defined in interface) |
| `CLRS.Ch31.ModExpLR.Lemmas.fsti` | Lemma signatures (bit decomposition, step) |
| `CLRS.Ch31.ModExpLR.Lemmas.fst` | Proofs (bit arithmetic, LR step correctness) |
| `CLRS.Ch31.GCD.Complexity.fsti` | `num_bits` (reused) |
