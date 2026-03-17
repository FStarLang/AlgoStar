# GCD — Euclid's Algorithm (CLRS §31.2, Alg 31.2)

## Top-Level Signature

Here is the top-level signature proven about GCD in
`CLRS.Ch31.GCD.Impl.fsti`:

```fstar
val gcd_impl (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt SZ.t
    (GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0))
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
      cf >= reveal c0 /\
      cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init) /\
      (SZ.v b_init > 0 ==> cf - reveal c0 <= op_Multiply 2 (num_bits (SZ.v b_init)) + 1)
    ))
```

### Parameters

* `a_init` and `b_init` are machine-sized unsigned integers (`SZ.t`),
  representing the two inputs to Euclid's algorithm.

* `ctr` is a **ghost counter** — a ghost reference to a natural number used to
  count loop iterations. The initial value is `c0`. Ghost values are erased at
  runtime; they exist only for specification and proof.

### Preconditions

* `SZ.v a_init > 0 \/ SZ.v b_init > 0`: At least one input must be positive
  (gcd(0, 0) is undefined).

### Postcondition

The `ensures` clause states that there exists a final counter value `cf` such
that:

* `SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init)` — The result equals
  the pure recursive GCD specification.

* `cf >= reveal c0` — The counter is non-decreasing.

* `cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init)` — The counter
  tracks the **exact** number of Euclidean steps.

* `SZ.v b_init > 0 ==> cf - reveal c0 <= 2 * num_bits(b_init) + 1` — When
  `b > 0`, the step count is bounded by O(log b).

## Auxiliary Definitions

### `gcd_spec` (from `CLRS.Ch31.GCD.Spec`)

```fstar
let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)
```

The standard Euclidean algorithm as a pure recursive function. Base case:
gcd(a, 0) = a. Recursive case: gcd(a, b) = gcd(b, a mod b).

### `gcd_steps` (from `CLRS.Ch31.GCD.Complexity`)

```fstar
let rec gcd_steps (a b: nat) : Tot nat (decreases b) =
  if b = 0 then 0
  else 1 + gcd_steps b (a % b)
```

Counts the exact number of recursive calls (loop iterations) in Euclid's
algorithm. Structurally mirrors `gcd_spec`.

### `num_bits` (from `CLRS.Ch31.GCD.Complexity`)

```fstar
let rec num_bits (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else 1 + num_bits (n / 2)
```

The number of bits needed to represent `n` (i.e., ⌊log₂(n)⌋ + 1 for n > 0,
and 0 for n = 0).

### `gcd_complexity_bounded` (from `CLRS.Ch31.GCD.Complexity`)

```fstar
let gcd_complexity_bounded (cf c0: nat) (a_init b_init: nat) : prop =
  cf >= c0 /\
  cf - c0 == gcd_steps a_init b_init /\
  (b_init > 0 ==> cf - c0 <= op_Multiply 2 (num_bits b_init) + 1)
```

Combines the exact step count with the O(log b) upper bound.

## What Is Proven

The postcondition establishes:

1. **Functional correctness**: `result == gcd_spec a b`. The imperative loop
   computes the same value as the pure recursive specification.

2. **Exact step count**: `cf - c0 == gcd_steps a b`. The ghost counter tracks
   the precise number of Euclidean steps — not just an upper bound.

3. **O(log b) complexity**: When `b > 0`, the step count satisfies
   `gcd_steps a b ≤ 2 * num_bits(b) + 1`. This captures the same O(log b)
   bound as CLRS Theorem 31.11 (Lamé's theorem). The proof uses the
   mod-halving argument: `a % b ≤ a / 2` when `a ≥ b`, so every two steps
   halve the larger argument.

4. **Divisibility**: A separate lemma `gcd_spec_divides` in
   `CLRS.Ch31.GCD.Lemmas` proves that `gcd_spec a b` divides both `a` and `b`.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**No "greatest" property.**~~ **Resolved.** The lemma `gcd_spec_is_greatest`
   in `CLRS.Ch31.GCD.Lemmas` proves that any positive common divisor of `a` and
   `b` divides `gcd_spec a b`, establishing that it is the *greatest* common
   divisor. The proof delegates to Bézout's identity from the Extended GCD module.

2. **Precondition excludes gcd(0, 0).** The precondition requires
   `a > 0 ∨ b > 0`. Mathematically gcd(0, 0) = 0, but the implementation
   does not handle this degenerate case.

3. **Machine-size limitation.** Inputs are `SZ.t` (machine-sized), so the
   implementation cannot handle arbitrarily large integers. The pure
   specification works over unbounded `nat`.

4. **Commutativity proven separately.** `gcd_spec_comm` proves
   `gcd_spec a b == gcd_spec b a`, but the `O(log min(a,b))` bound
   (`gcd_steps_log_min`) requires both inputs to be positive.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Loop iterations | O(log b) = 2·num_bits(b) + 1 | ✅ Ghost counter | Exact count + upper bound |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented by `tick ctr` inside the while loop of the Pulse
code, and the postcondition directly constrains `cf - c0`. The exact count
`gcd_steps a b` is an equality, not just an upper bound. The O(log b) bound is
additionally proven as an inequality.

## Proof Structure

The Pulse implementation uses a while loop with mutable variables `a` and `b`.
The loop invariant maintains:

* `gcd_spec(a, b) == gcd_spec(a_init, b_init)` — the GCD is preserved.
* `vc - c0 + gcd_steps(a, b) == gcd_steps(a_init, b_init)` — the counter plus
  remaining steps equals the total.

The O(log b) bound is proven in `CLRS.Ch31.GCD.Complexity` using a direct
mod-halving argument: since `a % b ≤ a / 2` when `a ≥ b`, every two Euclidean
steps reduce `b` by at least one bit.

## Checklist

- [x] Zero admits, zero assumes
- [x] Functional correctness: `result == gcd_spec(a, b)`
- [x] Exact step count: `cf - c0 == gcd_steps(a, b)`
- [x] O(log b) complexity bound (Lamé's theorem)
- [x] Divisibility: `gcd_spec a b` divides both `a` and `b`
- [x] Greatest-divisor property (via Bézout's identity from ExtendedGCD)
- [x] Commutativity: `gcd_spec a b == gcd_spec b a`
- [x] O(log min(a,b)) bound (`gcd_steps_log_min`)
- [x] Rubric compliance: Spec, Lemmas, Complexity, Impl all present
- [x] Proof stability: max z3rlimit 20 (reduced from 150)
- [ ] Handle `gcd(0, 0)` degenerate case (currently excluded by precondition)
- [ ] Best-case complexity (lower bound on step count)
- [x] Spec validation test (`CLRS.Ch31.GCD.ImplTest.fst`)

## Spec Validation (ImplTest)

**Test:** `gcd(12, 8) = 4` — see `CLRS.Ch31.GCD.ImplTest.fst` and
`CLRS.Ch31.GCD.ImplTest.md` for details.

**Results:**
- ✅ Precondition `SZ.v a > 0 ∨ SZ.v b > 0` is satisfiable for (12, 8).
- ✅ Postcondition uniquely determines result: `gcd_spec 12 8 == 4` by
  normalization, proving `SZ.v result == 4`.
- ✅ Complexity spec `gcd_steps 12 8 == 2` is computable by normalization.
- ✅ No admits, no assumes in the test.

**Spec issues found:** None. The specification is precise and complete.
