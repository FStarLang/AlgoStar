# Audit Report: Chapter 31 — Number-Theoretic Algorithms

**Scope:** `CLRS.Ch31.GCD.fst`, `CLRS.Ch31.ExtendedGCD.fst`, `CLRS.Ch31.ModExp.fst`
**Lines audited:** 586 (198 + 172 + 216)
**Verification status:** All 3 files have `.checked` caches — fully verified, zero admits.

---

## 1. CLRS Fidelity

### 1.1 EUCLID (CLRS p. 935) → `CLRS.Ch31.GCD.fst`

**CLRS pseudocode:**
```
EUCLID(a, b)
1  if b == 0
2    return a
3  else return EUCLID(b, a mod b)
```

**Implementation:** The pure spec `gcd_spec` (line 40–41) is a *verbatim* translation
of the recursive pseudocode. The Pulse implementation `gcd_impl` (lines 149–198)
converts the tail-recursive algorithm into an iterative while-loop, which is the
standard transformation. The loop invariant (lines 166–175) preserves
`gcd_spec(va, vb) == gcd_spec(a_init, b_init)` — exactly the CLRS recursion
theorem (Theorem 31.9).

**Verdict: Faithful.** Iterative ≡ tail-recursive; spec is line-for-line CLRS.

### 1.2 EXTENDED-EUCLID (CLRS p. 937) → `CLRS.Ch31.ExtendedGCD.fst`

**CLRS pseudocode:**
```
EXTENDED-EUCLID(a, b)
1  if b == 0
2    return (a, 1, 0)
3  else (d', x', y') = EXTENDED-EUCLID(b, a mod b)
4    (d, x, y) = (d', y', x' − ⌊a/b⌋ · y')
5    return (d, x, y)
```

**Implementation:** `extended_gcd` (lines 34–44) is a *verbatim* recursive
translation. The base case returns `(| a, 1, 0 |)` (line 37), matching CLRS line 2.
The recursive case computes `x = y'` and `y = x' − q * y'` (lines 42–43), matching
CLRS line 4 exactly.

**Verdict: Exact match.**

### 1.3 MODULAR-EXPONENTIATION (CLRS p. 957) → `CLRS.Ch31.ModExp.fst`

**CLRS pseudocode** scans bits **left-to-right** (MSB → LSB):
```
MODULAR-EXPONENTIATION(a, b, n)
1  c = 0; d = 1
2  let ⟨b_k, ..., b_0⟩ be binary representation of b
3  for i = k downto 0
4    c = 2c; d = (d · d) mod n
5    if b_i == 1: c = c+1; d = (d · a) mod n
6  return d
```

**Implementation:** `mod_exp_impl` (lines 156–215) scans bits **right-to-left**
(LSB → MSB) using `e / 2` and `e % 2`. This is the variant from **CLRS Exercise
31.6-2**, not the textbook's primary algorithm. Both compute `b^e mod m` correctly,
but the control flow differs: the implementation maintains a running `result`
accumulator and a squaring `base`, rather than CLRS's prefix-value `c` and
repeated-squaring `d`.

**Verdict: Correct variant (Exercise 31.6-2), not the primary CLRS algorithm.**
The header comment (line 4) says "Implements MODULAR-EXPONENTIATION from
CLRS Chapter 31" without noting the right-to-left variant.

---

## 2. Specification Strength

| Property | GCD | Extended GCD | ModExp |
|----------|-----|-------------|--------|
| Functional correctness | ✅ `result == gcd_spec(a,b)` | ✅ `d == gcd(a,b)` | ✅ `result == pow b e % m` |
| Bézout's identity | — | ✅ `a*x + b*y == d` | — |
| Divisibility | — | ✅ `divides d a ∧ divides d b` | — |
| Greatest-divisor | — | ✅ `∀c. divides c a ∧ divides c b ⟹ divides c d` | — |
| Complexity bound | ✅ O(log b) | ❌ none | ✅ O(log e) |
| Concrete test cases | — | ✅ two examples (30,21) and (99,78) | — |

### Observations

- **GCD spec is purely syntactic.** `gcd_spec` is proven equal to the algorithm
  output but is not itself connected to the divisibility notion (`divides` from
  `FStar.Math.Euclid`). The *Extended GCD* module independently proves the
  mathematical GCD properties, but `CLRS.Ch31.GCD` does not import or refer to
  those results. A user of `gcd_impl` only learns the output matches the recursive
  definition, not that it divides both inputs.

- **Extended GCD specification is exemplary.** All four properties (gcd value,
  Bézout's identity, divisibility, greatest-divisor) are packaged into
  `extended_gcd_correctness` (lines 133–154). This is the strongest specification
  in the chapter.

- **ModExp specification is complete.** `mod_exp_spec b e m = pow b e % m` is
  the standard mathematical definition. The pure `pow` function and its algebraic
  lemmas (`pow_add`, `pow_pow`, `pow_square`, `pow_even`, `pow_odd`,
  `pow_mod_base`) form a solid algebraic foundation.

- **ModExp preconditions are slightly restrictive.** The Pulse function requires
  `m_init > 1 ∧ e_init > 0` (line 158). CLRS handles `b = 0` (returns 1) and
  `n = 1` (returns 0). These are trivial edge cases but worth noting.

---

## 3. Complexity Analysis

### GCD — O(log b)

The bound is `gcd_steps(a, b) ≤ 2 · num_bits(b) + 1` (line 118), where
`num_bits(n) = 1 + ⌊log₂ n⌋` for n > 0. This gives an upper bound of
`2·⌊log₂ b⌋ + 3` steps, which is **O(log b)** = O(log min(a,b)) since
`gcd_spec_comm` proves commutativity.

The approach differs from CLRS's Fibonacci-based Lamé's theorem
(Theorem 31.11) but captures the same asymptotic bound via a direct mod-halving
argument: `a % b ≤ a/2` (line 92) so the remainder halves every two steps.
This is clean and arguably simpler than the Fibonacci route.

The complexity predicate `gcd_complexity_bounded` (lines 138–142) packages
`cf − c0 == gcd_steps(a_init, b_init)` and the log bound, tracked via ghost ticks.

### ModExp — O(log e)

The bound is `cf − c0 ≤ log2f(e_init) + 1` (line 149), i.e., at most
⌊log₂ e⌋ + 1 iterations. This is tight — exactly the number of bits in `e`.
The `log2f` function (lines 131–133) and halving lemma (lines 135–144) are
straightforward.

### Extended GCD — No complexity proof

No step counter or complexity analysis. Since the algorithm is pure F*
(not Pulse), there is no ghost tick infrastructure. The complexity would be
identical to GCD (same recursion structure).

---

## 4. Code Quality

### Structure and Organization

All three files follow a clean pattern:
1. Ghost tick infrastructure (Pulse files)
2. Pure specification
3. Algebraic lemmas
4. Pulse/F* implementation
5. (GCD/ModExp) Complexity analysis integrated into the implementation

### Language Choice

| File | Language | Rationale |
|------|----------|-----------|
| GCD | Pulse | Imperative loop with mutable state, ghost ticks |
| ExtendedGCD | Pure F* | Recursive, no mutation needed |
| ModExp | Pulse | Imperative loop with mutable state, ghost ticks |

The choice is appropriate: Extended GCD is naturally recursive and returns a
triple, making pure F* the right fit. GCD and ModExp use mutable variables
and benefit from Pulse's separation logic.

### Solver Settings

| File | Location | Settings |
|------|----------|----------|
| GCD | Line 91 | `--z3rlimit 20` (for `lemma_mod_le_half`) |
| GCD | Line 115 | `--z3rlimit 150 --fuel 3 --ifuel 2` (for `lemma_gcd_steps_log`) |
| GCD | Line 146 | `--z3rlimit 10` (for Pulse impl) |
| ModExp | Line 96 | `--z3rlimit 20` (for step lemmas) |
| ModExp | Line 154 | `--z3rlimit 20` (for Pulse impl) |
| ExtendedGCD | — | Default settings throughout |

The `z3rlimit 150` with `fuel 3` for `lemma_gcd_steps_log` is the highest
resource usage. This is acceptable for an inductive complexity proof with
two levels of unfolding. All other limits are modest (10–20).

### Minor Issues

- **Duplicated `gcd` definition.** `gcd_spec` in `CLRS.Ch31.GCD.fst` (line 40)
  and `gcd` in `CLRS.Ch31.ExtendedGCD.fst` (line 24) are identical functions
  with different names. No cross-module dependency exists.

- **Duplicated `incr_nat` / `tick`.** Both `GCD.fst` (lines 26–34) and
  `ModExp.fst` (lines 23–31) define identical ghost tick infrastructure.
  This should be in a shared `common/` module.

- **SizeT vs int domains.** GCD uses `FStar.SizeT` (bounded machine integers);
  ModExp uses unbounded `int`. This means GCD has an implicit overflow
  guard (SizeT fits in machine word) while ModExp operates on mathematical
  integers only.

---

## 5. Proof Quality — Admits and Assumes

### Admits: **0** (zero)
### Assumes: **0** (zero)

All three files are fully verified with no proof holes. This is confirmed by:
1. `grep -c "admit\|assume" *.fst` returns 0 (excluding comments)
2. All `.checked` files present in `_cache/`
3. Header comments accurately state "NO admits. NO assumes."

### Proof Techniques

| Technique | Where Used |
|-----------|-----------|
| Structural induction on `b` | `gcd_spec_comm`, `extended_gcd_*`, `bezout_identity`, `lemma_gcd_steps_log` |
| `calc` proof blocks | `pow_mod_base` (ModExp line 79–91) |
| Ghost reference ticks | GCD loop (line 187), ModExp loop (line 197) |
| `FStar.Math.Euclid` library | ExtendedGCD (`divides_*`, `euclidean_division_definition`) |
| `FStar.Math.Lemmas` library | ModExp (`lemma_mod_mul_distr_l/r`) |
| `FStar.Classical.forall_intro` | ExtendedGCD `extended_gcd_correctness` (line 154) |

The proofs are clean, well-structured, and rely on standard library lemmas
rather than heavy automation. The `calc` block in `pow_mod_base` is
particularly readable.

---

## 6. Documentation Accuracy

| Claim | Location | Accurate? |
|-------|----------|-----------|
| "Implements the classic recursive GCD algorithm iteratively" | GCD header | ✅ |
| "gcd(a, b) = gcd(b, a mod b) with base case gcd(a, 0) = a" | GCD header | ✅ |
| "Proves both functional correctness and O(log b) complexity" | GCD header | ✅ |
| "Complexity analysis uses Lamé's theorem (CLRS Theorem 31.11)" | GCD line 8 | ⚠️ Indirect — uses mod-halving, not Fibonacci numbers |
| "NO admits. NO assumes." | All 3 headers | ✅ Verified |
| "Implements EXTENDED-EUCLID algorithm" | ExtendedGCD header | ✅ |
| "a*x + b*y = d (Bézout's identity)" | ExtendedGCD header | ✅ |
| "Implements MODULAR-EXPONENTIATION from CLRS Chapter 31" | ModExp header | ⚠️ Right-to-left variant, not the primary CLRS algorithm |
| "at most ⌊log₂(e)⌋ + 1 squarings" | ModExp header | ✅ |
| README: "GCD, Modular Exponentiation" for ch31 | README.md | ⚠️ Omits Extended GCD |

---

## 7. Task List

### Priority 1 — Correctness / Fidelity

| # | Task | File | Effort |
|---|------|------|--------|
| 1.1 | **Document ModExp variant.** Add a comment noting this is the right-to-left (Exercise 31.6-2) variant, not the primary left-to-right CLRS algorithm. | `ModExp.fst` line 4 | Trivial |
| 1.2 | **Link GCD spec to divisibility.** Add a lemma `gcd_spec_divides: a:nat → b:nat → Lemma (divides (gcd_spec a b) a ∧ divides (gcd_spec a b) b)` to connect `gcd_spec` to the mathematical GCD definition, or import the result from `ExtendedGCD`. | `GCD.fst` | Small |

### Priority 2 — Completeness

| # | Task | File | Effort |
|---|------|------|--------|
| 2.1 | **Add complexity proof for Extended GCD.** The recursion is identical to GCD; the step count and O(log b) bound carry over directly. Could be a Pulse wrapper or a pure step-counting function. | `ExtendedGCD.fst` | Medium |
| 2.2 | **Handle edge cases in ModExp.** Relax preconditions to allow `e_init = 0` (return 1 % m) and `m_init = 1` (return 0), matching CLRS fully. | `ModExp.fst` line 158 | Small |
| 2.3 | **Update README** to list Extended GCD in the ch31 row. | `README.md` | Trivial |

### Priority 3 — Code Quality

| # | Task | File | Effort |
|---|------|------|--------|
| 3.1 | **Factor out ghost tick infrastructure** (`incr_nat`, `tick`) into a shared module (e.g., `common/GhostTick.fst`) to eliminate duplication across GCD, ModExp, and other chapters. | `common/` | Small |
| 3.2 | **Unify GCD definitions.** Either have `ExtendedGCD.fst` import `gcd_spec` from `GCD.fst`, or create a shared `GCD.Spec` module. The two identical definitions (`gcd_spec` and `gcd`) should not coexist independently. | Both GCD files | Small |
| 3.3 | **Fix Lamé's theorem documentation.** Line 8 of GCD says "Complexity analysis uses Lamé's theorem" but the proof uses a direct mod-halving argument, not the Fibonacci-based Lamé bound. Either clarify the comment or add the Fibonacci connection. | `GCD.fst` line 8 | Trivial |

### Priority 4 — Enhancements (Optional)

| # | Task | File | Effort |
|---|------|------|--------|
| 4.1 | **Add left-to-right ModExp** implementing the primary CLRS algorithm for completeness, keeping the current right-to-left version as an alternative. | New file | Medium |
| 4.2 | **Add concrete test cases for GCD and ModExp** (like the CLRS examples: `gcd(30,21)=3`, `7^560 mod 561 = 1`). ExtendedGCD already has tests. | `GCD.fst`, `ModExp.fst` | Trivial |
| 4.3 | **Prove GCD commutativity implies O(log min(a,b)).** The current bound is O(log b); combining with `gcd_spec_comm` gives O(log min(a,b)), but this isn't stated as a standalone lemma. | `GCD.fst` | Trivial |

---

## Summary

Chapter 31 is one of the strongest chapters in AutoCLRS. All three files are
**fully verified with zero admits**, the specifications are mathematically
meaningful, and complexity proofs accompany 2 of 3 algorithms. The Extended GCD
module is exemplary — it proves all four GCD properties plus Bézout's identity
with clean, readable proofs.

The main gaps are:
1. ModExp implements the right-to-left variant (CLRS Exercise 31.6-2) but
   documents it as the primary algorithm.
2. The GCD module's spec is purely syntactic (no divisibility link).
3. Extended GCD lacks a complexity proof.
4. Ghost tick infrastructure and GCD definitions are duplicated.

None of these are soundness issues — the verified properties are all correct.
