.. _Ch31_NumberTheory:

###############################################
Number Theory: GCD & Modular Exponentiation
###############################################

This chapter covers four algorithms from CLRS Chapter 31: Euclid's
GCD algorithm (§31.2), the Extended Euclidean algorithm (§31.2),
right-to-left modular exponentiation (Exercise 31.6-2), and
left-to-right modular exponentiation (§31.6). All four are fully
verified with **zero admits, assumes, or assume_ calls**. For each
algorithm we prove:

1. Functional correctness against a pure recursive specification.
2. Key mathematical properties (Bézout's identity, divisibility).
3. The number of iterations is bounded by the claimed complexity.

GCD
===

CLRS §31.2 presents Euclid's algorithm as the foundational
number-theoretic algorithm. Our formalization provides both a pure
specification and an imperative Pulse implementation with an O(log b)
complexity proof.

Specification
~~~~~~~~~~~~~

The pure recursive specification follows the textbook definition
directly:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: gcd_spec
   :end-before: //SNIPPET_END: gcd_spec

The base case returns ``a`` when ``b = 0``; otherwise the algorithm
recurses with ``(b, a % b)``. The ``(decreases b)`` annotation proves
termination: since ``a % b < b``, the second argument strictly
decreases at each call.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The Pulse implementation iterates the same recurrence in a while loop:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: gcd_impl_sig
   :end-before: //SNIPPET_END: gcd_impl_sig

Reading this signature: given two machine-sized integers ``a_init``
and ``b_init`` with at least one positive, the function returns a
value equal to ``gcd_spec (SZ.v a_init) (SZ.v b_init)``. The ghost
counter ``ctr`` tracks the exact step count (``gcd_steps``) and
satisfies the O(log b) upper bound ``2·num_bits(b) + 1``.

Loop Invariant
~~~~~~~~~~~~~~

The while loop maintains the GCD invariant — the GCD of the current
pair equals the GCD of the original inputs:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: gcd_loop
   :end-before: //SNIPPET_END: gcd_loop

The invariant binds existential variables ``va`` and ``vb`` (the
current values of the mutable references). The key conjunct
``gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v a_init) (SZ.v b_init)``
asserts that each iteration preserves the GCD. When the loop exits
with ``vb == 0``, the definition of ``gcd_spec`` gives
``gcd_spec va 0 == va``, yielding the postcondition.

The loop body computes ``temp = a % b``, then assigns ``a := b`` and
``b := temp``. The GCD preservation follows directly from the
recursive definition: ``gcd_spec a b == gcd_spec b (a % b)``.

Complexity
~~~~~~~~~~

The complexity module proves that Euclid's algorithm takes at most
O(log b) iterations, following CLRS Theorem 31.11 (Lamé's theorem).
The cost model counts one ghost tick per mod operation.

The step count and bit-width functions:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: gcd_steps
   :end-before: //SNIPPET_END: gcd_steps

The main complexity theorem:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: lemma_gcd_steps_log
   :end-before: //SNIPPET_END: lemma_gcd_steps_log

The proof proceeds by induction with a two-step analysis. The key
lemma ``lemma_mod_le_half`` shows that ``a % b ≤ a / 2`` when
``a ≥ b > 0``. After two iterations ``(a, b) → (b, a%b) → (a%b, b%(a%b))``,
the new second argument is at most half of the original ``b``, so
``num_bits`` decreases by at least one. This gives the bound
``gcd_steps a b ≤ 2 * num_bits(b) + 1``.

The complexity-bounded predicate:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: gcd_complexity_bounded
   :end-before: //SNIPPET_END: gcd_complexity_bounded

The Pulse implementation threads a ``GhostReference.ref nat`` counter,
calling ``tick`` once per loop iteration. The loop invariant tracks
the identity ``vc - c0 + gcd_steps va vb == gcd_steps a_init b_init``:
the steps taken so far plus the steps remaining equals the total. On
exit, the logarithmic bound theorem is applied to conclude the
overall complexity.

Extended GCD
============

CLRS §31.2 also presents the Extended Euclidean algorithm, which
computes not only ``d = gcd(a, b)`` but also Bézout coefficients
``x`` and ``y`` satisfying ``a*x + b*y = d``. This is implemented as
a pure recursive function in F* (no Pulse).

Algorithm
~~~~~~~~~

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ExtendedGCD.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_gcd
   :end-before: //SNIPPET_END: extended_gcd

The algorithm follows the textbook: recursively compute
``(d', x', y')`` for ``(b, a % b)``, then set ``d = d'``,
``x = y'``, and ``y = x' - (a/b) * y'``. The base case returns
``(a, 1, 0)`` since ``a*1 + 0*0 = a``.

Bézout's Identity
~~~~~~~~~~~~~~~~~

The central theorem is that the returned coefficients satisfy
Bézout's identity:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ExtendedGCD.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: bezout_identity
   :end-before: //SNIPPET_END: bezout_identity

The proof is by induction on ``b``. The base case is immediate. For
the inductive step, the IH gives ``b * x' + (a % b) * y' == d'``.
Substituting ``a % b = a - (a/b)*b`` (via ``euclidean_division_definition``)
and rearranging yields ``a * y' + b * (x' - (a/b)*y') == d'``, which
matches the algorithm's output. The algebraic manipulations are
guided by explicit assertions that help Z3 verify each step.

Complete Specification
~~~~~~~~~~~~~~~~~~~~~~

All four properties are packaged into a single correctness theorem:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ExtendedGCD.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_gcd_correctness
   :end-before: //SNIPPET_END: extended_gcd_correctness

The theorem establishes: (1) ``d`` equals the GCD, (2) Bézout's
identity holds, (3) ``d`` divides both ``a`` and ``b``, and (4) any
common divisor of ``a`` and ``b`` divides ``d`` (maximality). Property
(4) uses the Bézout identity: if ``c | a`` and ``c | b``, then ``c``
divides any linear combination ``a*x + b*y = d``, so ``c | d``. The
divisibility lemmas come from ``FStar.Math.Euclid``.

Complexity
~~~~~~~~~~

The extended GCD has the same recursion structure as ``gcd_spec``:
both recurse on ``(b, a%b)`` with base case ``b=0``. Therefore
``gcd_steps`` counts the calls and the O(log b) bound applies:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ExtendedGCD.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_gcd_complexity
   :end-before: //SNIPPET_END: extended_gcd_complexity

Modular Exponentiation (Right-to-Left)
======================================

CLRS Exercise 31.6-2 presents right-to-left modular exponentiation
by repeated squaring, computing ``b^e mod m`` in O(log e) squarings.
Our formalization provides a pure specification and a Pulse
implementation.

Specification
~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: mod_exp_spec
   :end-before: //SNIPPET_END: mod_exp_spec

``pow`` is the standard recursive exponentiation. ``mod_exp_spec``
computes ``pow b e % m`` — the value the implementation must return.

Step Lemma
~~~~~~~~~~

The key proof obligation for each loop iteration is captured by:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: mod_exp_step
   :end-before: //SNIPPET_END: mod_exp_step

This lemma says: after one iteration (squaring the base modulo ``m``,
halving the exponent, and optionally multiplying the result by the
base), the loop invariant is preserved. It delegates to
``mod_exp_step_even`` and ``mod_exp_step_odd``, which use
``pow_mod_base`` (reducing the base modulo ``m`` does not change the
result modulo ``m``) and ``pow_even``/``pow_odd`` (splitting the
exponent).

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: mod_exp_impl_sig
   :end-before: //SNIPPET_END: mod_exp_impl_sig

The implementation takes a base, exponent, and modulus (with
``m > 1``) and returns ``mod_exp_spec b_init e_init m_init``.

Loop Invariant
~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: mod_exp_loop
   :end-before: //SNIPPET_END: mod_exp_loop

The invariant maintains ``(vr * pow vb ve) % m_init == mod_exp_spec b_init e_init m_init``.
Initially ``vr = 1``, ``vb = b_init % m_init``, and ``ve = e_init``,
so the invariant holds by ``pow_mod_base``. Each iteration calls
``mod_exp_step`` to re-establish it. The range constraints
``0 ≤ vr, vb < m_init`` ensure intermediate values stay bounded.

When the loop exits with ``ve == 0``, ``pow vb 0 == 1``, so
``vr % m_init == mod_exp_spec b_init e_init m_init``. Since
``vr < m_init``, this simplifies to ``vr == mod_exp_spec ...``.

Complexity
~~~~~~~~~~

The complexity module proves an O(log e) bound on the number of
squaring operations:

.. literalinclude:: ../autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: modexp_complexity_bounded
   :end-before: //SNIPPET_END: modexp_complexity_bounded

The bound ``log2f(e) + 1`` counts the number of times the exponent
can be halved before reaching zero. The loop invariant tracks
``(vc - c0) + log2f(ve) ≤ log2f(e_init)`` when ``ve > 0``: each
tick increases ``vc - c0`` by one while ``log2f(ve)`` decreases by
at least one (via ``lemma_log2f_halve_le``), keeping the sum bounded.

Modular Exponentiation (Left-to-Right)
======================================

CLRS §31.6 presents the primary MODULAR-EXPONENTIATION algorithm,
scanning bits from MSB to LSB (left-to-right). The algorithm maintains
``d = b^c mod m`` where ``c`` is the prefix of the binary
representation of ``e`` processed so far. At each step, square ``d``
(doubling ``c``) and optionally multiply by ``b`` (incrementing ``c``
by 1 if the current bit is 1).

The Pulse implementation is in ``ModExpLR.Impl.fst`` with complexity
bound ``num_bits(e)`` (equivalent to ⌊log₂(e)⌋ + 1). Both the
correctness and complexity are fully proven with zero admits.

Proof Techniques Summary
=========================

This chapter demonstrates several techniques:

1. **Specification-first verification**: Both GCD and modular
   exponentiation define a pure recursive spec, then prove the
   imperative loop matches it. This separates the mathematical
   argument (the spec is correct) from the systems argument (the
   implementation matches the spec).

2. **Modular arithmetic via calc**: The ``pow_mod_base`` proof uses
   F*'s ``calc`` notation to chain modular arithmetic equalities,
   applying ``lemma_mod_mul_distr_l/r`` from ``FStar.Math.Lemmas``
   at each step.

3. **Two-step induction for complexity**: The GCD complexity proof
   analyzes two iterations at a time to show the second argument
   halves, giving the O(log b) bound. This matches CLRS's proof of
   Lamé's theorem.

4. **Ghost cost counters**: As in Chapter 2, a ``GhostReference.ref nat``
   threads through the Pulse code, incremented by ``tick`` at each
   counted operation. The counter is completely erased at runtime.

5. **Pure-only proofs**: The Extended GCD is purely functional — no
   mutable state, no Pulse. This is appropriate when the algorithm
   is naturally recursive and the proof obligations are algebraic
   rather than involving heap reasoning.

Verification Status Summary
============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits / Assumes
   * - GCD.Spec
     - Pure spec
     - **0** ✅
   * - GCD.Impl
     - Pulse impl
     - **0** ✅
   * - GCD.Complexity
     - Pure proof
     - **0** ✅
   * - ExtendedGCD.Spec
     - Pure spec
     - **0** ✅
   * - ExtendedGCD.Lemmas
     - Pure proof
     - **0** ✅
   * - ExtendedGCD.Complexity
     - Pure proof
     - **0** ✅
   * - ModExp.Spec
     - Pure spec
     - **0** ✅
   * - ModExp.Impl
     - Pulse impl
     - **0** ✅
   * - ModExp.Lemmas
     - Pure proof
     - **0** ✅
   * - ModExp.Complexity
     - Pure proof
     - **0** ✅
   * - ModExpLR.Impl
     - Pulse impl
     - **0** ✅
   * - ModExpLR.Lemmas
     - Pure proof
     - **0** ✅
   * - ModExpLR.Complexity
     - Pure proof
     - **0** ✅

All four number-theoretic algorithms are fully verified with zero
admits in their implementations, specifications, and complexity
analyses ✅.
