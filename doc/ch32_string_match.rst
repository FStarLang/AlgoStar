.. _Ch32_StringMatch:

########################################
String Matching
########################################

This chapter covers the string-matching algorithms from CLRS
Chapter 32: the naive algorithm (§32.1), Rabin-Karp (§32.2), and
the Knuth-Morris-Pratt algorithm (§32.4). Each algorithm is
implemented in Pulse and verified against a common specification:
count the number of positions where a pattern matches the text.

All three algorithms are **fully verified with 0 admits** in
their implementations, specifications, and complexity analyses ✅.

Naive String Matching
=====================

CLRS §32.1 presents the brute-force approach: slide the pattern
across the text, checking every position. Our formalization proves
functional correctness and the O((n−m+1)·m) complexity bound,
both with **0 admits**.

Specification
~~~~~~~~~~~~~

The core predicate defines when a pattern matches at a given offset:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.NaiveStringMatch.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: matches_at_spec
   :end-before: //SNIPPET_END: matches_at_spec

``matches_at text pattern s`` holds when the pattern aligns with
the text starting at position *s* — every character in the pattern
equals the corresponding text character.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation follows the CLRS pseudocode directly:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.NaiveStringMatch.fst
   :language: pulse
   :start-after: //SNIPPET_START: naive_string_match_sig
   :end-before: //SNIPPET_END: naive_string_match_sig

The postcondition guarantees that the returned count equals
``count_matches_up_to``, a pure function that counts the number of
valid shifts where the pattern matches. The implementation has
**0 admits and 0 assume_ calls**.

Note: There is no separate ``Impl.fsti`` — the function is defined
directly in ``NaiveStringMatch.fst``.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postcondition provides the exact match count (not just
"found a match"), which is the strongest possible guarantee
for a counting algorithm. The complexity bound ``(n-m+1)·m``
is tight: it counts one ghost tick per character comparison.

Complexity
~~~~~~~~~~

The complexity bound is defined in a pure F* module:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.NaiveStringMatch.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound_naive
   :end-before: //SNIPPET_END: complexity_bound_naive

This captures the worst-case bound: the total number of character
comparisons is at most (n−m+1)·m. The complexity module has
**0 admits**.

Rabin-Karp
==========

CLRS §32.2 presents Rabin-Karp, which uses a rolling hash to
filter candidate positions before performing character-by-character
verification. Our formalization covers the hash function, rolling
update, and the matching algorithm in both pure F* and Pulse.

Hash Specification
~~~~~~~~~~~~~~~~~~

The hash function follows CLRS §32.2: a big-endian polynomial hash
where the leftmost character gets the highest power of the radix.
The rolling hash step computes the next window's hash from the
previous one in O(1):

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: hash
   :end-before: //SNIPPET_END: hash

The key proof insight, adapted from
``FStar/examples/algorithms/StringMatching.fst``, is the
``hash_inversion`` lemma which extracts the most-significant digit
(leftmost character) from the hash. This enables proving
``rolling_hash_step_correct`` (that the imperative rolling hash
step produces the correct hash for the next window) and
``hash_slice_lemma`` (that equal substrings produce equal hashes,
for the no-false-negatives direction):

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: rolling_hash_step_correct
   :end-before: //SNIPPET_END: rolling_hash_step_correct

Pure Algorithm
~~~~~~~~~~~~~~

The pure Rabin-Karp implementation scans the text with a rolling hash,
verifying character-by-character on hash matches:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: rabin_karp
   :end-before: //SNIPPET_END: rabin_karp

Correctness
~~~~~~~~~~~

The main correctness theorem combines no-false-positives (every
returned position is a valid match) and no-false-negatives (every
valid match is returned):

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: correctness
   :end-before: //SNIPPET_END: correctness

The specification module has **0 admits and 0 assumes**.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation follows the CLRS pseudocode: compute the
pattern hash and the initial text-window hash, then slide the
window across the text, using the rolling hash to update and
verifying character-by-character on hash matches:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.fst
   :language: pulse
   :start-after: //SNIPPET_START: rabin_karp_sig
   :end-before: //SNIPPET_END: rabin_karp_sig

The postcondition guarantees the same ``count_matches_up_to``
property as the naive algorithm. The implementation module
(``RabinKarp``) has **0 admits and 0 assume_ calls**.

Complexity
~~~~~~~~~~

The complexity analysis distinguishes best and worst cases:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: rk_complexity
   :end-before: //SNIPPET_END: rk_complexity

The best case is O(n+m) when no spurious hash matches occur. The
worst case is O(nm) when all hash values collide. Both bounds are
proven; the expected-case analysis (O(n+m) depending on hash quality
and prime choice) is not formalized. The complexity module has
**0 admits**.

Limitations
~~~~~~~~~~~

- **Pure implementation**: The core Rabin-Karp specification and
  correctness proofs are in pure F*, not Pulse.
- **Expected-case not formalized**: Only the worst-case O(nm) bound
  is formally proven. The expected O(n+m) depends on hash quality.

Knuth-Morris-Pratt
==================

CLRS §32.4 presents KMP as a linear-time string-matching algorithm
that avoids redundant comparisons by precomputing a *prefix
function*. Our formalization verifies both the prefix-function
computation and the matcher, with 0 admits in the implementations.
The amortized complexity analysis is also **fully verified with 0
admits**.

Prefix Function Specification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The prefix function π captures the longest proper prefix of the
pattern that is also a suffix at each position:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.PureDefs.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_prefix_suffix
   :end-before: //SNIPPET_END: is_prefix_suffix

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.PureDefs.fst
   :language: fstar
   :start-after: //SNIPPET_START: pi_correct
   :end-before: //SNIPPET_END: pi_correct

``pi_correct pattern pi`` asserts that for every position *q* in
the pattern, ``pi[q]`` gives a valid prefix-suffix length — the
prefix of length ``pi[q]`` matches the suffix ending at position
*q*. Maximality (``pi[q]`` is the *longest* such prefix-suffix)
is proven separately in ``Bridge.pi_max_sz``.

Prefix Function Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation computes the prefix function following
CLRS Compute-Prefix-Function:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: pulse
   :start-after: //SNIPPET_START: compute_prefix_function_sig
   :end-before: //SNIPPET_END: compute_prefix_function_sig

The postcondition guarantees that the output satisfies both
``pi_correct`` (validity) and ``Bridge.pi_max_sz`` (maximality).
The implementation has **0 admits**.

KMP Matcher
~~~~~~~~~~~

The matcher uses the precomputed prefix function to avoid
backtracking in the text:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: pulse
   :start-after: //SNIPPET_START: kmp_matcher_sig
   :end-before: //SNIPPET_END: kmp_matcher_sig

The postcondition guarantees the returned count equals
``Spec.count_matches_spec``, with the matcher complexity bound
``cf - c0 ≤ 2·n``. The implementation has **0 admits and 0
assume_ calls**.

Completeness is proven via the bridge from the Pulse
``pi_correct``/``pi_max_sz`` to the pure specification's
``Spec.pi_max``, and through ``Spec.kmp_count_step`` which
shows each KMP step correctly updates the match count.

Complexity
~~~~~~~~~~

The amortized complexity analysis proves the O(n+m) bound:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.PureDefs.fst
   :language: fstar
   :start-after: //SNIPPET_START: kmp_total_complexity
   :end-before: //SNIPPET_END: kmp_total_complexity

The bound states that the total number of character comparisons
across both the prefix-function computation and the matching phase
is at most 2n + 2m. This is an **exact** bound, not just asymptotic.

The proof follows the standard amortized argument with potential
functions:

- **Prefix computation**: potential Φ = k (current match length).
  Each comparison either advances ``q`` (potential unchanged, no
  tick) or decreases ``k`` (tick +1, potential −1, net ≤ 0).
  Bound: ``vc - c0 + k ≤ 2·(q - 1)``.

- **Matching**: potential Φ = q (current match position in pattern).
  Each comparison either advances the text pointer (potential
  unchanged or increases by 1) or decreases the match length
  (tick +1, potential decrease ≥ 1, net ≤ 0).
  Bound: ``vc - c0 + q ≤ 2·i``.

The complexity module is **fully verified with 0 admits** ✅.

Verification Status Summary
============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits / Assumes
   * - NaiveStringMatch
     - Pulse impl
     - **0** ✅
   * - NaiveStringMatch.Spec
     - Pure spec
     - **0** ✅
   * - NaiveStringMatch.Lemmas
     - Pure proof
     - **0** ✅
   * - NaiveStringMatch.Complexity
     - Pure proof
     - **0** ✅
   * - RabinKarp.Spec
     - Pure spec + proofs
     - **0** ✅
   * - RabinKarp.Lemmas
     - Pure proof
     - **0** ✅
   * - RabinKarp
     - Pulse impl
     - **0** ✅
   * - RabinKarp.Complexity
     - Pure proof
     - **0** ✅
   * - KMP.PureDefs
     - Pure spec
     - **0** ✅
   * - KMP.Spec
     - Pure completeness
     - **0** ✅
   * - KMP.Bridge
     - Bridging lemmas
     - **0** ✅
   * - KMP
     - Pulse impl
     - **0** ✅
   * - KMP.Test
     - Test
     - **0** ✅

All three string-matching implementations (naive, Rabin-Karp, KMP)
are fully verified with 0 admits in their Pulse code, specifications,
and complexity analyses ✅.
