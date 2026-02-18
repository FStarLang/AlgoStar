.. _Ch32_StringMatch:

########################################
String Matching
########################################

This chapter covers the string-matching algorithms from CLRS
Chapter 32: the naive algorithm (§32.1), Rabin-Karp (§32.2), and
the Knuth-Morris-Pratt algorithm (§32.4). Each algorithm is
implemented in Pulse and verified against a common specification:
count the number of positions where a pattern matches the text.

The naive algorithm and Rabin-Karp are **fully verified with 0
admits** in both their implementations and specifications. KMP is
also fully verified at the implementation level (0 admits); its
amortized complexity analysis has 7 admits.

Naive String Matching
=====================

CLRS §32.1 presents the brute-force approach: slide the pattern
across the text, checking every position. Our formalization proves
functional correctness and the O((n−m+1)·m) complexity bound,
both with **0 admits**.

Specification
~~~~~~~~~~~~~

The core predicate defines when a pattern matches at a given offset:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.NaiveStringMatch.fst
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

Complexity
~~~~~~~~~~

The complexity bound is proved in a pure F* module:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.NaiveStringMatch.Complexity.fst
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
update, and the matching algorithm.

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
from the hash.  This enables proving ``rolling_hash_step_correct``
(that the imperative rolling hash step produces the correct hash
for the next window) and ``hash_slice_lemma`` (that equal
substrings produce equal hashes, for the no-false-negatives
direction):

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: rolling_hash_step_correct
   :end-before: //SNIPPET_END: rolling_hash_step_correct

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

The complexity analysis is done in a pure F* module:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.RabinKarp.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: rk_complexity
   :end-before: //SNIPPET_END: rk_complexity

The best case is O(n+m) when no spurious hash matches occur. The
worst case is O(nm) when all hash values collide. The complexity
module has **0 admits**.

Knuth-Morris-Pratt
==================

CLRS §32.4 presents KMP as a linear-time string-matching algorithm
that avoids redundant comparisons by precomputing a *prefix
function*. Our formalization verifies both the prefix-function
computation and the matcher, with 0 admits in the implementations.
The amortized complexity analysis has 7 admits.

Prefix Function Specification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The prefix function π captures the longest proper prefix of the
pattern that is also a suffix at each position:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_prefix_suffix
   :end-before: //SNIPPET_END: is_prefix_suffix

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: fstar
   :start-after: //SNIPPET_START: pi_correct
   :end-before: //SNIPPET_END: pi_correct

``pi_correct pattern pi`` asserts that for every position *q* in
the pattern, ``pi[q]`` gives a valid prefix-suffix length — the
prefix of length ``pi[q]`` matches the suffix ending at position
*q*.

Prefix Function Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation computes the prefix function following
CLRS Compute-Prefix-Function:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: pulse
   :start-after: //SNIPPET_START: compute_prefix_function_sig
   :end-before: //SNIPPET_END: compute_prefix_function_sig

The postcondition guarantees that the output satisfies
``pi_correct``. The implementation has **0 admits**.

KMP Matcher
~~~~~~~~~~~

The matcher uses the precomputed prefix function to avoid
backtracking in the text:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.fst
   :language: pulse
   :start-after: //SNIPPET_START: kmp_matcher_sig
   :end-before: //SNIPPET_END: kmp_matcher_sig

The implementation has **0 admits and 0 assume_ calls**.

A separate module (``KMP.StrengthenedSpec``) provides a
strengthened postcondition specification connecting the matcher
result to the ``matches_at`` predicate, also with **0 admits**.

Complexity
~~~~~~~~~~

The amortized complexity analysis proves the O(n+m) bound:

.. literalinclude:: ../ch32-string-matching/CLRS.Ch32.KMP.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: kmp_total_complexity
   :end-before: //SNIPPET_END: kmp_total_complexity

The bound states that the total number of character comparisons
across both the prefix-function computation and the matching phase
is at most 2n + 2m. This follows the standard amortized argument:
each comparison either advances the text pointer or decreases the
match length, and each can happen at most O(n) times.

The complexity module has **7 admits**, all in the amortized
analysis of the potential function (3 in the prefix-function
complexity proof and 4 in the matcher complexity proof). These
are the standard amortized-analysis steps where the potential
decrease must compensate for the iteration cost.

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
     - 0
   * - NaiveStringMatch.Complexity
     - Pure proof
     - 0
   * - KMP
     - Pulse impl
     - 0
   * - KMP.StrengthenedSpec
     - Pure spec
     - 0
   * - KMP.Complexity
     - Pure proof
     - 7 admit()
   * - RabinKarp
     - Pulse impl
     - 0
   * - RabinKarp.Spec
     - Pure spec
     - 0
   * - RabinKarp.Complexity
     - Pure proof
     - 0

All three string-matching implementations (naive, Rabin-Karp, KMP)
are fully verified with 0 admits in their Pulse code. The admits
are confined to the amortized complexity analysis of KMP (7 admits)
and the rolling-hash correctness lemmas of Rabin-Karp (3 admits).
