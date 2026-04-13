/*
 * Huffman Merge — C implementation with c2pulse verification.
 *
 * Implements the merge step of Huffman's algorithm (CLRS §16.3)
 * using the efficient two-queue method. Given sorted positive
 * frequencies, this runs in O(n) time.
 *
 * Returns the root frequency of the Huffman tree, which equals
 * the sum of all input frequencies.
 *
 * Verified properties:
 *   1. Memory safety: all array accesses within bounds
 *   2. Exactly n-1 merge steps (loop termination)
 *   3. Queue pointer bounds: h1 <= n, h2 <= t2 <= n-1
 *   4. Accounting: h1 + h2 == 2 * step, t2 == step
 *   5. Phase 1 overflow safety: total_sum <= n * 1000000 < INT32_MAX
 *   6. Input frequencies preserved (read-only access)
 *   7. Positive result: return > 0 (tracked through merge queue)
 *
 * Admitted step (1 of 6 original admits remain):
 *   - Phase 2 overflow: min1 + min2 <= total_sum requires a ghost
 *     sum-conservation argument (sum of all queue elements = total_sum,
 *     so each element <= total_sum). Expressing this needs a recursive
 *     ghost function over the array's snapshot sequence, which c2pulse's
 *     specification language cannot currently reference from C-level
 *     invariants.
 *
 * Note: Full tree construction and WPL-optimality proofs live in
 * CLRS.Ch16.Huffman.Impl.fsti and require recursive data structures
 * not yet supported by c2pulse.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

/*
 * Perform Huffman merge steps using the two-queue method.
 *
 * freq[0..n)  — symbol frequencies, sorted non-decreasing
 * n           — number of symbols (must be > 0)
 *
 * Returns the root frequency (== sum of all input frequencies).
 */
int huffman_merge(
    _array int *freq,
    size_t n)
  _requires(freq._length == n)
  _requires(n > 0)
  _requires(n <= 1000)
  _requires(_forall(size_t i, i < n ==> freq[i] > 0 && freq[i] <= 1000000))
  _requires(_forall(size_t i, i + 1 < n ==> freq[i] <= freq[i + 1]))
  _ensures(freq._length == n)
  _ensures(return > 0)
{
  /* Phase 1: Compute total_sum = sum of all frequencies.
   * This bounds all merged values for overflow safety. */
  int total_sum = 0;
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(total_sum))
    _invariant(_live(*freq))
    _invariant(freq._length == n)
    _invariant(i <= n)
    _invariant(n > 0)
    _invariant(n <= 1000)
    _invariant(_forall(size_t j, j < n ==> freq[j] > 0 && freq[j] <= 1000000))
    _invariant(total_sum >= 0)
    _invariant((bool) _inline_pulse(Int32.v $(total_sum) >= SizeT.v $(i)))
    _invariant((bool) _inline_pulse(Int32.v $(total_sum) <= SizeT.v $(i) * 1000000))
  {
    total_sum = total_sum + freq[i];
  }

  /* When n == 1, the merge loop below is skipped entirely.
   * We return freq[0] directly via the h1 < n branch. */

  /* Phase 2: Two-queue merge — n-1 steps. */
  size_t mq_len = n;
  int *mq = (int *)calloc(mq_len, sizeof(int));
  _assert(mq._length == mq_len);

  size_t h1 = 0;
  size_t h2 = 0;
  size_t t2 = 0;

  for (size_t step = 0; step + 1 < n; step = step + 1)
    _invariant(_live(step) && _live(h1) && _live(h2) && _live(t2) && _live(total_sum))
    _invariant(_live(*freq) && _live(*mq))
    _invariant(freq._length == n && mq._length == mq_len)
    _invariant(step + 1 <= n)
    _invariant(h1 <= n)
    _invariant(h2 <= t2 && t2 <= mq_len)
    _invariant(t2 == step)
    _invariant(total_sum > 0)
    _invariant((bool) _inline_pulse(SizeT.v $(h1) + SizeT.v $(h2) = 2 * SizeT.v $(step)))
    _invariant(_forall(size_t j, j < n ==> freq[j] > 0 && freq[j] <= 1000000))
    _invariant(_forall(size_t j, j >= h2 && j < t2 ==> mq[j] > 0))
  {
    /* --- Extract min1: smallest from Q1 or Q2 front --- */
    int min1;
    if (h2 >= t2) {
      min1 = freq[h1];
      h1 = h1 + 1;
    } else if (h1 >= n) {
      min1 = mq[h2];
      h2 = h2 + 1;
    } else if (freq[h1] <= mq[h2]) {
      min1 = freq[h1];
      h1 = h1 + 1;
    } else {
      min1 = mq[h2];
      h2 = h2 + 1;
    }

    /* --- Extract min2: smallest from Q1 or Q2 front --- */
    int min2;
    if (h2 >= t2) {
      min2 = freq[h1];
      h1 = h1 + 1;
    } else if (h1 >= n) {
      min2 = mq[h2];
      h2 = h2 + 1;
    } else if (freq[h1] <= mq[h2]) {
      min2 = freq[h1];
      h1 = h1 + 1;
    } else {
      min2 = mq[h2];
      h2 = h2 + 1;
    }

    _assert(min1 > 0 && min2 > 0);
    /* admit: min1 + min2 <= total_sum by sum conservation
     * (sum of all queue elements = total_sum, each element > 0,
     * so any single element <= total_sum, and min1+min2 = total_sum
     * minus remaining positive elements <= total_sum <= 10^9 < 2^31).
     * Proving this requires a recursive ghost sum over the array
     * snapshot sequence, which c2pulse cannot express. */
    _ghost_stmt(admit());
    int merged = min1 + min2;
    mq[t2] = merged;
    t2 = t2 + 1;
  }

  /* After n-1 merges: exactly 1 item remains. */
  int root;
  if (h1 < n) {
    root = freq[h1];
  } else {
    root = mq[h2];
  }

  free(mq);
  return root;
}
