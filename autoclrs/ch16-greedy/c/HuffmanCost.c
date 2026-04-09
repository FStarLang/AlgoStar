/*
 * Huffman Merge — C implementation with c2pulse verification.
 *
 * Implements the merge step of Huffman's algorithm (CLRS §16.3)
 * using the efficient two-queue method. Given sorted frequencies,
 * this runs in O(n) time.
 *
 * Returns the root frequency of the Huffman tree, which equals
 * the sum of all input frequencies.
 *
 * Verified properties:
 *   1. Memory safety: all array accesses within bounds
 *   2. Exactly n-1 merge steps (loop termination)
 *   3. Queue pointer bounds: h1 <= n, h2 <= t2 <= n-1
 *   4. Accounting: h1 + h2 == 2 * step, t2 == step
 *
 * Admitted (requires conservation-of-sum argument):
 *   - Int32 overflow safety for additions
 *   - Result positivity
 *
 * Note: Full tree construction and WPL-optimality proofs require
 * recursive data structures not yet supported by c2pulse.
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
  _requires(_forall(size_t i, i + 1 < n ==> freq[i] <= freq[i + 1]))
  _ensures(freq._length == n)
{
  if (n <= 1) return freq[0];

  /* Phase 1: Compute total_sum (admits overflow proofs). */
  int total_sum = freq[0];
  for (size_t i = 1; i < n; i = i + 1)
    _invariant(_live(i) && _live(total_sum))
    _invariant(_live(*freq))
    _invariant(freq._length == n)
    _invariant(i >= 1 && i <= n)
  {
    _ghost_stmt(admit());
    total_sum = total_sum + freq[i];
  }

  /* Phase 2: Two-queue merge — n-1 steps. */
  size_t mq_len = n - 1;
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
    _invariant((bool) _inline_pulse(SizeT.v $(h1) + SizeT.v $(h2) = 2 * SizeT.v $(step)))
  {
    /* --- Extract min1 --- */
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

    /* --- Extract min2 --- */
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
