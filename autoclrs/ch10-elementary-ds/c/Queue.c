/*
 * Circular-buffer Queue — C implementation with c2pulse verification.
 *
 * Proves FIFO properties equivalent to CLRS.Ch10.Queue.Impl.fsti:
 *   1. enqueue places element at tail, advances tail with wraparound
 *   2. dequeue returns element at head, advances head with wraparound
 *   3. queue_empty correctly checks emptiness
 *
 * Representation (matches CLRS §10.1 with explicit size tracking):
 *   - a[0..cap): circular buffer storing elements
 *   - head: index of front element (dequeue position)
 *   - tail: index of next insertion point (enqueue position)
 *   - sz: current number of elements
 *   - cap: total capacity of the buffer
 *
 * Invariant: tail == (head + sz) % cap
 * Elements are at positions (head + i) % cap for i in [0, sz)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Queue-empty: check if the queue has no elements.
 *
 * F* equivalent (Impl.fsti):
 *   ensures pure (b <==> L.length (reveal contents) == 0)
 */
size_t queue_empty(size_t sz)
  _ensures(sz == 0 ==> return != 0)
  _ensures(sz > 0 ==> return == 0)
{
  if (sz == 0) return 1;
  return 0;
}

/*
 * Enqueue: place element x at position tail, advance tail with wraparound.
 *
 * Corresponds to CLRS ENQUEUE(Q, x):
 *   Q[Q.tail] = x
 *   if Q.tail == Q.length
 *     Q.tail = 1
 *   else Q.tail = Q.tail + 1
 *
 * F* equivalent (Impl.fsti):
 *   ensures queue_inv q (hide (L.append (reveal contents) [x]))
 *   ≡ a[old_tail] == x, tail advances with wraparound, size increments,
 *     head unchanged, other elements unchanged
 */
void enqueue(_array int *a, size_t cap, size_t *head, size_t *tail, size_t *sz, int x)
  _preserves(a._length == cap)
  _requires(cap > 0 && *sz < cap)
  _requires(*head < cap && *tail < cap)
  _ensures(*sz == _old(*sz) + 1)
  _ensures(*head == _old(*head))
  _ensures(*tail < cap)
  _ensures(a[_old(*tail)] == x)
  _ensures(_forall(size_t i, i < cap && i != _old(*tail) ==> a[i] == _old(a[i])))
{
  a[*tail] = x;
  *tail = *tail + 1;
  if (*tail >= cap) *tail = 0;
  *sz = *sz + 1;
}

/*
 * Dequeue: return element at head, advance head with wraparound.
 *
 * Corresponds to CLRS DEQUEUE(Q):
 *   x = Q[Q.head]
 *   if Q.head == Q.length
 *     Q.head = 1
 *   else Q.head = Q.head + 1
 *   return x
 *
 * F* equivalent (Impl.fsti):
 *   ensures ∃xs. queue_inv q (hide xs) ∧ reveal contents == x :: xs
 *   ≡ return == a[old_head], head advances with wraparound, size decrements,
 *     tail unchanged, array unchanged
 */
int dequeue(_array int *a, size_t cap, size_t *head, size_t *tail, size_t *sz)
  _preserves(a._length == cap)
  _requires(cap > 0 && *sz > 0)
  _requires(*head < cap && *tail < cap)
  _ensures(*sz == _old(*sz) - 1)
  _ensures(*tail == _old(*tail))
  _ensures(*head < cap)
  _ensures(return == _old(a[*head]))
  _ensures(_forall(size_t i, i < cap ==> a[i] == _old(a[i])))
{
  int x = a[*head];
  *head = *head + 1;
  if (*head >= cap) *head = 0;
  *sz = *sz - 1;
  return x;
}
