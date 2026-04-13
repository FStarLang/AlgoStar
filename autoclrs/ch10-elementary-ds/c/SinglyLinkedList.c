/*
 * Array-based Singly Linked List — C implementation with c2pulse verification.
 *
 * Represents a singly linked list as a contiguous array a[0..n):
 *   - a[0] is the head of the list
 *   - Elements stored in list order: logical list is [a[0], a[1], ..., a[n-1]]
 *   - n: current number of elements
 *   - cap: array capacity
 *
 * Uses _rec functions for naturally recursive list traversals,
 * corresponding to CLRS.Ch10.SinglyLinkedList.Spec operations:
 *   - list_find_from / list_search: LIST-SEARCH (recursive scan)
 *   - shift_left / list_delete:     LIST-DELETE (find + compact)
 *   - shift_right / list_insert:    LIST-INSERT at head (shift + place)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * SHIFT-LEFT (recursive): Move elements a[pos+1..n) left by one,
 * effectively removing the element at position pos.
 *
 * After: a[pos..n-2] == old a[pos+1..n-1], elements before pos unchanged.
 * Corresponds to the pointer-surgery step of LIST-DELETE.
 */
_rec void shift_left(_array int *a, size_t n, size_t pos)
  _requires(a._length >= n)
  _requires(pos < n && n > 0)
  _preserves_value(a._length)
  _ensures(_forall(size_t j, j < pos ==> a[j] == _old(a[j])))
  _ensures(_forall(size_t j, pos < j && j < n ==> a[j - 1] == _old(a[j])))
  _ensures(_forall(size_t j, n <= j && j < a._length ==> a[j] == _old(a[j])))
  _decreases(n - pos)
{
  if (pos + 1 >= n) return;
  a[pos] = a[pos + 1];
  shift_left(a, n, pos + 1);
}

/*
 * SHIFT-RIGHT (recursive): Move elements a[0..hi) right by one to a[1..hi+1),
 * processing high-to-low to avoid overwrites.
 *
 * After: a[1..hi] == old a[0..hi-1], a[0] unchanged (caller overwrites it).
 * Corresponds to making room at the head for LIST-INSERT.
 */
_rec void shift_right(_array int *a, size_t cap, size_t hi)
  _requires(a._length == cap)
  _requires(hi < cap)
  _preserves_value(a._length)
  _ensures(a[0] == _old(a[0]))
  _ensures(_forall(size_t j, 0 < j && j <= hi ==> a[j] == _old(a[j - 1])))
  _ensures(_forall(size_t j, hi < j && j < cap ==> a[j] == _old(a[j])))
  _decreases(hi)
{
  if (hi == 0) return;
  a[hi] = a[hi - 1];
  if (hi <= 1) return;
  shift_right(a, cap, hi - 1);
}

/*
 * LIST-FIND (recursive): Find first index j in [i,n) where a[j]==k.
 * Returns the found index, or n if not found.
 *
 * Corresponds to the recursive structure of
 *   CLRS.Ch10.SinglyLinkedList.Spec.list_search
 * which scans node-by-node through the list.
 */
_rec size_t list_find_from(_array int *a, size_t n, int k, size_t i)
  _requires(a._length >= n)
  _requires(i <= n)
  _preserves_value(a._length)
  _ensures(_forall(size_t j, j < n ==> a[j] == _old(a[j])))
  _ensures(return <= n && return >= i)
  _ensures(return < n ==> a[return] == k)
  _ensures(_forall(size_t j, i <= j && j < return ==> a[j] != k))
  _decreases(n - i)
{
  if (i >= n) return n;
  if (a[i] == k) return i;
  return list_find_from(a, n, k, i + 1);
}

/*
 * LIST-SEARCH: Check membership of key k in a[0..n).
 * Returns nonzero if found, 0 otherwise.
 */
size_t list_search(_array int *a, size_t n, int k)
  _requires(a._length >= n)
  _preserves_value(a._length)
  _ensures(_forall(size_t j, j < n ==> a[j] == _old(a[j])))
  _ensures(return <= 1)
  _ensures(return == 0 ==> _forall(size_t j, j < n ==> a[j] != k))
  _ensures(return != 0 ==> _exists(size_t j, j < n && a[j] == k))
{
  size_t idx = list_find_from(a, n, k, 0);
  if (idx < n) return 1;
  return 0;
}

/*
 * LIST-DELETE: Remove first occurrence of key k from a[0..*count).
 * Returns 1 if deleted (decrements *count), 0 if not found.
 */
size_t list_delete(_array int *a, size_t cap, size_t *count, int k)
  _preserves(a._length == cap)
  _requires(*count <= cap)
  _ensures(*count <= _old(*count))
  _ensures(return <= 1)
  _ensures(return == 0 ==> *count == _old(*count))
  _ensures(return == 0 ==> _forall(size_t j, j < *count ==> a[j] == _old(a[j])))
  _ensures(return != 0 ==> *count + 1 == _old(*count))
{
  if (*count == 0) return 0;
  size_t idx = list_find_from(a, *count, k, 0);
  if (idx >= *count) return 0;
  shift_left(a, *count, idx);
  *count = *count - 1;
  return 1;
}

/*
 * LIST-INSERT: Insert element x at head (position 0) of a[0..*count).
 * Shifts existing elements right to make room.
 */
void list_insert(_array int *a, size_t cap, size_t *count, int x)
  _preserves(a._length == cap)
  _requires(*count < cap)
  _ensures(*count == _old(*count) + 1)
  _ensures(a[0] == x)
  _ensures(_forall(size_t j, 0 < j && j <= _old(*count) ==> a[j] == _old(a[j - 1])))
{
  shift_right(a, cap, *count);
  a[0] = x;
  *count = *count + 1;
}
