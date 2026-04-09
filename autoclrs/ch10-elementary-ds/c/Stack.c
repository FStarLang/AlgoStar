/*
 * Array-based Stack — C implementation with c2pulse verification.
 *
 * Proves LIFO properties equivalent to CLRS.Ch10.Stack.Impl.fsti:
 *   1. push preserves existing elements and places new element at top
 *   2. pop returns the top element and preserves elements below
 *   3. peek returns top element without modification
 *   4. stack_empty correctly checks emptiness
 *
 * Representation:
 *   - a[0..top): stack elements in push order
 *   - top: index of next free slot (0 = empty)
 *   - cap: array capacity
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Push: add element x at position top, then increment top.
 *
 * Corresponds to CLRS PUSH(S, x):
 *   S.top = S.top + 1
 *   S[S.top] = x
 *
 * F* equivalent (Impl.fsti):
 *   ensures stack_inv s (hide (L.append (reveal contents) [x]))
 *   ≡ a[old_top] == x ∧ top == old_top + 1 ∧ ∀i < old_top. a[i] unchanged
 */
void push(_array int *a, size_t cap, size_t *top, int x)
  _preserves(a._length == cap)
  _requires(*top < cap)
  _ensures(*top == _old(*top) + 1)
  _ensures(a[_old(*top)] == x)
  _ensures(_forall(size_t i, i < _old(*top) ==> a[i] == _old(a[i])))
{
  a[*top] = x;
  *top = *top + 1;
}

/*
 * Pop: decrement top, then return the element at the new top.
 *
 * Corresponds to CLRS POP(S):
 *   S.top = S.top - 1
 *   return S[S.top + 1]
 *
 * F* equivalent (Impl.fsti):
 *   ensures ∃xs. stack_inv s (hide xs) ∧ L.append xs [x] == reveal contents
 *   ≡ return == a[old_top - 1] ∧ top == old_top - 1 ∧ ∀i < top. a[i] unchanged
 */
int pop(_array int *a, size_t cap, size_t *top)
  _preserves(a._length == cap)
  _requires(*top > 0 && *top <= cap)
  _ensures(*top == _old(*top) - 1)
  _ensures(return == _old(a[*top - 1]))
  _ensures(_forall(size_t i, i < *top ==> a[i] == _old(a[i])))
{
  *top = *top - 1;
  return a[*top];
}

/*
 * Peek: return the top element without modifying the stack.
 *
 * F* equivalent (Impl.fsti):
 *   ensures stack_inv s contents ∧ x == L.last (reveal contents)
 *   ≡ return == a[top - 1] ∧ array unchanged
 */
int peek(_array int *a, size_t cap, size_t top)
  _preserves(a._length == cap)
  _requires(top > 0 && top <= cap)
  _ensures(return == _old(a[top - 1]))
{
  return a[top - 1];
}

/*
 * Stack-empty: check if the stack has no elements.
 *
 * F* equivalent (Impl.fsti):
 *   ensures pure (b <==> L.length (reveal contents) == 0)
 *   ≡ return nonzero ↔ top == 0
 */
size_t stack_empty(size_t top)
  _ensures(top == 0 ==> return != 0)
  _ensures(top > 0 ==> return == 0)
{
  if (top == 0) return 1;
  return 0;
}
