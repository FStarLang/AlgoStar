# Queue Spec Validation — ImplTest.md

## Source

Adapted from
[Test.Queue.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Queue.fst)
in the [intent-formalization](https://github.com/microsoft/intent-formalization)
repository (spec-validation methodology from
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757)).

## Test Description

**File:** `CLRS.Ch10.Queue.ImplTest.fst`

The test creates a queue of capacity 5 and exercises two scenarios:
1. **Basic FIFO**: enqueue `10, 20, 30`, dequeue and verify FIFO order.
2. **Wraparound**: after emptying, enqueue/dequeue interleaved to exercise the
   circular buffer wraparound logic.

### Operations tested

| Step | Operation | Expected result | Proven? |
|------|-----------|-----------------|---------|
| 1 | `create_queue int 0 5sz` | Empty queue | ✅ |
| 2 | `queue_empty` | `true` | ✅ |
| 3–5 | `enqueue 10, 20, 30` | Contents = `[10; 20; 30]` | ✅ |
| 6 | `queue_empty` | `false` | ✅ |
| 7 | `dequeue` | Returns `10` (FIFO) | ✅ |
| 8 | `dequeue` | Returns `20` | ✅ |
| 9 | `dequeue` | Returns `30` | ✅ |
| 10 | `queue_empty` | `true` | ✅ |
| 11–12 | `enqueue 40, 50` then `dequeue` | Returns `40` | ✅ |
| 13 | `enqueue 60` (wraparound) | — | ✅ |
| 14 | `dequeue` | Returns `50` | ✅ |
| 15 | `dequeue` | Returns `60` | ✅ |
| 16 | `queue_empty` | `true` | ✅ |

### What is proven

1. **Precondition satisfiability**: All four operations (`create_queue`,
   `enqueue`, `dequeue`, `queue_empty`) are successfully called.

2. **Dequeue postcondition precision**: The postcondition
   `exists* xs. queue_inv q (hide xs) ** pure (reveal contents == x :: xs)` is
   strong enough for Z3 to determine the dequeued value in all cases. The
   `x :: xs` decomposition directly gives the head element.

3. **FIFO ordering**: Enqueue `10, 20, 30` → dequeue `10, 20, 30`. Verified.

4. **Circular buffer wraparound**: After 3 enqueues and 3 dequeues (head moves
   forward), then 2 more enqueues, 1 dequeue, 1 enqueue (tail wraps), then 3
   dequeues — all values correct. This exercises the modular arithmetic in the
   invariant `tail == (head + size) % capacity`.

5. **queue_empty precision**: Returns `true` iff contents is empty. Verified at
   multiple empty/non-empty states.

### Auxiliary lemmas needed

**None.** The dequeue postcondition `contents == x :: xs` directly exposes the
head element without needing any lemma. This is a cleaner spec than the stack's
`pop` (which uses `L.append xs [x]` to encode the tail).

### Spec issues found

**None.** All preconditions are satisfiable and all postconditions are precise
enough to determine concrete outputs. The circular buffer invariant is correct
and supports wraparound.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)
