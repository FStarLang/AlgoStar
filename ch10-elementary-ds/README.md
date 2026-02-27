# Elementary Data Structures in Pulse (CLRS Chapter 10)

This directory contains formally verified implementations of elementary data structures
in Pulse, following CLRS Chapter 10. All code is **admit-free and assume-free**.

## Files

### Stack (§10.1)
- **CLRS.Ch10.Stack.fsti** — Interface specification
- **CLRS.Ch10.Stack.fst** — Implementation
- **CLRS.Ch10.Stack.Test.fst** — Basic usage test

### Queue (§10.1)
- **CLRS.Ch10.Queue.fsti** — Interface specification
- **CLRS.Ch10.Queue.fst** — Implementation
- **CLRS.Ch10.Queue.Test.fst** — Wraparound test

### Singly-Linked List (§10.2)
- **CLRS.Ch10.SinglyLinkedList.Base.fst** — Shared node type, `is_dlist` predicate, ghost helpers
- **CLRS.Ch10.SinglyLinkedList.fst** — Heap-allocated SLL with insert/search/delete
- **CLRS.Ch10.SinglyLinkedList.Test.fst** — Test
- **CLRS.Ch10.SinglyLinkedList.Complexity.fst** — SLL with ghost tick counters and precise cost bounds

### Doubly-Linked List (§10.2)
- **CLRS.Ch10.DLL.fst** — True DLL with `dls` segment predicate, insert/search/delete/delete_node
- **CLRS.Ch10.DLL.Test.fst** — Test

### Pure Specifications
- **CLRS.Ch10.DS.Spec.fst** — Stack (8+ lemmas), Queue (12 lemmas), LinkedList (9 lemmas), refinement lemmas
- **CLRS.Ch10.LinkedList.Spec.fst** — 17 lemmas + 1 theorem for linked-list spec
- **CLRS.Ch10.DataStructures.Complexity.fst** — Operation-count constants

## Stack

```pulse
noeq type stack (t:Type) = {
  data: V.vec t;             // Array to store elements
  top: B.box SZ.t;           // Index of next free slot (0 = empty)
  capacity: erased nat;      // Maximum capacity (ghost)
}
```

### Stack Invariant

The stack maintains a separation logic invariant `stack_inv` that:
- Relates the array contents to a logical list: `arr[i] == list[i]` for `i < top`
- Ensures `top` points to the next free slot (0 = empty)
- The last element of the logical list is the stack top

### Operations

| Operation | Precondition | Postcondition |
|-----------|-------------|---------------|
| `push s x` | `length contents < capacity` | `contents' = L.append contents [x]` |
| `pop s` | `length contents > 0` | `L.append contents' [result] == contents` |
| `peek s` | `Cons? contents` | `exists init. L.append init [result] == contents` |
| `stack_empty s` | — | `result <==> length contents == 0` |

## Queue

Circular buffer with head, tail, and size tracking. Uses a 3-field design
(head + tail + size) rather than CLRS's 2-field design (head + tail) — see
comment in `Queue.fsti` for rationale.

## Building

```bash
make    # from ch10-elementary-ds/
```
