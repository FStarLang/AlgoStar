# Elementary Data Structures in Pulse (CLRS Chapter 10)

This directory contains formally verified implementations of elementary data
structures from CLRS Chapter 10: **Stack** (§10.1), **Queue** (§10.1),
**Singly-Linked List** (§10.2), and **Doubly-Linked List** (§10.2).

**All proofs are complete with zero admits, zero assumes, and zero assume_ calls.**

## Summary Table

| Data Structure | CLRS | Operations | Ghost List | Complexity (proven) | Admits |
|----------------|------|------------|------------|---------------------|--------|
| Stack | §10.1 | `push`, `pop`, `peek`, `stack_empty` | `list t` (append model) | O(1) by construction | 0 |
| Queue | §10.1 | `enqueue`, `dequeue`, `queue_empty` | `list t` (append model) | O(1) by construction | 0 |
| Singly-Linked List | §10.2 | `list_insert`, `list_search`, `list_delete` | `list int` | O(1)/O(n)/O(n) via ghost ticks | 0 |
| Doubly-Linked List | §10.2 | `list_insert`, `list_search`, `list_delete`, + 5 more | `list int` | O(1) insert, O(n) search/delete | 0 |

## Stack (CLRS §10.1)

### Specification

The pure stack model from `DS.Spec`:

```fstar
type stack (a: Type) = list a
let stack_push (#a: Type) (s: stack a) (x: a) : stack a = x :: s
let stack_pop (#a: Type) (s: stack a{Cons? s}) : (a & stack a) =
  match s with | hd :: tl -> (hd, tl)
```

LIFO properties hold by computation:
```fstar
let lemma_stack_lifo_pop_push (s: stack a) (x: a)
  : Lemma (fst (stack_pop (stack_push s x)) == x) = ()
```

### Data Structure and Invariant

```fstar
noeq type stack (t:Type) = {
  data: V.vec t;          // Array to store elements
  top: B.box SZ.t;        // Index of next free slot (0 = empty)
  capacity: erased nat;   // Maximum capacity (ghost)
}
```

The separation-logic invariant `stack_inv` ties the array contents to a
ghost list element-by-element:

```fstar
let stack_inv (#t:Type) (s: stack t) (contents: erased (list t)) : slprop =
  exists* arr_seq top_v.
    V.pts_to s.data arr_seq ** B.pts_to s.top top_v **
    pure (SZ.v top_v == L.length contents /\ SZ.v top_v <= reveal s.capacity /\
          (forall (i:nat). i < L.length contents ==> Seq.index arr_seq i == L.index contents i))
```

### Correctness Theorems

| Operation | Precondition | Postcondition |
|-----------|-------------|---------------|
| `create_stack` | `capacity > 0` | `stack_inv s []` |
| `push s x` | `length contents < capacity` | `stack_inv s (append contents [x])` |
| `pop s` | `length contents > 0` | `∃xs. stack_inv s xs ∧ append xs [result] == contents` |
| `peek s` | `Cons? contents` | `∃init. append init [result] == contents` |
| `stack_empty s` | — | `result ⟺ length contents == 0` |

**Strongest guarantee?** Yes. The ghost list fully specifies LIFO behavior:
`push` appends to the end, `pop` removes the last. The invariant is a
complete abstraction — clients reason purely about lists.

### Limitations

- **Fixed capacity**: Stack size is bounded at creation time. No dynamic
  resizing.
- **No complexity ghost counter**: O(1) follows from single array accesses
  but is not mechanized.

## Queue (CLRS §10.1)

### Data Structure and Invariant

Circular buffer with head, tail, and size tracking:

```fstar
noeq type queue (t:Type) = {
  data: V.vec t;
  head: B.box SZ.t;       // Front of queue (dequeue position)
  tail: B.box SZ.t;       // Next insertion point
  size: B.box SZ.t;       // Current number of elements
  capacity_sz: SZ.t;      // Runtime capacity
  capacity: erased nat;   // Ghost capacity
}
```

**Design note**: CLRS uses 2 fields (head + tail) where an empty slot
distinguishes full from empty. We use 3 fields (head + tail + size) to
allow full capacity usage and simplify the invariant.

The invariant maps circular indices to the logical list:

```fstar
(forall (i:nat). i < size ==>
  Seq.index arr_seq ((head + i) % capacity) == L.index contents i)
```

### Correctness Theorems

| Operation | Precondition | Postcondition |
|-----------|-------------|---------------|
| `create_queue` | `capacity > 0` | `queue_inv q []` |
| `enqueue q x` | `length contents < capacity` | `queue_inv q (append contents [x])` |
| `dequeue q` | `length contents > 0` | `∃xs. queue_inv q xs ∧ contents == result :: xs` |
| `queue_empty q` | — | `result ⟺ length contents == 0` |

**Strongest guarantee?** Yes. `enqueue` appends to back, `dequeue` returns
from front (`contents == result :: xs`). This is the complete FIFO
specification.

### Limitations

- **Fixed capacity**: No dynamic resizing.
- **3-field design**: Uses one extra field vs CLRS; not a fidelity issue but
  a design choice.

## Singly-Linked List (CLRS §10.2)

### Specification

Node type and recursive predicate from `SinglyLinkedList.Base`:

```fstar
noeq type node = { key: int; next: option (box node); }
let dlist = option (box node)

let rec is_dlist (x: dlist) (l: list int) : Tot slprop (decreases l) =
  match l with
  | [] -> pure (x == None)
  | hd :: tl -> exists* (p: box node) (tail: dlist).
      pure (x == Some p) ** pts_to p { key = hd; next = tail } ** is_dlist tail tl
```

### Correctness Theorems

```fstar
fn list_insert (x: int) (head: dlist)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (x :: 'l)

fn list_search (head: dlist) (k: int)
  preserves is_dlist head 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

fn list_delete (head: dlist) (k: int)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (remove_first k 'l)
```

### Complexity (Ghost Tick Variants)

The `_tick` variants thread a `GhostReference.ref nat` counter:

| Operation | Proven Bound |
|-----------|-------------|
| `list_insert_tick` | Exactly 1 (O(1)) |
| `list_search_tick` | ≤ `search_cost(n)` (O(n)) |
| `list_delete_tick` | ≤ `delete_cost(n)` (O(n)) |

### Limitations

- **Singly-linked**: No O(1) delete by pointer (must traverse from head).
- **No tail pointer**: Insert is head-only.

## Doubly-Linked List (CLRS §10.2)

### Specification

Abstract node type with a `dll` separation-logic predicate:

```fstar
val node : Type0
let dptr = option (box node)
val dll (hd tl: dptr) (l: list int) : slprop
```

The DLL maintains both head and tail pointers, enabling O(1) operations
at both ends.

### Correctness Theorems

Eight verified operations:

```fstar
fn list_insert (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires ∃ hd tl. pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures ∃ hd' tl'. pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)

fn list_insert_tail (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  ensures ... dll hd' tl' (l @ [x])

fn list_search (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  ensures ... dll hd' tl' (remove_first k l)

fn list_delete_node (hd_ref tl_ref: ref dptr) (#l: erased (list int){Cons? l})
  (i: nat{i < L.length l})
  ensures ... dll hd' tl' (remove_at i l)
```

Also provides: `list_search_back`, `list_search_ptr`, `list_delete_last`.

### Strongest Guarantee?

Yes. Each operation's postcondition specifies the exact effect on the
ghost list: insert prepends/appends, search returns membership, delete
removes the first/last occurrence or at a given index. The `dll` predicate
fully abstracts the pointer structure.

### Limitations

- **No complexity ghost counter**: O(1) insert and O(n) search/delete
  follow from the algorithm structure but are not mechanized with ticks
  (unlike the SLL).
- **Abstract node type**: Clients cannot directly inspect node fields;
  all interaction is through the DLL operations.

## File Inventory

| File | Role | Admits |
|------|------|--------|
| `CLRS.Ch10.DS.Spec.fst` | Pure specs: Stack (8+ lemmas), Queue (12 lemmas), LinkedList (9 lemmas) | 0 |
| `CLRS.Ch10.Stack.Spec.fst` | Pure functional stack spec | 0 |
| `CLRS.Ch10.Stack.Impl.fsti` | Stack interface: type, invariant, operations | 0 |
| `CLRS.Ch10.Stack.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch10.Stack.Lemmas.fsti` | Stack lemma interface (LIFO property) | 0 |
| `CLRS.Ch10.Stack.Lemmas.fst` | Stack lemma proofs | 0 |
| `CLRS.Ch10.Stack.Test.fst` | Basic usage test | 0 |
| `CLRS.Ch10.Queue.Spec.fst` | Pure functional queue spec (two-list) | 0 |
| `CLRS.Ch10.Queue.Impl.fsti` | Queue interface: type, invariant, operations | 0 |
| `CLRS.Ch10.Queue.Impl.fst` | Pulse implementation (circular buffer) | 0 |
| `CLRS.Ch10.Queue.Lemmas.fsti` | Queue lemma interface (FIFO property) | 0 |
| `CLRS.Ch10.Queue.Lemmas.fst` | Queue lemma proofs | 0 |
| `CLRS.Ch10.Queue.Test.fst` | Wraparound test | 0 |
| `CLRS.Ch10.SinglyLinkedList.Base.fst` | Node type, `is_dlist` predicate, ghost helpers | 0 |
| `CLRS.Ch10.SinglyLinkedList.Spec.fst` | 17 lemmas + 1 theorem for SLL spec | 0 |
| `CLRS.Ch10.SinglyLinkedList.Impl.fsti` | SLL interface: ops + tick variants | 0 |
| `CLRS.Ch10.SinglyLinkedList.Impl.fst` | Pulse implementation | 0 |
| `CLRS.Ch10.SinglyLinkedList.Lemmas.fsti` | SLL lemma interface | 0 |
| `CLRS.Ch10.SinglyLinkedList.Lemmas.fst` | SLL lemma proofs | 0 |
| `CLRS.Ch10.SinglyLinkedList.Test.fst` | Test | 0 |
| `CLRS.Ch10.DLL.Spec.fst` | Pure DLL spec | 0 |
| `CLRS.Ch10.DLL.Impl.fsti` | DLL interface: 8 operations | 0 |
| `CLRS.Ch10.DLL.Impl.fst` | Pulse implementation (dls segment predicate) | 0 |
| `CLRS.Ch10.DLL.Lemmas.fsti` | DLL lemma interface | 0 |
| `CLRS.Ch10.DLL.Lemmas.fst` | DLL lemma proofs | 0 |
| `CLRS.Ch10.DLL.Test.fst` | Test | 0 |
| `Makefile` | Build configuration | — |

## Building

```bash
# From the ch10-elementary-ds directory:
make

# Or from the project root:
make -C ch10-elementary-ds
```

Requires the Pulse toolchain. Set `PULSE_ROOT` if not at `../../pulse`.
