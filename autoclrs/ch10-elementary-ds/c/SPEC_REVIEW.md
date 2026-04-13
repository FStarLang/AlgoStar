# Ch10 C Code — Specification Review

## Overview

The C code in this directory implements four data structures from CLRS Ch10:
- **Stack** (array-based: `Stack.c`, pointer-based: `StackPtr.c`)
- **Queue** (array-based: `Queue.c`, pointer-based: `QueuePtr.c`)
- **SinglyLinkedList** (array-based: `SinglyLinkedList.c`, pointer-based: `SinglyLinkedListPtr.c`)
- **DLL** (pointer-based: `DLLPtr.c`)

Each has a corresponding `Impl.fsti` in the parent ch10 directory that specifies the
operations in terms of abstract `list int` (or `list t`) using separation logic predicates.

## Issue 1: No computational code in `_include_pulse` ✅ CLEAN

- Array-based files (Stack.c, Queue.c, SinglyLinkedList.c) don't use `_include_pulse` at all.
- Pointer-based files use `_include_pulse` only for predicates, ghost functions, and type-level
  helpers. No computational code exists in any `_include_pulse` block.

## Issue 2: No complexity instrumentation ✅ CLEAN

- None of the C files contain complexity-related specifications or ghost tick counters.
- The `_tick` variants exist only in the F* Impl.fsti files and are not relevant to C.

## Issue 3: Specification Gaps — Detailed Checklist

### 3.1 Stack (Array-based: Stack.c)

**Impl.fsti specs** (uses `stack_inv s contents` where `contents: erased (list t)`):
- `push`: ensures `stack_inv s (L.append contents [x])`
- `pop`: ensures `∃xs. stack_inv s xs ∧ L.append xs [x] == contents`
- `peek`: ensures `stack_inv s contents ∧ x == L.last contents`
- `stack_empty`: ensures `b <==> L.length contents == 0`

**Current C specs**:
- `push`: ensures `a[old_top] == x`, `top == old_top + 1`, frame preserved ⟹ low-level only
- `pop`: ensures `return == a[old_top - 1]`, `top == old_top - 1`, frame preserved ⟹ low-level only
- `peek`: ensures `return == a[top - 1]` ⟹ low-level only
- `stack_empty`: ensures `top==0 ⟹ return≠0`, `top>0 ⟹ return==0` ⟹ **adequate** (matches Impl.fsti structure)

**Gap**: The C specs prove low-level array properties but never connect them to the
abstract list representation. Need bridge lemmas (like `BridgeLemmas.fst` for SLL)
to show these imply the `stack_inv` postconditions.

**Status**: Low-level specs are CORRECT and SUFFICIENT for the array operations.
The abstraction connection requires bridge lemmas but is NOT required for the C code
itself — the C code is self-contained with its own representation.

### 3.2 Stack (Pointer-based: StackPtr.c)

**Impl.fsti specs**: Same as above (abstract stack operations).

**Current C specs** (uses `is_stack` predicate over linked list):
- `push`: ensures `is_stack return (x :: l)` ✅ matches `stack_push` semantics
- `pop`: ensures `is_stack return (safe_tl l)` and `out == safe_hd l` ✅ matches `stack_pop`
- `peek`: ensures `is_stack top l` and `return == safe_hd l` ✅ matches peek
- `stack_empty`: ensures `return <==> l == []` ✅ matches emptiness check

**Gap**: None significant. The pointer-based specs directly use `list Int32.t` representation
and match the Impl.fsti semantics. The only difference is `Int32.t` vs `int` types.

### 3.3 Queue (Array-based: Queue.c)

**Impl.fsti specs** (uses `queue_inv q contents` with circular buffer):
- `enqueue`: ensures `queue_inv q (L.append contents [x])`
- `dequeue`: ensures `∃xs. queue_inv q xs ∧ contents == x :: xs`
- `queue_empty`: ensures `b <==> L.length contents == 0`

**Current C specs**:
- `enqueue`: ensures `sz == old_sz + 1`, `a[old_tail] == x`, head unchanged,
  tail < cap, frame preserved ⟹ low-level only
- `dequeue`: ensures `sz == old_sz - 1`, `return == a[old_head]`, tail unchanged,
  head < cap, frame preserved ⟹ low-level only
- `queue_empty`: ensures `sz==0 ⟹ return≠0`, `sz>0 ⟹ return==0` ⟹ adequate

**Gap**: Same pattern as Stack. Low-level array specs are correct but not connected
to the abstract list representation. Would need circular-buffer-to-list bridge lemmas.

**Status**: Low-level specs CORRECT and SUFFICIENT. Bridge lemmas possible but complex
due to circular buffer arithmetic.

### 3.4 Queue (Pointer-based: QueuePtr.c)

**Impl.fsti specs**: Same abstract queue operations.

**Current C specs** (uses `is_queue` predicate):
- `enqueue`: ensures `is_queue return (L.append l [x])` ✅ matches enqueue
- `dequeue`: ensures `is_queue return (safe_tl l)` and `out == safe_hd l` ✅ matches dequeue
- `queue_empty`: ensures `return <==> l == []` ✅ matches emptiness check

**Gap**: None significant. Pointer-based specs use `list Int32.t` directly.

### 3.5 SinglyLinkedList (Array-based: SinglyLinkedList.c)

**Impl.fsti specs** (uses `is_dlist` predicate with heap-allocated nodes):
- `list_insert`: ensures `is_dlist new_head (x :: l)` — prepend at head
- `list_search`: ensures `found <==> L.mem k l`
- `list_delete`: ensures `is_dlist new_head (remove_first k l)`

**Current C specs**:
- `list_insert`: ensures `a[0] == x`, shifted right, count incremented ⟹ low-level
- `list_search`: ensures `return <= 1`, `return==0 ⟹ ∀j<n. a[j]≠k` ⟹ low-level
  - **Missing**: `return!=0 ⟹ ∃j<n. a[j]==k` (positive found case)
- `list_delete`: ensures count decremented, return indicates success ⟹ low-level
  - **Missing**: after delete, array contents match `remove_first` on old list
- `list_find_from`: provides index-level find semantics ⟹ correct helper

**Gap**: Bridge lemmas already exist in `CLRS.Ch10.SinglyLinkedList.C.BridgeLemmas.fst`
connecting array-level properties to `list_insert_head`, `list_search`, `list_delete`.
However, the C specs for `list_search` are missing the positive-found postcondition.

### 3.6 SinglyLinkedList (Pointer-based: SinglyLinkedListPtr.c)

**Impl.fsti specs**: Same as SLL Impl.fsti.

**Current C specs** (uses `is_list` predicate):
- `list_insert`: ensures `is_list return (x :: l)` ✅ matches insert
- `list_search`: ensures `is_list head l` and `return <==> L.mem k l` ✅ matches search
- `list_delete`: ensures `is_list return (remove_first k l)` ✅ matches delete

**Gap**: None. Pointer-based specs directly match the Impl.fsti semantics.

### 3.7 DLL (Pointer-based: DLLPtr.c)

**Impl.fsti specs** (uses abstract `dll hd tl l` predicate with head/tail pointers):
- `list_insert`: ensures `dll hd' tl' (x :: l)`
- `list_insert_tail`: ensures `dll hd' tl' (l @ [x])`
- `list_search`: ensures `found <==> L.mem k l`
- `list_search_back`: ensures `found <==> L.mem k l`
- `list_search_ptr`: ensures `result matches membership`
- `list_delete`: ensures `dll hd' tl' (remove_first k l)`
- `list_delete_last`: ensures `dll hd' tl' (remove_last k l)`
- `list_delete_node`: ensures `dll hd' tl' (remove_at i l)`

**Current C specs** (uses `is_dll head prev l`):
- `list_insert`: ensures `is_dll return null (x :: l)` ✅
- `list_insert_tail`: ensures `is_dll return prev (L.append l [x])` ✅
- `list_search`: ensures `is_dll head prev l ** pure (return <==> L.mem k l)` ✅
- `list_search_back`: ensures same as search ✅
- `list_search_ptr`: ensures membership via null/non-null ✅
- `list_delete`: ensures `is_dll return prev (remove_first k l)` ✅
- `list_delete_last`: ensures `is_dll return prev (remove_last k l)` ✅
- `list_delete_node`: ensures `is_dll return prev (remove_at i l)` ✅

**Gap**: The Impl.fsti uses a `dll hd tl l` predicate with BOTH head and tail pointers,
while the C code uses `is_dll head prev l` with only a head pointer (and prev for
internal recursion). The C DLL does NOT maintain a tail pointer. This is a
representation difference — the C code proves operations correct for the singly-linked
traversal direction but doesn't maintain the O(1) tail access that a full DLL provides.

However, the FUNCTIONAL CORRECTNESS (the list contents) is fully proven.

## Summary of Gaps to Fix

| File | Issue | Priority |
|------|-------|----------|
| `SinglyLinkedList.c` | `list_search` missing positive-found postcondition | HIGH |
| `SinglyLinkedList.c` | `list_delete` missing content-level postcondition | MEDIUM |

## Non-Issues (Design Choices, Not Bugs)

1. **Array-based vs pointer-based representation**: Array-based implementations (Stack.c,
   Queue.c, SinglyLinkedList.c) use index-level specifications. Pointer-based implementations
   use recursive linked-list predicates. Both are valid — the array implementations simply
   have a different representation that is correct at the C level.

2. **Int32.t vs int**: The C code uses `int` (mapped to `Int32.t` by c2pulse) while the
   Impl.fsti uses F* `int` (unbounded). This is inherent to the C representation and
   is not a bug.

3. **Bridge lemmas**: The existing BridgeLemmas.fst for SLL demonstrates the pattern for
   connecting array-level specs to list-level specs. Similar bridges could be written for
   Stack and Queue but are not strictly necessary — the C code is self-contained.
