# Singly Linked List Spec Validation — ImplTest.md

## Source

Adapted from
[Test.SLL.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.SLL.fst)
in the [intent-formalization](https://github.com/microsoft/intent-formalization)
repository (spec-validation methodology from
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757)).

## Test Description

**File:** `CLRS.Ch10.SinglyLinkedList.ImplTest.fst`

The test builds a singly linked list by inserting 3, 2, 1 at the head
(producing `[1; 2; 3]`), then exercises search and delete operations with
concrete assertions.

### Operations tested

| Step | Operation | Expected result | Proven? |
|------|-----------|-----------------|---------|
| 1 | Start with `None` + `intro_is_dlist_nil` | Empty list | ✅ |
| 2–4 | `list_insert 3`, `2`, `1` | Contents = `[1; 2; 3]` | ✅ |
| 5 | `list_search hd 2` | `true` | ✅ |
| 6 | `list_search hd 99` | `false` | ✅ |
| 7 | `list_delete hd 2` | Contents = `[1; 3]` | ✅ |
| 7a | `list_delete hd 99` (not found) | Contents = `[1; 3]` (unchanged) | ✅ |
| 8 | `list_search hd 2` | `false` (after delete) | ✅ |
| 9 | `list_search hd 1` | `true` | ✅ |
| 10 | `list_search hd 3` | `true` | ✅ |
| 11 | `list_delete hd 1` | Contents = `[3]` | ✅ |
| 12 | `list_delete hd 3` | Contents = `[]` | ✅ |
| 13 | `elim_is_dlist_nil hd` | Recover `emp` | ✅ |

### What is proven

1. **Precondition satisfiability**: `list_insert`, `list_search`, `list_delete`,
   and the ghost helpers (`intro_is_dlist_nil`, `elim_is_dlist_nil`) are all
   successfully called.

2. **list_insert postcondition precision**: After `list_insert x hd`, the
   contents become `x :: 'l`. The cons-based specification directly gives the
   new list, making the postcondition maximally precise.

3. **list_search postcondition precision**: `found <==> L.mem k 'l` is an iff,
   so the postcondition uniquely determines the result. Verified for both
   present (`2` in `[1;2;3]`) and absent (`99`) elements.

4. **list_delete postcondition precision**: After deleting 2 from `[1;2;3]`,
   the contents become `remove_first 2 [1;2;3]`. Z3 normalizes `remove_first`
   to `[1;3]`. Subsequent searches confirm the precise list contents.

5. **Full round-trip**: Insert 3 elements, delete all 3, recover `emp`. This
   demonstrates the specification is consistent across all operations.

6. **remove_first correctness**: The test indirectly validates that
   `remove_first k l` correctly removes only the first occurrence — after
   deleting 2 from `[1;2;3]`, elements 1 and 3 are still present.

7. **Delete-not-found correctness** (added 2026-03-17): Deleting key 99 (not in
   list) from `[1;3]` leaves the list unchanged (`remove_first 99 [1;3] == [1;3]`).
   Subsequent searches confirm the list is unmodified. This validates that the
   delete spec handles the "key not found" error case correctly.

### Auxiliary lemmas needed

**None.** All postconditions are directly usable by Z3 without helper lemmas.
The cons-based insert spec and `remove_first`-based delete spec are both
normalizable by Z3.

### Spec issues found

**None.** All preconditions are satisfiable and all postconditions are precise.
The SLL specification is clean and complete.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)

### Concrete Execution (C extraction)

Extracted to C via `make test-c` (F* → krml → karamel → C → gcc).

- **Extraction**: `CLRS.Ch10.SinglyLinkedList.{Base,Impl,ImplTest}` extracted
  to `CLRS_Ch10_SinglyLinkedList_ImplTest.c` via karamel. Required including
  `FStar_Pervasives_Native.krml` for `option (box node)` support.
- **Compilation**: Compiled with `cc -std=c11` against krmllib.
- **Execution**: `test_sll_spec_validation()` runs to completion with exit code 0.
  All SLL operations (insert, search, delete) execute correctly with proper
  heap allocation/deallocation of linked list nodes.
- **Status**: ✅ PASS
