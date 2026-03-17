# Doubly Linked List Spec Validation — ImplTest.md

## Source

Adapted from
[Test.DLL.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL.fst)
and
[Test.DLL2.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL2.fst)
in the [intent-formalization](https://github.com/microsoft/intent-formalization)
repository (spec-validation methodology from
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757)).

## Test Description

**File:** `CLRS.Ch10.DLL.ImplTest.fst`

The test exercises four scenarios:

1. **Insert at head + search + delete**: Insert 3, 2, 1 at head → `[1;2;3]`.
   Search (forward and backward), search_ptr, delete 2 → `[1;3]`. Delete
   non-existent key 99 → `[1;3]` unchanged. Delete all.
2. **Insert at tail**: Insert 10 at head, 20 and 30 at tail → `[10;20;30]`.
   Verify via search, delete all.
3. **list_delete_last**: Build `[1;2;1;3]` (duplicate keys), delete last
   occurrence of 1 → `[1;2;3]`. Delete last of non-existent 99 → unchanged.
4. **list_delete_node (by index)**: Build `[10;20;30]`, delete at index 1 →
   `[10;30]`, delete at index 0 → `[30]`, delete at index 0 → empty.

### Operations tested

| Step | Operation | Expected result | Proven? |
|------|-----------|-----------------|---------|
| — | `dll_nil None None` | Empty DLL | ✅ |
| 1–3 | `list_insert 3, 2, 1` | Contents = `[1; 2; 3]` | ✅ |
| 4 | `list_search hd tl 2` | `true` | ✅ |
| 5 | `list_search hd tl 99` | `false` | ✅ |
| 6 | `list_search_back hd tl 3` | `true` | ✅ |
| 7 | `list_search_back hd tl 0` | `false` | ✅ |
| 8 | `list_search_ptr hd tl 1` | `Some?` | ✅ |
| 9 | `list_search_ptr hd tl 42` | `None?` | ✅ |
| 10 | `list_delete 2` | Contents = `[1; 3]` | ✅ |
| 10a | `list_delete 99` (not found) | Contents = `[1; 3]` (unchanged) | ✅ |
| 11 | `list_search hd tl 2` (after delete) | `false` | ✅ |
| 12 | `list_search hd tl 1` | `true` | ✅ |
| 13 | `list_search hd tl 3` | `true` | ✅ |
| 14–15 | `list_delete 1`, `list_delete 3` | Contents = `[]` | ✅ |
| 16 | `dll_nil_elim` | `hd == None /\ tl == None` | ✅ |
| 17 | `list_insert 10` + `list_insert_tail 20, 30` | `[10; 20; 30]` | ✅ |
| 18–20 | Search for 10, 20, 30 | All `true` | ✅ |
| 21 | Search for 99 | `false` | ✅ |
| 22–24 | Delete 10, 20, 30 | Contents = `[]` | ✅ |
| 25–28 | Build `[1;2;1;3]`, `list_delete_last 1` | `[1;2;3]` | ✅ |
| 29 | Search 1, 2, 3 in result | All `true` | ✅ |
| 30 | `list_delete_last 99` (not found) | Unchanged | ✅ |
| 31–33 | Delete all, build `[10;20;30]` | — | ✅ |
| 34 | `list_delete_node 1` | `[10; 30]` | ✅ |
| 35–37 | Search 10, 30 (`true`), 20 (`false`) | Correct | ✅ |
| 38 | `list_delete_node 0` | `[30]` | ✅ |
| 39 | `list_delete_node 0` | `[]` | ✅ |
| 40 | `dll_nil_elim` | `hd == None /\ tl == None` | ✅ |

### What is proven

1. **Precondition satisfiability**: All tested operations are successfully
   called: `dll_nil`, `list_insert`, `list_insert_tail`, `list_search`,
   `list_search_back`, `list_search_ptr`, `list_delete`, `list_delete_last`,
   `list_delete_node`, `dll_nil_elim`.

2. **list_insert postcondition precision**: Contents become `x :: l`. Directly
   precise.

3. **list_insert_tail postcondition precision**: Contents become `l @ [x]`.
   Combined with head insert, builds `[10; 20; 30]`. Precise.

4. **list_search / list_search_back precision**: Both return
   `found <==> L.mem k 'l`, an iff. Verified for present and absent keys.

5. **list_search_ptr precision**: Returns `Some _` iff `L.mem k 'l`, `None`
   iff `~(L.mem k 'l)`. Verified.

6. **list_delete precision**: Contents become `remove_first k l`. After
   deleting 2 from `[1;2;3]`, the list is `[1;3]`. Confirmed by subsequent
   searches.

7. **Delete-not-found correctness**: Deleting key 99 (not in list) from
   `[1;3]` leaves the list unchanged (`remove_first 99 [1;3] == [1;3]`).
   Validates the error case where the key is absent.

8. **list_delete_last precision**: After deleting the last occurrence of 1
   from `[1;2;1;3]`, the result is `[1;2;3]` — the first occurrence of 1 is
   preserved while the second is removed. Also validates delete-last of a
   non-existent key (99) leaves the list unchanged.

9. **list_delete_node precision**: Deleting at index 1 from `[10;20;30]`
   removes the middle element (20), giving `[10;30]`. Successive deletions
   at index 0 correctly remove elements until the list is empty.

10. **Ghost helpers**: `dll_nil` creates an empty DLL from `None/None` pointers.
    `dll_nil_elim` recovers the pointer-is-None facts from an empty DLL. Both
    work correctly.

11. **Full round-trip**: Insert all elements, delete all elements, verify empty.
    Works for head-insert, tail-insert, delete-last, and delete-node scenarios.

### Auxiliary lemmas needed

**None.** All postconditions are directly usable by Z3.

### Spec issues found

**None.** All tested preconditions are satisfiable and all tested postconditions
are precise enough to determine concrete outputs.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)
