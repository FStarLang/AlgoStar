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

The test exercises two scenarios:

1. **Insert at head + search + delete**: Insert 3, 2, 1 at head → `[1;2;3]`.
   Search (forward and backward), search_ptr, delete 2 → `[1;3]`. Delete all.
2. **Insert at tail**: Insert 10 at head, 20 and 30 at tail → `[10;20;30]`.
   Verify via search, delete all.

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
| 11 | `list_search hd tl 2` (after delete) | `false` | ✅ |
| 12 | `list_search hd tl 1` | `true` | ✅ |
| 13 | `list_search hd tl 3` | `true` | ✅ |
| 14–15 | `list_delete 1`, `list_delete 3` | Contents = `[]` | ✅ |
| 16 | `dll_nil_elim` | `hd == None /\ tl == None` | ✅ |
| 17 | `list_insert 10` + `list_insert_tail 20, 30` | `[10; 20; 30]` | ✅ |
| 18–20 | Search for 10, 20, 30 | All `true` | ✅ |
| 21 | Search for 99 | `false` | ✅ |
| 22–24 | Delete 10, 20, 30 | Contents = `[]` | ✅ |

### What is proven

1. **Precondition satisfiability**: All tested operations are successfully
   called: `dll_nil`, `list_insert`, `list_insert_tail`, `list_search`,
   `list_search_back`, `list_search_ptr`, `list_delete`, `dll_nil_elim`.

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

7. **Ghost helpers**: `dll_nil` creates an empty DLL from `None/None` pointers.
   `dll_nil_elim` recovers the pointer-is-None facts from an empty DLL. Both
   work correctly.

8. **Full round-trip**: Insert all elements, delete all elements, verify empty.
   Works for both head-insert and tail-insert scenarios.

### Operations NOT tested

- `list_delete_last` (delete last occurrence) — not tested in this file.
  The reference tests from intent-formalization did not include it. Could be
  added in a follow-up.
- `list_delete_node` (delete by index) — not tested. Requires passing a `nat`
  index with `Cons? l` and `i < L.length l` preconditions, which requires
  ghost-level knowledge of the current list length. Could be tested with
  additional ghost tracking.
- `dll_none_nil`, `dll_some_cons` ghost helpers — not explicitly tested but
  available for client use.

### Auxiliary lemmas needed

**None.** All postconditions are directly usable by Z3.

### Spec issues found

**None.** All tested preconditions are satisfiable and all tested postconditions
are precise enough to determine concrete outputs.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)
