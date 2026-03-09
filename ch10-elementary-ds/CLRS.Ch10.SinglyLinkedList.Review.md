# Singly Linked List (CLRS §10.2)

## Top-Level Signatures

Here are the top-level signatures proven about the singly linked list operations
in `CLRS.Ch10.SinglyLinkedList.Impl.fsti`:

### Core Operations

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

### Complexity-Tracked Variants

```fstar
fn list_insert_tick (x: int) (head: dlist) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* (cf: erased nat).
    is_dlist new_head (x :: 'l) ** GR.pts_to ctr cf **
    pure (reveal cf == reveal c0 + insert_cost)

fn list_search_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns found: bool
  ensures exists* (cf: erased nat).
    is_dlist head 'l ** GR.pts_to ctr cf **
    pure (
      found <==> L.mem k 'l /\
      reveal cf - reveal c0 <= search_cost (L.length 'l)
    )

fn list_delete_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* l' (cf: erased nat).
    is_dlist new_head l' ** GR.pts_to ctr cf **
    pure (
      (L.mem k 'l ==> l' == remove_first k 'l) /\
      (~(L.mem k 'l) ==> l' == 'l) /\
      reveal cf - reveal c0 <= delete_cost (L.length 'l)
    )
```

### Parameters

* `head` is a `dlist` — an `option (box node)` representing a nullable pointer
  to the head node.

* `'l` is a ghost `list int` capturing the logical contents.

* `k`/`x` is the key to search/insert/delete.

* `ctr` is a ghost counter for the tick variants.

### Key Types (from `CLRS.Ch10.SinglyLinkedList.Base`)

```fstar
noeq
type node = {
  key:  int;
  next: option (box node);
}

let dlist = option (box node)
```

### Recursive Predicate (from `CLRS.Ch10.SinglyLinkedList.Base`)

```fstar
let rec is_dlist (x: dlist) (l: list int) : Tot slprop (decreases l) =
  match l with
  | [] -> pure (x == None)
  | hd :: tl ->
    exists* (p: box node) (tail: dlist).
      pure (x == Some p) **
      pts_to p { key = hd; next = tail } **
      is_dlist tail tl
```

This is the standard recursive separation logic predicate for a singly linked
list: the empty list is `None`, and a cons cell owns a heap-allocated node
whose key matches the head and whose `next` pointer represents the tail.

### Preconditions

* `list_insert`: The list `'l` must be well-formed (`is_dlist head 'l`).
* `list_search`: Same; the list is preserved (read-only via `preserves`).
* `list_delete`: Same.

### Postconditions

* `list_insert`: Contents become `x :: 'l` — insertion at head.
* `list_search`: Returns `found <==> L.mem k 'l` — exact membership test.
* `list_delete`: Contents become `remove_first k 'l` — first occurrence removed.

## Auxiliary Definitions

### `remove_first` (from `CLRS.Ch10.SinglyLinkedList.Base`)

```fstar
let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl
```

Removes the first occurrence of `k` from the list. If `k` is not present,
returns the list unchanged.

### Cost Functions (from `CLRS.Ch10.SinglyLinkedList.Impl.fst`)

```fstar
let insert_cost : nat = 1
let search_cost (n: nat) : nat = n
let delete_cost (n: nat) : nat = n + 1
```

* `insert_cost = 1` — exactly 1 operation (pointer manipulation).
* `search_cost n = n` — at most n comparisons (linear scan).
* `delete_cost n = n + 1` — at most n comparisons + 1 pointer surgery.

**Note:** These definitions are abstract (`val`) in the `.fsti` — clients cannot
see the concrete values without accessing the `.fst` file.

## What Is Proven

1. **Functional correctness**: Insert prepends to head, search tests membership,
   delete removes first occurrence — all specified against the ghost list.

2. **Complexity**: The tick variants prove:
   * Insert: exactly 1 tick (O(1))
   * Search: at most n ticks (O(n))
   * Delete: at most n+1 ticks (O(n))

3. **Memory safety**: The `is_dlist` predicate ensures ownership of all nodes.
   The recursive structure guarantees no dangling pointers.

4. **`list_search` preserves the list.** The `preserves` keyword means the list
   predicate is returned unchanged — the operation is read-only.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **Cost functions are abstract in `.fsti`.** Clients see
   `val insert_cost : nat`, `val search_cost (n: nat) : nat`, and
   `val delete_cost (n: nat) : nat` — they cannot determine the concrete values.

2. **`list_delete_tick` has weaker postcondition than `list_delete`.** The tick
   variant uses a conditional postcondition: `L.mem k 'l ==> l' ==
   remove_first k 'l` and `~(L.mem k 'l) ==> l' == 'l`, while the non-tick
   variant directly states `is_dlist new_head (remove_first k 'l)`. These are
   logically equivalent but the tick variant requires the client to case-split.

3. **Only `int` keys.** The node type is hardcoded to `int`. A polymorphic
   version would require an `eqtype` constraint for search/delete.

4. **No `free`/`destroy` for individual nodes.** Deleted nodes are removed from
   the logical list but the memory management is handled by Pulse's separation
   logic (nodes are consumed when removed).

5. **No tail pointer.** Insertion at tail requires O(n) traversal. This is
   inherent to singly linked lists and matches CLRS §10.2.

## Complexity

| Operation | Bound | Linked? | Exact? |
|-----------|-------|---------|--------|
| `list_insert` | O(1) | ✅ via `list_insert_tick` | ✅ Exact (= 1) |
| `list_search` | O(n) | ✅ via `list_search_tick` | Upper bound (≤ n) |
| `list_delete` | O(n) | ✅ via `list_delete_tick` | Upper bound (≤ n+1) |

## Proof Structure

* **`CLRS.Ch10.SinglyLinkedList.Base`**: Shared definitions — node type, `dlist`
  alias, recursive `is_dlist` predicate, ghost fold/unfold boilerplate, and
  `remove_first`.

* **`CLRS.Ch10.SinglyLinkedList.Lemmas`**: Pure correctness lemmas about insert,
  search, delete operations (insert makes element searchable, delete of
  non-existent element is identity, etc.).

* **`CLRS.Ch10.SinglyLinkedList.Spec`**: Pure functional specification with
  count-based lemmas.

## Files

| File | Role |
|------|------|
| `CLRS.Ch10.SinglyLinkedList.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch10.SinglyLinkedList.Impl.fst` | Pulse implementation + cost definitions |
| `CLRS.Ch10.SinglyLinkedList.Base.fst` | Node type, `dlist`, `is_dlist`, `remove_first` |
| `CLRS.Ch10.SinglyLinkedList.Spec.fst` | Pure functional specification |
| `CLRS.Ch10.SinglyLinkedList.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch10.SinglyLinkedList.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch10.SinglyLinkedList.Test.fst` | Tests |
