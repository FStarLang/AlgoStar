# Doubly Linked List (CLRS §10.2)

## Top-Level Signatures

Here are the top-level signatures proven about the doubly linked list operations
in `CLRS.Ch10.DLL.Impl.fsti`:

### Abstract Types

```fstar
val node : Type0

let dptr = option (box node)

val dll (hd tl: dptr) (l: list int) : slprop
```

The node type is **fully abstract** — clients cannot inspect its fields. The
`dll` predicate is also abstract, taking head/tail pointers and a logical list.

### Operations

```fstar
fn list_insert (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)

fn list_insert_tail (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (l @ [x])

fn list_search (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

fn list_search_back (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

fn list_search_ptr (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns result: dptr
  ensures pure (
    match result with
    | None -> ~(L.mem k 'l)
    | Some _ -> L.mem k 'l
  )

fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l)

fn list_delete_last (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_last k l)

fn list_delete_node
  (hd_ref tl_ref: ref dptr)
  (#l: erased (list int) {Cons? l})
  (i: nat {i < L.length l})
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_at i l)
```

### Parameters

* `hd_ref`, `tl_ref` are mutable references to head/tail pointers. The DLL
  maintains both ends for O(1) insert at head or tail.

* `hd`, `tl` are the actual head/tail `dptr` values (nullable `option (box node)`).

* `l` is the ghost list of contents.

* `k` is the key to search/delete; `i` is the index for `list_delete_node`.

### Preconditions

* `list_insert`/`list_insert_tail`: Well-formed DLL.
* `list_delete_node`: `Cons? l` (non-empty) and `i < L.length l`.
* No capacity constraints — the list is heap-allocated and unbounded.

### Postconditions

* `list_insert`: Contents become `x :: l` — insertion at head.
* `list_insert_tail`: Contents become `l @ [x]` — insertion at tail.
* `list_search` / `list_search_back`: `found <==> L.mem k 'l`.
* `list_search_ptr`: Returns `Some _` if found, `None` if not.
* `list_delete`: Contents become `remove_first k l`.
* `list_delete_last`: Contents become `remove_last k l`.
* `list_delete_node`: Contents become `remove_at i l`.

## Internal Representation

### Node Type (from `CLRS.Ch10.DLL.Impl.fst`, hidden from `.fsti`)

```fstar
noeq
type node = {
  key:  int;
  prev: option (box node);
  next: option (box node);
}
```

Each node has a key and bidirectional pointers (prev/next), matching CLRS §10.2.

### Segment Predicate `dls` (from `CLRS.Ch10.DLL.Impl.fst`)

```fstar
let rec dls
  (p: box node) (l: list int {Cons? l})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  : Tot slprop (decreases l)
  = match l with
    | [k] ->
      exists* (v: node).
        pts_to p v **
        pure (v.key == k /\ v.prev == prev_ptr /\
              v.next == last_ptr /\ p == tail)
    | k :: rest ->
      exists* (v: node) (np: box node).
        pts_to p v **
        dls np rest (Some p) tail last_ptr **
        pure (v.key == k /\ v.prev == prev_ptr /\
              v.next == Some np)
```

The `dls` (doubly-linked segment) predicate describes a linked chain from `p`
to `tail`, with `prev_ptr` as the predecessor of `p` and `last_ptr` as the
successor of `tail`. This is the core ownership model — each node owns its
heap cell, and the recursive structure ensures no aliasing.

```fstar
let dll (hd tl: dptr) (l: list int) : slprop =
  match l with
  | [] -> pure (hd == None /\ tl == None)
  | k :: rest ->
    exists* (hp tp: box node).
      dls hp (k :: rest) None tp None **
      pure (hd == Some hp /\ tl == Some tp)
```

The top-level `dll` wraps `dls` with `None` for the external prev/next pointers.

## Auxiliary Definitions

### `remove_first`, `remove_at`, `remove_last` (from `CLRS.Ch10.DLL.Impl.fsti`)

```fstar
let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl

let rec remove_at (i: nat) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if i = 0 then tl else hd :: remove_at (i - 1) tl

let rec remove_last (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl ->
    if mem k tl then hd :: remove_last k tl
    else if hd = k then tl
    else hd :: tl
```

### Ghost Helpers

```fstar
ghost fn dll_nil (hd tl: dptr)
  requires pure (hd == None /\ tl == None)
  ensures dll hd tl []

ghost fn dll_nil_elim (hd tl: dptr)
  requires dll hd tl []
  ensures pure (hd == None /\ tl == None)

ghost fn dll_none_nil (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (hd == None)
  ensures pure (l == ([] #int))

ghost fn dll_some_cons (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (Some? hd)
  ensures pure (Cons? l)
```

These ghost functions allow clients to reason about the relationship between
pointers and list contents without accessing internal representation.

## What Is Proven

1. **Functional correctness**: Insert at head/tail, search (front-to-back and
   back-to-front), delete by key (first/last occurrence), and delete by index —
   all specified against the ghost list.

2. **Rich operation set**: Eight operations total, including bidirectional
   search and three deletion variants. This goes beyond CLRS §10.2.

3. **Abstract interface**: The node type and `dll` predicate are fully abstract.
   Clients interact only through the published operations and ghost helpers.

4. **Memory safety**: The `dls` segment predicate ensures exclusive ownership of
   each node. No aliasing, no dangling pointers.

**Zero admits, zero assumes.** All operations are fully verified (confirmed in
the implementation: "All operations fully verified with 0 admits").

## Specification Gaps and Limitations

1. **No complexity tracking.** Unlike the singly linked list's tick variants,
   the DLL has no ghost counter instrumentation. Operation costs are not formally
   stated:
   * `list_insert` and `list_insert_tail` are O(1) in practice.
   * `list_search`, `list_search_back`, `list_delete`, `list_delete_last` are
     O(n).
   * `list_delete_node` takes an index, requiring O(n) traversal to the index.

2. **`list_delete_node` is O(n), not O(1).** CLRS §10.2 describes delete-by-node
   as O(1) when given a pointer to the node. This implementation takes an
   *index* (`i: nat`), requiring traversal. The O(1) pointer-based delete is
   not provided.

3. **Only `int` keys.** The node key type is hardcoded to `int`.

4. **`list_delete` and `list_delete_last` hide the input list.** The
   `requires` clause uses `exists* ... l` rather than a named ghost parameter,
   so the client does not control which list the operation starts from. This
   is a weaker interface than the singly linked list's version.

5. **No `free`/`destroy` for the entire list.** Individual deletions consume
   nodes, but there is no bulk deallocation.

6. **More complex ownership model.** The `dls` segment predicate is
   significantly more complex than the singly linked list's `is_dlist`. It
   tracks prev/next pointers, head/tail identity, and segment boundaries. This
   complexity is necessary for doubly-linked structure but makes the proof
   substantially harder.

## Complexity

| Operation | Expected | Linked? |
|-----------|----------|---------|
| `list_insert` | O(1) | Not tracked |
| `list_insert_tail` | O(1) | Not tracked |
| `list_search` | O(n) | Not tracked |
| `list_search_back` | O(n) | Not tracked |
| `list_search_ptr` | O(n) | Not tracked |
| `list_delete` | O(n) | Not tracked |
| `list_delete_last` | O(n) | Not tracked |
| `list_delete_node` | O(n) | Not tracked |

## Proof Structure

The proof is the most complex in Chapter 10, due to the bidirectional pointer
structure. Key challenges:

* **Segment splitting/joining**: Operations that modify the middle of the list
  must split the `dls` segment, modify nodes, and rejoin. The implementation
  handles "predicate split/join without admits" (per implementation comments).

* **`CLRS.Ch10.DLL.Lemmas`**: Pure correctness lemmas about the list operations
  (insert/search/delete correctness, length invariants).

* **`CLRS.Ch10.DLL.Spec`**: Pure functional specification — at the pure level, a
  DLL is just a `list int`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch10.DLL.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch10.DLL.Impl.fst` | Pulse implementation (node, `dls`, `dll`, all ops) |
| `CLRS.Ch10.DLL.Spec.fst` | Pure functional DLL specification |
| `CLRS.Ch10.DLL.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch10.DLL.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch10.DLL.Test.fst` | Tests |
