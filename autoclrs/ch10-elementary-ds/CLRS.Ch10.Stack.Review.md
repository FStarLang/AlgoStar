# Stack (CLRS §10.1)

## Top-Level Signatures

Here are the top-level signatures proven about the stack operations in
`CLRS.Ch10.Stack.Impl.fsti`:

### Data Type

```fstar
noeq type stack (t:Type) = {
  data: V.vec t;
  top: B.box SZ.t;      // Index of next free slot (0 = empty)
  capacity: erased nat;
}
```

### Invariant

```fstar
let stack_inv (#t:Type) (s: stack t) (contents: erased (list t)) : slprop = 
  exists* arr_seq top_v.
    V.pts_to s.data arr_seq **
    B.pts_to s.top top_v **
    pure (
      SZ.v top_v == L.length contents /\
      SZ.v top_v <= reveal s.capacity /\
      Seq.length arr_seq == reveal s.capacity /\
      SZ.fits (reveal s.capacity + 1) /\
      (forall (i:nat). i < L.length contents ==> 
        Seq.index arr_seq i == L.index contents i)
    )
```

### Operations

```fstar
fn create_stack (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp ** pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns s: stack t
  ensures stack_inv s (hide []) ** 
          pure (reveal s.capacity == SZ.v capacity /\ SZ.v capacity > 0)

fn stack_empty (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  returns b: bool
  ensures stack_inv s contents **
          pure (b <==> L.length (reveal contents) == 0)

fn push (#t:Type0) (s: stack t) (#contents: erased (list t)) (x: t)
  requires stack_inv s contents **
           pure (L.length (reveal contents) < reveal s.capacity)
  returns unit
  ensures stack_inv s (hide (L.append (reveal contents) [x]))

fn pop (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    stack_inv s (hide xs) **
    pure (L.append xs [x] == reveal contents)

fn peek (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (Cons? (reveal contents))
  returns x: t
  ensures stack_inv s contents **
          pure (exists (init:list t). L.append init [x] == reveal contents)
```

### Parameters

* `s` is the stack structure: an array (`data`), a mutable top index (`top`),
  and a ghost `capacity`.

* `contents` is a ghost list capturing the logical contents of the stack.

* `x` is the element to push.

### Preconditions

* `create_stack`: capacity > 0 and fits in machine size.
* `push`: stack is not full (`L.length contents < capacity`).
* `pop`/`peek`: stack is non-empty.

### Postconditions

* `push`: the logical contents become `L.append contents [x]` — the element is
  appended at the end (the end represents the top of the stack).

* `pop`: returns `x` such that `L.append xs [x] == contents` — the last element
  is removed (LIFO).

* `peek`: returns the last element without modifying the stack.

* `stack_empty`: returns `true` iff the logical list is empty.

## Auxiliary Definitions

### Ghost list specification (LIFO)

The stack is specified via a **ghost list** `contents: erased (list t)`. The
invariant `stack_inv` ties the array contents to this ghost list:

* `top_v == L.length contents` — the top pointer equals the list length.
* `forall i < L.length contents. arr_seq[i] == L.index contents i` — array
  elements match list elements positionally.

The LIFO behavior is encoded by the push/pop specifications:
* Push appends to the end: `L.append contents [x]`
* Pop removes from the end: `L.append xs [x] == contents`

This is equivalent to a traditional stack where the top is at the end of the
list, matching the CLRS array-based stack design where `top` is an index.

## What Is Proven

1. **Functional correctness**: Push appends to top, pop removes from top, peek
   reads top — all specified via the ghost list.

2. **LIFO property**: The pure spec in `CLRS.Ch10.Stack.Spec` proves
   `fst (stack_pop (stack_push s x)) == x` and
   `snd (stack_pop (stack_push s x)) == s`.

3. **Capacity safety**: Push requires `length < capacity`, preventing overflow.

4. **Memory safety**: All array accesses are within bounds via the invariant.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **No complexity tracking.** Unlike the Ch09 algorithms, the stack operations
   do not use ghost counters. All operations are trivially O(1), so this is
   reasonable but not formally stated.

2. **Fixed capacity.** The stack has a fixed capacity set at creation time. There
   is no dynamic resizing (no amortized doubling). This matches CLRS §10.1
   which uses a fixed-size array.

3. **Append-based specification.** Push uses `L.append contents [x]`, which is
   O(n) in the ghost specification (though erased at runtime). A cons-based
   specification (with reversed logical order) would be simpler but would not
   match the physical array layout.

4. **No `free`/`destroy` operation.** The stack cannot be deallocated. Once
   created, the memory is permanently allocated.

5. **Generic but restricted to `Type0`.** The stack is polymorphic over
   `t:Type0` (not higher universes).

## Complexity

| Operation | Bound | Linked? |
|-----------|-------|---------|
| `create_stack` | O(n) (allocation) | Not tracked |
| `push` | O(1) | Not tracked |
| `pop` | O(1) | Not tracked |
| `peek` | O(1) | Not tracked |
| `stack_empty` | O(1) | Not tracked |

## Proof Structure

The proof is straightforward: each operation manipulates the array and top index,
and the invariant is maintained by construction. Supporting lemmas in
`CLRS.Ch10.Stack.Lemmas` prove the LIFO properties and size invariants at the
pure specification level.

## Files

| File | Role |
|------|------|
| `CLRS.Ch10.Stack.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch10.Stack.Impl.fst` | Pulse implementation |
| `CLRS.Ch10.Stack.Spec.fst` | Pure functional stack specification |
| `CLRS.Ch10.Stack.Lemmas.fsti` | LIFO property lemma signatures |
| `CLRS.Ch10.Stack.Lemmas.fst` | LIFO property proofs |
| `CLRS.Ch10.Stack.Test.fst` | Tests |
| `CLRS.Ch10.DS.Spec.fst` | Shared pure specs for Ch10 data structures |
