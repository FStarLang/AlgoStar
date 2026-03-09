# Queue (CLRS §10.1)

## Top-Level Signatures

Here are the top-level signatures proven about the queue operations in
`CLRS.Ch10.Queue.Impl.fsti`:

### Data Type

```fstar
noeq type queue (t:Type) = {
  data: V.vec t;
  head: B.box SZ.t;     // Front of queue (dequeue position)
  tail: B.box SZ.t;     // Next insertion point (enqueue position)
  size: B.box SZ.t;     // Current number of elements
  capacity_sz: SZ.t;    // Runtime capacity value
  capacity: erased nat;  // Ghost capacity for specification
}
```

### Invariant

```fstar
let queue_inv (#t:Type) (q: queue t) (contents: erased (list t)) : slprop = 
  exists* arr_seq head_v tail_v size_v.
    V.pts_to q.data arr_seq **
    B.pts_to q.head head_v **
    B.pts_to q.tail tail_v **
    B.pts_to q.size size_v **
    pure (
      SZ.v q.capacity_sz == reveal q.capacity /\
      SZ.v size_v == L.length contents /\
      SZ.v size_v <= reveal q.capacity /\
      SZ.v head_v < reveal q.capacity /\
      SZ.v tail_v < reveal q.capacity /\
      SZ.v tail_v == (SZ.v head_v + SZ.v size_v) % reveal q.capacity /\
      Seq.length arr_seq == reveal q.capacity /\
      reveal q.capacity > 0 /\
      (forall (i:nat). i < SZ.v size_v ==> 
        Seq.index arr_seq ((SZ.v head_v + i) % reveal q.capacity) == 
        L.index contents i)
    )
```

### Operations

```fstar
fn create_queue (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp
  requires pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns q: queue t
  ensures queue_inv q (hide []) ** 
          pure (reveal q.capacity == SZ.v capacity)

fn queue_empty (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  returns b: bool
  ensures queue_inv q contents **
          pure (b <==> L.length (reveal contents) == 0)

fn enqueue (#t:Type0) (q: queue t) (#contents: erased (list t)) (x: t)
  requires queue_inv q contents **
           pure (L.length (reveal contents) < reveal q.capacity)
  returns unit
  ensures queue_inv q (hide (L.append (reveal contents) [x]))

fn dequeue (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    queue_inv q (hide xs) **
    pure (reveal contents == x :: xs)
```

### Parameters

* `q` is the queue structure: a circular buffer (`data`), head/tail indices,
  a size counter, and capacity.

* `contents` is a ghost list capturing the logical contents in FIFO order.

### Preconditions

* `create_queue`: capacity > 0 and fits in machine size.
* `enqueue`: queue is not full (`L.length contents < capacity`).
* `dequeue`: queue is non-empty.

### Postconditions

* `enqueue`: contents become `L.append contents [x]` — element added at the end.

* `dequeue`: returns `x` such that `contents == x :: xs` — the first element is
  removed (FIFO).

* `queue_empty`: returns `true` iff the logical list is empty.

## Auxiliary Definitions

### Ghost list specification (FIFO)

The queue is specified via a **ghost list** `contents: erased (list t)`. The
invariant `queue_inv` ties the circular buffer to this ghost list:

* `size_v == L.length contents` — size matches.
* `tail_v == (head_v + size_v) % capacity` — circular buffer arithmetic.
* `forall i < size_v. arr_seq[(head_v + i) % capacity] == L.index contents i`
  — elements match in circular order.

The FIFO behavior is encoded by the enqueue/dequeue specifications:
* Enqueue appends to end: `L.append contents [x]`
* Dequeue removes from front: `contents == x :: xs`

### Design Note: 3-field vs. 2-field

CLRS §10.1 uses a 2-field design (head + tail) where an empty slot distinguishes
full from empty (at most n−1 elements in an n-slot array). This implementation
uses a 3-field design (head + tail + size) which allows the full capacity to be
used and simplifies the full/empty invariant.

## What Is Proven

1. **Functional correctness**: Enqueue adds to the back, dequeue removes from
   the front — all specified via the ghost list.

2. **FIFO property**: The pure spec in `CLRS.Ch10.Queue.Spec` and the lemma
   `lemma_queue_dequeue_preserves_contents` in `CLRS.Ch10.Queue.Lemmas` prove
   that `queue_to_list q == x :: queue_to_list q'` after dequeue.

3. **Circular buffer correctness**: The modular arithmetic invariant
   `tail == (head + size) % capacity` is maintained through all operations.

4. **Capacity safety**: Enqueue requires the queue to not be full.

5. **Memory safety**: All array accesses are within bounds via modular arithmetic.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **No complexity tracking.** All operations are O(1), but this is not formally
   stated via ghost counters.

2. **Fixed capacity.** No dynamic resizing. Matches CLRS §10.1.

3. **3-field design differs from CLRS.** CLRS uses 2 fields (head + tail) with
   capacity n−1. This uses 3 fields (head + tail + size) with full capacity.
   Functionally equivalent but structurally different.

4. **No `free`/`destroy` operation.** The queue cannot be deallocated.

5. **Append-based ghost specification.** Enqueue uses `L.append contents [x]`,
   which is O(n) in the ghost world. The pure spec (`CLRS.Ch10.Queue.Spec`)
   uses a two-list representation for efficient functional operations, but the
   imperative invariant uses a flat list.

## Complexity

| Operation | Bound | Linked? |
|-----------|-------|---------|
| `create_queue` | O(n) (allocation) | Not tracked |
| `enqueue` | O(1) | Not tracked |
| `dequeue` | O(1) | Not tracked |
| `queue_empty` | O(1) | Not tracked |

## Proof Structure

The proof maintains the circular buffer invariant through modular arithmetic.
Lemmas in `CLRS.Ch10.Queue.Lemmas` prove FIFO properties and size invariants at
the pure specification level, including the critical
`lemma_queue_dequeue_preserves_contents` which establishes the FIFO ordering.

## Files

| File | Role |
|------|------|
| `CLRS.Ch10.Queue.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch10.Queue.Impl.fst` | Pulse implementation |
| `CLRS.Ch10.Queue.Spec.fst` | Pure functional queue spec (two-list) |
| `CLRS.Ch10.Queue.Lemmas.fsti` | FIFO property lemma signatures |
| `CLRS.Ch10.Queue.Lemmas.fst` | FIFO property proofs |
| `CLRS.Ch10.Queue.Test.fst` | Tests |
| `CLRS.Ch10.DS.Spec.fst` | Shared pure specs for Ch10 data structures |
