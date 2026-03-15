# Huffman Coding (CLRS §16.3)

## Top-Level Signature

Here is the top-level signature proven about Huffman tree construction in
`CLRS.Ch16.Huffman.Impl.fsti`:

```fstar
fn huffman_tree
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to freqs freq_seq **
           GR.pts_to ctr c0 **
           pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    SZ.fits (2 * SZ.v n + 2) /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0))
  returns result: hnode_ptr
  ensures A.pts_to freqs freq_seq **
          (exists* ft (cf: nat). is_htree result ft **
                  GR.pts_to ctr cf **
                  pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
                        HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
                        HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0) /\
                        HCmplx.huffman_merge_bound cf (reveal c0) (SZ.v n)))
```

### Parameters

* `freqs` is a mutable array of `int` containing positive frequencies for
  `n` symbols.

* `n` is the number of symbols.

* `ctr` is a ghost counter for merge iterations.

### Preconditions

* `SZ.v n > 0`: At least one symbol.

* `SZ.fits (2 * SZ.v n + 2)`: Size bound for internal node allocation
  (a Huffman tree with `n` leaves has `n-1` internal nodes, so `2n-1`
  nodes total, plus some overhead).

* All frequencies are positive.

### Postcondition

The result is a heap-allocated Huffman tree `ft` satisfying:

* `HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0)` — The
  tree's cost (sum of internal node frequencies) equals the greedy algorithm's
  cost.

* `HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0)` — The
  tree's leaf frequencies form the same multiset as the input.

* `HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)` — The tree
  minimizes weighted path length over all trees with the same frequency
  multiset.

* `HCmplx.huffman_merge_bound cf (reveal c0) (SZ.v n)` — Exactly `n-1`
  merge iterations were performed (linked via ghost counter).

## Auxiliary Definitions

### `htree` (from `CLRS.Ch16.Huffman.Spec`)

```fstar
type htree =
  | Leaf : sym:nat -> freq:pos -> htree
  | Internal : freq:pos -> left:htree -> right:htree -> htree
```

A Huffman tree is either a leaf (symbol + frequency) or an internal node
(frequency + two children). All frequencies are positive (`pos`).

### `cost` (from `CLRS.Ch16.Huffman.Spec`)

```fstar
let rec cost_aux (t: htree) : nat =
  match t with
  | Leaf _ _ -> 0
  | Internal _ l r -> freq_of l + freq_of r + cost_aux l + cost_aux r

let cost (t: htree) : nat = cost_aux t
```

The cost is the sum of all internal node frequencies. CLRS proves this
equals the weighted path length (`wpl_equals_cost`):

```fstar
let wpl_equals_cost (t: htree)
  : Lemma (ensures weighted_path_length t == cost t)
  = wpl_cost_relation t 0
```

### `same_frequency_multiset` and `is_wpl_optimal` (from `CLRS.Ch16.Huffman.Spec`)

```fstar
let same_frequency_multiset (t: htree) (freqs: list pos) : prop =
  forall (x: pos). count x (leaf_freqs t) = count x freqs

let is_wpl_optimal (t: htree) (freqs: list pos) : prop =
  same_frequency_multiset t freqs /\
  (forall (t': htree). same_frequency_multiset t' freqs ==>
    weighted_path_length t <= weighted_path_length t')
```

Optimality is stated as: the tree has the correct leaf frequency multiset,
and its weighted path length is ≤ that of any other tree with the same
multiset. This is the strongest possible optimality statement.

### `greedy_cost` (from `CLRS.Ch16.Huffman.Optimality`)

```fstar
val greedy_cost (freqs: list pos) : Tot nat
```

The cost of the greedy merging strategy: repeatedly merge the two
smallest-frequency trees. Key lemmas:

* `greedy_cost_multiset_invariant`: Greedy cost is invariant under multiset
  equality of the frequency list.

* `greedy_cost_implies_optimal`: If `cost(ft) == greedy_cost(freqs)` and
  `same_frequency_multiset ft freqs`, then `is_wpl_optimal ft freqs`.

### `is_htree` (from `CLRS.Ch16.Huffman.Impl`)

```fstar
val is_htree (p: hnode_ptr) (ft: HSpec.htree) : Tot slprop
```

A recursive separation logic predicate relating a heap-allocated tree
structure to its pure spec tree. This is the core abstraction predicate
for the imperative implementation.

## What Is Proven

1. **Multiset preservation** (`same_frequency_multiset`): The constructed
   tree's leaf frequencies are exactly the input frequencies (as a multiset).

2. **Cost equality** (`cost ft == greedy_cost`): The tree's cost matches
   the greedy algorithm's theoretical cost.

3. **WPL optimality** (`is_wpl_optimal`): The tree minimizes weighted path
   length among all trees with the same frequency multiset. This is the
   **strongest possible optimality guarantee**.

4. **Encode/decode round-trip** (in `CLRS.Ch16.Huffman.Codec`):
   ```fstar
   val encode_decode_roundtrip (t: htree) (msg: list nat)
     : Lemma (requires Internal? t /\ Some? (encode t msg))
             (ensures (let Some bits = encode t msg in
                       decode t bits == Some msg))

   val decode_encode_roundtrip (t: htree) (bits: list bool)
     : Lemma (requires Internal? t /\ wf_htree t /\ Some? (decode t bits))
             (ensures (let Some msg = decode t bits in
                       Some? (encode t msg) /\
                       (let Some bits' = encode t msg in bits == bits')))
   ```
   Both directions of the round-trip are proven. Encode→decode needs only
   `Internal? t` (prefix-free is structural). Decode→encode additionally
   needs `wf_htree t` (no duplicate symbols) for uniqueness.

5. **Imperative codec** (in `CLRS.Ch16.Huffman.Codec.Impl`): Pulse
   implementations of `decode_step_impl`, `decode_impl`, `codeword_impl`,
   and `encode_impl` are proven to match the pure codec specifications.

**Zero admits, zero assumes.** A thorough search of all Huffman-related
files (`Impl.fst`, `Impl.fsti`, `Codec.fst`, `Codec.fsti`, `Codec.Impl.fst`,
`Codec.Impl.fsti`, `Optimality.fst`, `Optimality.fsti`, `PQForest.fst`,
`PQForest.fsti`, `PQLemmas.fst`, `PQLemmas.fsti`, `ForestLemmas.fst`,
`ForestLemmas.fsti`, `Defs.fst`, `Spec.fst`, `Complete.fst`,
`Complexity.fst`, `Complexity.fsti`) found **zero** `admit`, `assume`, or
`assume_` calls.

## Specification Gaps and Limitations

1. ~~**No complexity ghost counter.**~~ **ADDRESSED.** The Huffman Pulse
   implementation now carries a ghost tick counter (`ctr: GR.ref nat`)
   that is incremented once per merge iteration. The postcondition includes
   `huffman_merge_bound cf c0 n`, proving exactly `n-1` merge iterations.
   With a min-heap PQ, each iteration is O(log n), giving O(n log n) total.

2. **Priority queue abstraction.** The implementation uses
   `Pulse.Lib.PriorityQueue`, an external library. The PQ's correctness
   is assumed via its own interface (`PQ.is_minimum`, `PQ.extends`). The
   Huffman proof trusts these PQ specifications.

3. **`n > 0` only; no degenerate cases.** A single symbol (`n = 1`)
   produces a Leaf, not an Internal node. The codec round-trip requires
   `Internal? t`, so encoding/decoding with a single-symbol tree is not
   supported. CLRS's algorithm also assumes `n ≥ 2` for the priority queue
   merge loop.

4. **Symbol assignment.** The implementation assigns `sym = SZ.v idx`
   (the array index) as the symbol for each leaf. This means symbol identity
   is determined by position in the input array, not by any external label.

5. **`seq_to_pos_list` clamping.** The conversion from `Seq.seq int` to
   `list pos` clamps non-positive values to 1:
   ```fstar
   let v : pos = if Seq.index s k > 0 then Seq.index s k else 1 in
   ```
   The precondition requires all frequencies to be positive, so this
   clamping is never triggered in practice, but it is a defensive measure
   rather than a type-level guarantee.

6. **Forest-based proof complexity.** The proof tracks a ghost forest of
   intermediate trees using `merge_bundle`, `init_bundle`, and extensive
   list/multiset reasoning via `PQForest` and `ForestLemmas`. This is
   among the most complex proofs in the repository.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Merge iterations | O(n) = n−1 | ✅ Ghost counter | Exact count |
| PQ operations | O(n log n) | ⚠️ PQ abstracted | — |

The merge iteration count is **fully linked** to the imperative
implementation: the ghost counter `ctr` is incremented once per merge
iteration (iterations 0 through n-2), giving exactly `n-1` merges.
Each merge performs 3 PQ operations (2 extract-min + 1 insert), so with
a binary heap the total is O(n log n). The PQ operation cost is not
individually tracked since it depends on the PQ implementation.

## Proof Structure

The proof proceeds in two phases:

**Phase 1 (Initialization):** Build a priority queue of `n` single-leaf
trees, maintaining `init_bundle` — an opaque predicate bundling PQ validity,
forest structure, multiset preservation, and cost tracking.

**Phase 2 (Merge loop):** Repeatedly extract the two minimum-frequency
trees and merge them, maintaining `merge_bundle` — which additionally
tracks `forest_total_cost + greedy_cost(forest_root_freqs) == greedy_cost(input)`.
The key insight is `greedy_cost_unfold_with_mins`: extracting two minima
and merging them advances the greedy cost by exactly `f1 + f2`.

After the loop, a single tree remains. The bridge lemma
`greedy_cost_implies_optimal` converts the cost equality into WPL optimality.

## Files

| File | Role |
|------|------|
| `CLRS.Ch16.Huffman.Impl.fsti` | Public interface (tree construction) |
| `CLRS.Ch16.Huffman.Impl.fst` | Pulse implementation |
| `CLRS.Ch16.Huffman.Spec.fst` | `htree`, `cost`, `weighted_path_length`, `is_wpl_optimal` |
| `CLRS.Ch16.Huffman.Defs.fst` | PQ entry types, forest types, helper functions |
| `CLRS.Ch16.Huffman.Optimality.fsti` | `greedy_cost`, bridge lemmas |
| `CLRS.Ch16.Huffman.Optimality.fst` | Optimality proofs |
| `CLRS.Ch16.Huffman.PQForest.fsti` | PQ-forest interaction lemmas |
| `CLRS.Ch16.Huffman.PQForest.fst` | PQ-forest proofs |
| `CLRS.Ch16.Huffman.PQLemmas.fsti` | PQ multiset/validity lemmas |
| `CLRS.Ch16.Huffman.PQLemmas.fst` | PQ lemma proofs |
| `CLRS.Ch16.Huffman.ForestLemmas.fsti` | Forest manipulation lemmas |
| `CLRS.Ch16.Huffman.ForestLemmas.fst` | Forest lemma proofs |
| `CLRS.Ch16.Huffman.Complete.fst` | Pure Huffman construction + optimality proof |
| `CLRS.Ch16.Huffman.Codec.fsti` | Pure encode/decode interface |
| `CLRS.Ch16.Huffman.Codec.fst` | Pure encode/decode implementation + round-trip |
| `CLRS.Ch16.Huffman.Codec.Impl.fsti` | Pulse codec interface |
| `CLRS.Ch16.Huffman.Codec.Impl.fst` | Pulse codec implementation |
| `CLRS.Ch16.Huffman.Complexity.fsti` | Complexity interface |
| `CLRS.Ch16.Huffman.Complexity.fst` | Complexity proofs |
