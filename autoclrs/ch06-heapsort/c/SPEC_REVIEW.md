# Ch06 Heapsort: C Code Specification Review

## Comparison: `CLRS.Ch06.Heap.Impl.fsti` vs `heapsort.c`

### max_heapify

| Spec (Impl.fsti)                                  | C code (heapsort.c)           | Status |
|----------------------------------------------------|-------------------------------|--------|
| `Seq.length s' == Seq.length s`                    | `_preserves_value(a._length)` | ✅ Match |
| `heaps_from s' heap_size start`                    | `_ensures(_forall(... heaps_from ...))` | ✅ Match |
| `permutation s s'`                                 | —                             | ❌ **MISSING** |
| Frame: `∀k. heap_size ≤ k < len ⟹ s'[k] = s[k]` | `_ensures(_forall(... frame ...))` | ✅ Match |
| `almost_heaps_from` precondition                   | `_requires(_forall(... almost_heaps_from ...))` | ✅ Match |
| `grandparent_ok` precondition                      | `_requires(... grandparent_ok ...)` | ✅ Match |
| Cost bound (`cf - c0 <= ...`)                      | —                             | ✅ Removed per instructions |
| `bounded` pre/postcondition (value bound)          | Present in C code             | ✅ Extra (needed for heapsort) |

### build_max_heap

| Spec (Impl.fsti)                                  | C code (heapsort.c)           | Status |
|----------------------------------------------------|-------------------------------|--------|
| `Seq.length s == Seq.length s0`                    | `_preserves_value(a._length)` | ✅ Match |
| `is_max_heap s n`                                  | `_ensures(_forall(... heaps_from 0 ...))` | ✅ Match (heaps_from 0 ≡ is_max_heap) |
| `permutation s0 s`                                 | —                             | ❌ **MISSING** |
| Frame: `∀k. n ≤ k < len ⟹ s[k] = s0[k]`         | `_ensures(_forall(... frame ...))` | ✅ Match |
| `SZ.fits(2*len+2)` preserved                       | Implicit via `_preserves_value(a._length)` | ✅ Match |
| Cost bound (`cf - c0 <= ...`)                      | —                             | ✅ Removed per instructions |

### heapsort

| Spec (Impl.fsti)                                  | C code (heapsort.c)           | Status |
|----------------------------------------------------|-------------------------------|--------|
| `Seq.length s == Seq.length s0`                    | `_preserves_value(a._length)` | ✅ Match |
| `sorted_upto s n`                                  | `_ensures(_forall(... a[k] <= a[k+1] ...))` | ✅ Match (adjacent ≡ sorted_upto) |
| `permutation s0 s`                                 | —                             | ❌ **MISSING** |
| Frame: `∀k. n ≤ k < len ⟹ s[k] = s0[k]`         | `_ensures(_forall(... frame ...))` | ✅ Match |
| Cost bound (`cf - c0 <= ...`)                      | —                             | ✅ Removed per instructions |

## Summary of Gaps

The **only** specification gap is the **`permutation`** postcondition, missing from
all three functions. Without it, the C code proves:
- Memory safety and array bounds
- Max-heap property
- Sortedness
- Frame preservation

But does NOT prove that sorting preserves the multiset of elements (i.e., doesn't
"cheat" by zeroing or duplicating elements).

## Plan to Fix

### Approach

Use `FStar.Seq.Properties.permutation` over `Seq.seq (option Int32.t)` (the c2pulse
array representation). Express permutation postconditions via `_inline_pulse` with
`old(array_value_of(...))` to capture the pre-state sequence.

### Bridge Lemmas Needed (in `CLRS.Ch06.Heap.C.BridgeLemmas`)

1. **`swap_option_seq_eq`**: Show that c2pulse's two-step swap produces the same
   result as `SeqP.swap`.
2. **`swap_option_perm`**: Swapping two elements gives a permutation
   (wraps `SeqP.lemma_swap_permutes`).
3. **`option_perm_trans`**: Transitivity of permutation for composing swap + recursive call.
4. **`option_perm_refl`**: Reflexivity (no-swap case).

### Changes to `heapsort.c`

1. **max_heapify**: Add `_ensures((bool) _inline_pulse(permutation postcondition))`.
   Add `_ghost_stmt` calls after swap and after recursive call for proof steps.
2. **build_max_heap**: Add permutation postcondition and loop invariant.
3. **heapsort**: Add permutation postcondition and loop invariant.

### Representation Bridge

The c2pulse representation uses `Seq.seq (option Int32.t)` while Impl.fsti uses
`Seq.seq int`. The bridge lemmas in `CLRS.Ch06.Heap.C.BridgeLemmas` already handle
this conversion (via `extract_ints`) for the root dominance property. The same
pattern applies for permutation.
