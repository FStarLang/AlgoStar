# Ch11 Hash Table — C vs Impl.fsti Specification Review

## Overview

This document compares the C code specifications (in `HashTable.c`) against the
verified Pulse specifications in `CLRS.Ch11.HashTable.Impl.fsti`. The C code uses
c2pulse annotations and operates on `Int32.t` arrays via `Seq.seq (option Int32.t)`,
while the Impl.fsti uses `Seq.seq int`. Bridge lemmas in `BridgeLemmas.fst` handle
the representation change.

**Convention**: ✅ = at parity, ⚠️ = weaker but present, ❌ = missing entirely.

---

## 1. hash_search / hash_search_probe

### Impl.fsti postconditions:
1. `result <= size` ✅
2. `result < size ==> Seq.index s result == key` ✅
3. `result == size ==> ~(key_in_table s size key)` ✅ (fixed via `c_key_in_table` bridge + `_ghost_stmt`)
4. Table unchanged (preserves) ✅
5. `valid_ht` preserved ✅
6. Complexity: `cf - c0 <= size` — N/A (no ghost counters in c2pulse)

### Resolution:
- **Item 3**: Added `c_key_in_table` predicate in BridgeLemmas and
  `lemma_probe_absent_not_in_table` bridge lemma. hash_search_probe calls the
  lemma via `_ghost_stmt` when hitting an empty slot (-1) or exhausting probes.
  hash_search propagates `~(c_key_in_table)` on not-found.

---

## 2. hash_insert_probe / hash_insert

### Impl.fsti postconditions (on success, result=true):
1. `key_in_table s' size key` ✅ (fixed via `c_key_in_table` bridge)
2. `key_findable s' size key` ✅ (fixed via `c_key_findable` bridge + `lemma_valid_key_findable`)
3. `∃idx. idx < size ∧ (old slot was -1 or -2) ∧ new slot == key ∧ seq_modified_at` ✅ (strengthened `_exists` + `_forall` unchanged slots)
4. `valid_ht` preserved ✅

### Impl.fsti postconditions (on failure, result=false):
5. `s' == s` (table unchanged) ✅
6. All probe positions occupied (neither -1 nor -2) ✅ (added probe-based all-occupied postcondition)

### Resolution:
- Success: Strengthened `_exists` to include `_old(table[k]) == -1 || _old(table[k]) == -2`.
  Added `_forall(j, table[j] != _old(table[j]) ==> table[j] == key)` for unchanged-slot tracking.
  Added `c_key_in_table` and `c_key_findable` postconditions with `_ghost_stmt` for
  `lemma_valid_key_findable`.
- Failure: Added probe-based all-occupied postcondition via `_inline_pulse`.

---

## 3. hash_delete

### Impl.fsti postconditions (on success, result=true):
1. `∃idx. idx < size ∧ old slot == key ∧ new slot == -2` ✅
2. Unchanged slots: `_forall(k, table[k] != _old(table[k]) ==> _old(table[k]) == key && table[k] == -2)` ✅ (added)
3. `valid_ht` preserved ✅

### Impl.fsti postconditions (on failure, result=false):
4. `Seq.equal s' s` ✅
5. `~(key_in_table s size key)` ✅ (fixed via `c_key_in_table` bridge, inherited from hash_search)

### Resolution:
- Success: Added unchanged-slot tracking via `_forall`.
- Failure: Added `~(c_key_in_table)` postcondition, derived from hash_search's not-found result.

---

## 4. hash_insert_no_dup

### Impl.fsti postconditions (on success):
1. `key_in_table s' size key` ✅ (fixed)
2. `key_findable s' size key` ✅ (fixed, with `_ghost_stmt` for already-present case)
3. Unchanged slots on failure ✅
4. `valid_ht` preserved ✅

### Impl.fsti postconditions (on failure):
5. `s' == s` (all slots unchanged) ✅
6. `~(key_in_table s size key)` ⚠️ (not directly stated — indirectly implied by unchanged slots + hash_search result, but not expressible without a sequence-equality bridge lemma)

### Resolution:
- Success: Added `c_key_in_table` and `c_key_findable` postconditions. Added
  `_ghost_stmt(lemma_valid_key_findable ...)` in the early-return (already-present) branch.
- Failure `~(c_key_in_table)`: Omitted because proving it requires connecting
  "pointwise equal sequences ⟹ same c_key_in_table" across the hash_insert call
  boundary, which would need a new sequence-equality bridge lemma. The unchanged-slots
  postcondition (`_forall(k, k < size ==> table[k] == _old(table[k]))`) plus the
  hash_search not-found result together imply key absence semantically.

---

## 5. Complexity Bounds

All Impl.fsti functions have complexity bounds via ghost counter (`cf - c0 <= size`).
These are intentionally omitted in the C code because c2pulse does not support ghost
references. The Impl.fsti proofs cover complexity. **No action needed.**

---

## 6. No Computationally Relevant Code in `_include_pulse`

✅ The `_include_pulse` blocks only contain `open` statements for modules.
No implementation code is inside `_include_pulse` blocks.

---

## Bridge Lemmas Added

| Lemma / Predicate | Purpose |
|---|---|
| `c_key_in_table s size key` | c2pulse-level predicate: ∃i < size. seq_val s i == key |
| `c_key_findable s size key` | c2pulse-level predicate: ∃p < size. seq_val s (hash_probe_nat key p size) == key ∧ probes_not_key before p |
| `c_seq_modified_at s s' idx` | c2pulse-level predicate: only slot idx differs between s and s' |
| `lemma_probe_absent_not_in_table` | probe-based absence (∀p. seq_val at probe ≠ key) ⟹ ~(c_key_in_table) |
| `lemma_valid_key_findable` | c_valid_ht + c_key_in_table ⟹ c_key_findable |

---

## Remaining Gaps (Intentional)

1. **Complexity bounds** — c2pulse lacks ghost references
2. **hash_insert_no_dup failure `~(c_key_in_table)`** — needs sequence-equality bridge
3. **Distinguishing already-present vs fresh insert** in hash_insert_no_dup success — complex to express in c2pulse annotations
