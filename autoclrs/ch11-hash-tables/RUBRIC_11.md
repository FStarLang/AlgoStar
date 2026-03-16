# Chapter 11: Hash Tables — Rubric Compliance

**Module**: `CLRS.Ch11.HashTable`
**CLRS Scope**: §11.3–11.4 (Division-method hashing, Open addressing with linear probing)
**Last updated**: 2026-03-16

---

## Current File Inventory

| File | Rubric Role | Status |
|------|------------|--------|
| `CLRS.Ch11.HashTable.Spec.fst` | `Spec.fst` — Pure specification | ✅ Present |
| `CLRS.Ch11.HashTable.Impl.fsti` | `Impl.fsti` — Public interface | ✅ Present |
| `CLRS.Ch11.HashTable.Impl.fst` | `Impl.fst` — Pulse implementation | ✅ Present |
| `CLRS.Ch11.HashTable.Lemmas.fsti` | `Lemmas.fsti` — Refinement bridge interface | ✅ Present |
| `CLRS.Ch11.HashTable.Lemmas.fst` | `Lemmas.fst` — Refinement bridge proofs | ✅ Present |
| `CLRS.Ch11.HashTable.Complexity.fsti` | `Complexity.fsti` — Complexity definitions | ✅ Present |
| `CLRS.Ch11.HashTable.Complexity.fst` | `Complexity.fst` — Complexity proofs | ✅ Present |
| `CLRS.Ch11.HashTable.Test.fst` | (extra) — Test harness | ✅ Present (not required by rubric) |

---

## Algorithms Covered

| Algorithm | CLRS Reference | Operations |
|-----------|---------------|------------|
| Open-addressing hash table (linear probing) | §11.4, pp. 270–272 | `hash_insert`, `hash_search`, `hash_delete`, `hash_insert_no_dup` |
| Division-method hash function | §11.3.1 | `h(k) = k % m` |
| Linear probe function | §11.4, eq. on p. 272 | `h(k, i) = (h(k) + i) % m` |

---

## Rubric Compliance Matrix

| Required Artifact | Expected Name | Status | Notes |
|-------------------|---------------|--------|-------|
| **Spec.fst** | `CLRS.Ch11.HashTable.Spec.fst` | ✅ | Pure assoc-list model with 15+ proven lemmas |
| **Lemmas.fst** | `CLRS.Ch11.HashTable.Lemmas.fst` | ✅ | 8 refinement bridge lemmas connecting Spec ↔ Impl |
| **Lemmas.fsti** | `CLRS.Ch11.HashTable.Lemmas.fsti` | ✅ | Interface with all 8 lemma signatures |
| **Complexity.fst** | `CLRS.Ch11.HashTable.Complexity.fst` | ✅ | Slot counting, insert/delete slot-balance proofs |
| **Complexity.fsti** | `CLRS.Ch11.HashTable.Complexity.fsti` | ✅ | Interface with complexity definitions and signatures |
| **Impl.fst** | `CLRS.Ch11.HashTable.Impl.fst` | ✅ | Pulse implementation of all 4 operations |
| **Impl.fsti** | `CLRS.Ch11.HashTable.Impl.fsti` | ✅ | Public interface: types, predicates, signatures |

**Summary**: 7 ✅ / 0 🔶 / 0 ❌ → **fully compliant with rubric**

---

## Quality Checks

### Proof Quality

| Check | Status |
|-------|--------|
| Zero `admit()` across all files | ✅ |
| Zero `assume` across all files | ✅ |
| All 4 operations proven correct | ✅ (insert, insert_no_dup, search, delete) |
| `valid_ht` invariant preserved by all ops | ✅ (create, insert, delete) |
| Refinement bridges Spec ↔ Impl | ✅ (`key_in_table ⟺ array_has_key ⟺ Spec.mem`) |
| Key uniqueness + delete guarantees absence | ✅ |
| z3rlimits optimized (max 120, down from 200) | ✅ |

### Specification Completeness

| Property | Status |
|----------|--------|
| Insert postcondition: `key_in_table` + `key_findable` | ✅ |
| Insert postcondition: `seq_modified_at` (preserves others) | ✅ |
| Insert-no-dup: search + conditional insert, uniqueness | ✅ |
| Search found: slot contains key | ✅ |
| Search not-found: `¬(key_in_table)` (unconditional under `valid_ht`) | ✅ |
| Delete: marks slot `-2`, `seq_modified_at` | ✅ |
| Delete preserves `valid_ht` | ✅ |
| Worst-case O(n) complexity for all operations | ✅ |
| Slot counting (empty/deleted/available) | ✅ |
| Average-case complexity | ❌ Not addressed (requires probabilistic model) |

### CLRS Fidelity

| CLRS Element | Status |
|--------------|--------|
| HASH-INSERT (p. 270) | ✅ Faithful (returns `bool` instead of index — minor divergence) |
| HASH-SEARCH (p. 271) | ✅ Faithful |
| HASH-DELETE (p. 271) | ✅ Faithful (DELETED sentinel) |
| Linear probing probe sequence | ✅ `(h(k) + i) % m` |
| Division-method hash | ✅ `k % m` |
| Key-value pairs | ❌ Keys only (no satellite data) |

### Remaining Gaps

| ID | Item | Priority |
|----|------|----------|
| P2-1 | Return slot index from insert (match CLRS return type) | P2 |
| P2-2 | Load factor tracking (`count < size` precondition) | P2 |
| P2-4 | Key-value pair support | P2 |
| P3-5 | Type-safe sentinels (inductive `slot` type vs. magic `-1`/`-2`) | P3 |
