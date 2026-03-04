# Chapter 11: Hash Tables — Rubric Compliance

**Module**: `CLRS.Ch11.HashTable`
**CLRS Scope**: §11.3–11.4 (Division-method hashing, Open addressing with linear probing)
**Date**: 2025-07-15

---

## Current File Inventory

| File | Rubric Role | Status |
|------|------------|--------|
| `CLRS.Ch11.HashTable.Spec.fst` | `Spec.fst` — Pure specification | ✅ Present |
| `CLRS.Ch11.HashTable.Refinement.fst` | `Lemmas.fst` — Refinement / correctness proofs | 🔶 Present (named `Refinement`, not `Lemmas`) |
| `CLRS.Ch11.HashTable.fst` | `Impl.fst` — Pulse implementation | 🔶 Present (named `HashTable`, not `Impl`) |
| `CLRS.Ch11.HashTable.Test.fst` | (extra) — Test harness | ✅ Present (not required by rubric) |

---

## Algorithms Covered

| Algorithm | CLRS Reference | Operations |
|-----------|---------------|------------|
| Open-addressing hash table (linear probing) | §11.4, pp. 270–272 | `hash_insert`, `hash_search`, `hash_delete` |
| Division-method hash function | §11.3.1 | `h(k) = k % m` |
| Linear probe function | §11.4, eq. on p. 272 | `h(k, i) = (h(k) + i) % m` |

---

## Rubric Compliance Matrix

| Required Artifact | Expected Name | Actual | Status | Notes |
|-------------------|---------------|--------|--------|-------|
| **Spec.fst** | `CLRS.Ch11.HashTable.Spec.fst` | `CLRS.Ch11.HashTable.Spec.fst` | ✅ | Pure assoc-list model with 15+ proven lemmas |
| **Lemmas.fst** | `CLRS.Ch11.HashTable.Lemmas.fst` | `CLRS.Ch11.HashTable.Refinement.fst` | 🔶 | Rename `Refinement` → `Lemmas`; content matches role |
| **Lemmas.fsti** | `CLRS.Ch11.HashTable.Lemmas.fsti` | — | ❌ | Extract interface from Refinement.fst |
| **Complexity.fst** | `CLRS.Ch11.HashTable.Complexity.fst` | — | ❌ | Bounds proven inline in `HashTable.fst` postconditions; no separate module |
| **Complexity.fsti** | `CLRS.Ch11.HashTable.Complexity.fsti` | — | ❌ | No interface file for complexity definitions |
| **Impl.fst** | `CLRS.Ch11.HashTable.Impl.fst` | `CLRS.Ch11.HashTable.fst` | 🔶 | Rename or split; contains impl + predicates + complexity |
| **Impl.fsti** | `CLRS.Ch11.HashTable.Impl.fsti` | — | ❌ | No public interface file for the Pulse implementation |

**Summary**: 1 ✅ / 3 🔶 / 4 ❌ → **closest chapter to compliance** but still needs restructuring.

---

## Detailed Action Items

### A1 — Rename `Refinement.fst` → `Lemmas.fst` (🔶 → ✅)

`CLRS.Ch11.HashTable.Refinement.fst` already contains the correctness bridge between Spec and Impl (probe surjectivity, `key_in_table ⟺ array_has_key`, `array_to_model` correspondence). This is exactly the `Lemmas` role.

- Rename file to `CLRS.Ch11.HashTable.Lemmas.fst`.
- Update `module` declaration.
- Update any `open` / dependency in other files (currently none import it).

### A2 — Create `Lemmas.fsti` (❌ → ✅)

Extract an interface file exposing the four main lemma signatures:

1. `lemma_linear_probe_surjective`
2. `lemma_key_in_table_iff_array_has_key`
3. `lemma_probes_not_key_full_iff`
4. `lemma_array_to_model_mem_full`

Plus the `array_has_key` and `array_to_model` definitions needed by signatures.

### A3 — Create `Complexity.fst` + `Complexity.fsti` (❌ → ✅)

Extract complexity-related content from `HashTable.fst` into a dedicated module:

- **Definitions** (move to `.fsti`):
  - `hash_insert_complexity_bounded`
  - `hash_search_complexity_bounded`
  - `hash_delete_complexity_bounded`
- **Proofs** (move to `.fst`):
  - Any standalone complexity lemmas (currently the bounds are embedded in postconditions; consider adding wrapper lemmas that state the O(n) bound as free-standing theorems).

The inline postcondition bounds (`cf - c0 <= SZ.v size`) should remain in the implementation but be proved equivalent to the definitions in `Complexity.fst`.

### A4 — Rename / split `HashTable.fst` → `Impl.fst` (🔶 → ✅)

Current `CLRS.Ch11.HashTable.fst` bundles:
- Ghost tick primitives (lines 36–46)
- Helper predicates: `key_in_table`, `key_findable`, `probes_not_key`, `valid_ht`, `seq_modified_at`
- Pure lemmas about `valid_ht` preservation (lines 165–245)
- Pulse functions: `hash_table_create`, `hash_table_free`, `hash_insert`, `hash_search`, `hash_delete`

**Option A (minimal)**: Rename to `CLRS.Ch11.HashTable.Impl.fst`, keep all content.
**Option B (clean)**: Move predicates and pure lemmas into `Lemmas.fst`; keep only Pulse code in `Impl.fst`.

Recommendation: **Option A** first (unblocks compliance), refactor to Option B later.

### A5 — Create `Impl.fsti` (❌ → ✅)

Public interface exposing:
- `hash_insert`, `hash_search`, `hash_delete` signatures
- `hash_table_create`, `hash_table_free` signatures
- Required predicates (`key_in_table`, `key_findable`, `valid_ht`, etc.)

---

## Quality Checks

### Proof Quality

| Check | Status |
|-------|--------|
| Zero `admit()` across all files | ✅ |
| Zero `assume` across all files | ✅ |
| All 3 operations proven correct | ✅ (insert, search, delete) |
| `valid_ht` invariant preserved by all ops | ✅ (create, insert, delete) |
| Refinement bridges Spec ↔ Impl | ✅ (`key_in_table ⟺ array_has_key ⟺ Spec.mem`) |
| Proofs pass `--quake 3/3` | ✅ (per audit P1-5) |

### Specification Completeness

| Property | Status |
|----------|--------|
| Insert postcondition: `key_in_table` + `key_findable` | ✅ |
| Insert postcondition: `seq_modified_at` (preserves others) | ✅ |
| Search found: slot contains key | ✅ |
| Search not-found: `¬(key_in_table)` (unconditional under `valid_ht`) | ✅ |
| Delete: marks slot `-2`, `seq_modified_at` | ✅ |
| Delete preserves `valid_ht` | ✅ |
| Worst-case O(n) complexity for all 3 ops | ✅ |
| Average-case complexity | ❌ Not addressed |
| Spec: 15 algebraic lemmas (insert/search/delete commutativity, idempotence, membership) | ✅ |

### CLRS Fidelity

| CLRS Element | Status |
|--------------|--------|
| HASH-INSERT (p. 270) | ✅ Faithful (returns `bool` instead of index — minor divergence) |
| HASH-SEARCH (p. 271) | ✅ Faithful |
| HASH-DELETE (p. 271) | ✅ Faithful (DELETED sentinel) |
| Linear probing probe sequence | ✅ `(h(k) + i) % m` |
| Division-method hash | ✅ `k % m` |
| Key-value pairs | ❌ Keys only (no satellite data) |

### Remaining Gaps (from Audit)

| ID | Item | Priority |
|----|------|----------|
| P2-1 | Return slot index from insert (match CLRS return type) | P2 |
| P2-2 | Load factor tracking (`count < size` precondition) | P2 |
| P2-4 | Key-value pair support | P2 |
| P3-5 | Type-safe sentinels (inductive `slot` type vs. magic `-1`/`-2`) | P3 |
