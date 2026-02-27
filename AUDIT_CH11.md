# Audit Report — Chapter 11: Hash Tables

**Module**: `CLRS.Ch11.HashTable` (+ `.Spec`, `.Test`)
**Date**: 2025-07-15
**Scope**: CLRS §11.4 Open Addressing with Linear Probing
**Verdict**: Mostly faithful to CLRS; strong proofs; significant functional gaps remain

---

## 1. CLRS Fidelity

### Collision Resolution Strategy
- **Implemented**: Open addressing with **linear probing** (CLRS §11.4).
- Hash function: `h(k) = k % m` (division method, CLRS §11.3.1).
- Probe function: `h(k, i) = (h(k) + i) % m` (CLRS eq. for linear probing, p. 272).
- Both match the textbook definitions exactly.

### HASH-INSERT (CLRS p. 270)

| CLRS Pseudocode | Implementation | Match? |
|---|---|---|
| `i = 0` | `let mut i = 0sz` | ✅ |
| `repeat j = h(k, i)` | `let idx = hash_probe key vi size` | ✅ |
| `if T[j] == NIL: T[j] = k; return j` | Checks `slot = -1 ∥ slot = -2`, writes key | ✅ (extended for DELETED) |
| `else i = i + 1` | `i := SZ.add vi 1sz` | ✅ |
| `until i == m` | Loop guard `vi <^ size` | ✅ |
| `error "hash table overflow"` | Returns `false` | ✅ (different signalling) |
| Returns slot index `j` | Returns `bool` | ⚠️ Diverges — CLRS returns the index |

**Differences**:
1. CLRS `HASH-INSERT` returns the slot index; the implementation returns a `bool`.
2. The implementation correctly extends NIL-check to also accept DELETED slots (`-2`), matching the CLRS recommendation on p. 271 ("modify HASH-INSERT to treat such a slot as if it were empty").
3. **Unconditional write pattern** (line 177): the code always writes to the slot (`A.op_Array_Assignment table idx new_val`), computing a no-op write when `can_insert` is false. This is a Pulse workaround for conditional side effects and does not affect functional correctness (the written value equals the read value), but it is a departure from the CLRS pseudocode's guarded write and could matter for concurrent settings or hardware with write-sensitive memory.

### HASH-SEARCH (CLRS p. 271)

| CLRS Pseudocode | Implementation | Match? |
|---|---|---|
| `i = 0` | `let mut i = 0sz` | ✅ |
| `repeat j = h(k, i)` | `let idx = hash_probe key vi size` | ✅ |
| `if T[j] == k: return j` | `is_found = (slot = key)` → updates `found_idx` | ✅ |
| `i = i + 1` | `i := SZ.add vi 1sz` | ✅ |
| `until T[j] == NIL or i == m` | `done := is_found ∥ is_empty`; loop guard `vi <^ size` | ✅ |
| `return NIL` | Returns `size` (sentinel for not-found) | ✅ (equivalent) |

**Faithful** to CLRS. The search correctly stops on empty (`-1`) but **does not stop on deleted (`-2`)** slots, matching the CLRS specification: "We do not need to modify HASH-SEARCH, since it will pass over DELETED values while searching" (p. 271).

### HASH-DELETE — **MISSING** ❌

CLRS discusses deletion with DELETED markers (p. 271). The implementation:
- Defines `-2` as the deleted sentinel (line 31).
- `hash_insert` treats `-2` as insertable (line 173).
- `hash_search` correctly skips `-2` (line 271 — only stops on `-1`).
- **But no `hash_delete` function is implemented.** The infrastructure for deletion is partially present (sentinel is defined, insert/search handle it) but the actual operation is absent.

---

## 2. Specification Strength

### Pure Spec (`CLRS.Ch11.HashTable.Spec`)
The Spec module provides a **pure association-list model** with:
- `ht_insert`, `ht_search`, `ht_delete` over `list (nat & int)`.
- 15 lemmas proving algebraic properties (insert-search, delete-search, commutativity, idempotence, membership).
- All lemmas are fully proven (no admits).

**Critical gap**: The Spec module is **completely disconnected** from the Pulse implementation. There is:
- No `open CLRS.Ch11.HashTable.Spec` in either the implementation or test files.
- No refinement proof linking the array-based open-addressing table to the association-list model.
- No abstraction relation between the concrete array state and the abstract `ht_model`.

This means the Spec is a self-contained algebraic exercise but provides **zero assurance** about the actual Pulse implementation.

### Implementation Postconditions

**`hash_insert`** (lines 128–136):
- `key_in_table s' (SZ.v size) key` when successful — key exists somewhere in the probe sequence.
- `s' == s` when table is full — table unchanged.
- Complexity: `cf - c0 <= SZ.v size`.

**`hash_search`** (lines 215–227):
- If `result < size`, then `Seq.index s result == key` — found slot contains key.
- Table unchanged (`A.pts_to table s` in postcondition).
- Complexity: `cf - c0 <= SZ.v size`.

### Specification Weaknesses

| Gap | Severity | Notes |
|---|---|---|
| No insert-then-search round-trip lemma | **High** | Cannot prove that after inserting key `k`, `hash_search` finds `k`. The `key_in_table` predicate says the key *exists* somewhere, but not that search will find it. |
| No key preservation (insert doesn't clobber) | **High** | No guarantee that inserting `k1` preserves findability of previously inserted `k2`. The `seq_modified_at` predicate (line 109) is defined but never used. |
| `key_in_table` is weak | **Medium** | Only asserts existential: "some probe position holds key." Doesn't relate to the specific probe sequence that `hash_search` follows. |
| No load factor / fill tracking | **Medium** | No count of occupied slots; no precondition like `α < 1`. |
| `probes_not_key` not used in insert | **Low** | Defined (line 92) but only used in search invariant; could strengthen insert. |
| Keys restricted to non-negative `int` | **Low** | Conflates key space with sentinel space. CLRS uses a separate type for keys vs. NIL/DELETED. |
| No value storage | **Medium** | CLRS hash tables store key-value pairs; this stores keys only. |

---

## 3. Complexity Analysis

### What Is Proven
- **Insert**: `cf - c0 <= SZ.v size` — at most `n` probes (one tick per iteration).
- **Search**: `cf - c0 <= SZ.v size` — at most `n` probes.
- Ghost tick counter (`GR.ref nat`) is erased at extraction time.

### Assessment

| Property | Status |
|---|---|
| Worst-case O(n) probes | ✅ Verified via ghost counter |
| Average-case O(1) with load factor < 1 | ❌ Not addressed |
| Amortized analysis | ❌ Not addressed |
| Pure tautology lemmas (lines 293–311) | ⚠️ `hash_insert_worst n = n` proves `n <= n`, which is vacuous |

The pure "complexity lemmas" at lines 293–311 are trivial tautologies that add no insight:
```fstar
let hash_insert_worst (n: nat) : nat = n
let hash_insert_linear (n: nat) : Lemma (hash_insert_worst n <= n) = ()
```
These should either be removed or replaced with meaningful asymptotic bounds.

---

## 4. Code Quality

### Strengths
- Clean separation of ghost tick logic from functional code.
- Loop invariants are well-structured with separate correctness and complexity components.
- Proper use of Pulse idioms: `exists*` witnesses, pure propositions, ghost references.
- Consistent naming: `hash_probe`, `hash_probe_nat`, `key_in_table`.
- No redundant code.

### Issues

| Issue | Location | Severity |
|---|---|---|
| Unconditional write in insert body | Line 177 | Low — correct but wasteful; adds unnecessary array writes when slot is occupied |
| `SZ.fits key` precondition leak | Lines 59, 63, 126 | Low — implementation detail exposed to caller; could hide behind a wrapper |
| No table creation/destruction helpers | — | Medium — Test file has 10+ lines of boilerplate for alloc/free |
| No resize / dynamic table | — | Medium — CLRS §11.4 assumes fixed-size, but practical use requires growth |
| `inserted` flag redundant with `done` | Lines 139–140 | Low — could use one flag + found index, but current form aids clarity |
| Mixed int sentinels | Line 31 | Medium — type safety relies on convention, not types |

---

## 5. Proof Quality

### Admits and Assumes

**No `admit()` or `assume` found in any of the three files.** All proofs are complete. ✅

### Proof Techniques

| Technique | Usage |
|---|---|
| SMT (`z3rlimit 100`) | Insert and search (lines 114, 201) |
| Ghost references | Tick counter for complexity |
| Separation logic invariants | Loop invariants in both operations |
| Fuel/ifuel hints | `--fuel 2 --ifuel 1` for both loops |
| Explicit lemma assertions | `assert pure (lemma_hash_probe_consistent ...)` at line 179 |

### Proof Robustness Concerns
1. **z3rlimit 100** is moderate but not excessive. The proofs may be sensitive to Z3 version changes; no `--retry` or `--quake` testing noted.
2. The insert invariant `(vinserted == false ==> Seq.equal st s)` (line 158) is strong: it says the table is *completely unchanged* before the first insertion. This is correct due to the unconditional-write-of-same-value pattern, but relies on Z3 reasoning about `Seq.equal` after a write of the same value.
3. The Spec module proofs are all by structural induction on the association list — clean and robust.

---

## 6. Documentation & Comments

### README.md
- Accurate description of the data structure, operations, and sentinel values. ✅
- Build instructions reference a stale path (`/home/nswamy/workspace/clrs/ch11-hash-tables`). ❌
- Claims "Functional correctness — Operations implement CLRS linear probing algorithm" — this is partially true but overstated given the missing insert-search round-trip proof.

### Module Header (lines 1–14)
- States "NO admits. NO assumes." — **verified correct**. ✅
- Lists operations and complexity — accurate.
- Does not mention the missing `hash_delete`.

### Inline Comments
- Sentinel values clearly documented (line 31).
- Each code section has section headers (`========== ... ==========`).
- Loop body steps have one-line comments — good.
- `SNIPPET_START/END` markers present for documentation extraction.

---

## 7. Task List

### Priority 1 — Critical (Specification Completeness)

- [x] **P1-1: Implement `hash_delete`**. Define `fn hash_delete` that marks a slot with `-2` (DELETED). Prove postcondition: after delete, `hash_search` for the deleted key returns `size` (not found). This completes the CLRS §11.4 operation set.
- [x] **P1-2: Prove that when search fails the key is not present in the table**. Strengthened `hash_search` postcondition: when not found, either `~(key_in_table s size key)` (all probes exhausted) or empty slot reached with `probes_not_key` up to that point. Added `lemma_probes_not_key_full` with SMTPat.
- [x] **P1-3: Prove insert preserves existing keys**. `hash_insert` postcondition now includes `seq_modified_at s s' idx` proving only one slot changed, plus the original slot was empty/deleted. Any other key at any other position is preserved.
- [ ] **P1-4: Connect Spec to implementation**. Define an abstraction relation `repr : Seq.seq int → ht_model → prop` and prove that `hash_insert` / `hash_search` / `hash_delete` refine the pure `ht_insert` / `ht_search` / `ht_delete` from `CLRS.Ch11.HashTable.Spec`. *(Blocked: requires P2-4 or a key-only Spec adaptation first, since Spec uses key-value pairs but implementation stores keys only.)*

### Priority 2 — Important (Robustness & Completeness)

- [ ] **P2-1: Return slot index from insert** (like CLRS). Change `hash_insert` return type from `bool` to `SZ.t`, returning the slot index on success and `size` on failure. This matches the CLRS pseudocode and enables callers to use the result.
- [ ] **P2-2: Add load factor tracking**. Maintain a ghost (or concrete) count of non-empty slots. Add precondition `count < size` for insert to guarantee success, or prove that insert succeeds iff a free slot exists in the probe sequence.
- [ ] **P2-3: Remove trivial complexity tautologies** (lines 293–311) or replace with meaningful bounds (e.g., relating probe count to load factor `α`). ✅ *Done: replaced with a comment summarizing the verified bounds.*
- [ ] **P2-4: Add key-value pair support**. CLRS hash tables store satellite data. Extend the table to `array (int & int)` or a struct, or document the deliberate restriction to key-only storage.
- [x] **P2-5: Strengthen `key_in_table`** to tie the existential witness to the linear-probing sequence. Added `key_findable` predicate: key is at some probe position `p` with no empty slots (-1) at earlier probe positions. Proven as postcondition of `hash_insert`.

### Priority 3 — Low (Quality of Life)

- [x] **P3-1: Fix stale build path in README.md** (line 67 references `/home/nswamy/workspace/clrs/` instead of current location).
- [x] **P3-2: Add creation/destruction helpers** (`hash_table_create`, `hash_table_free`) to reduce boilerplate in test and client code.
- [ ] **P3-3: Add negative tests** in `CLRS.Ch11.HashTable.Test.fst` — insert until full, then verify insert returns `false`; search for key not present; delete and re-search.
- [ ] **P3-4: Add collision test** — insert keys that hash to the same slot (e.g., 3 and 8 in a size-5 table) and verify both are findable.
- [ ] **P3-5: Use type-safe sentinels** instead of magic numbers (`-1`, `-2`). Define an inductive type `slot = Empty | Deleted | Occupied (key: nat)` and store `array slot`. This eliminates the key-space restriction (`key >= 0`).
- [ ] **P3-6: Investigate stale cache entry** — `_cache/CLRS.Ch11.HashTable.Complexity.fst.checked` exists but no corresponding `.fst` file is present. Clean up or restore the file.
- [ ] **P3-7: Proof stability** — run with `--quake 3` to test resilience of the Z3-dependent proofs (rlimit 100). ✅ *Done: all queries pass 3/3 quake runs. Proofs are fully stable.*

---

## Summary Scorecard

| Dimension | Score | Notes |
|---|---|---|
| CLRS Fidelity | **7/10** | INSERT and SEARCH faithful; DELETE missing; no key-value pairs |
| Specification Strength | **4/10** | Weak postconditions; Spec module disconnected from implementation |
| Complexity Proofs | **6/10** | Worst-case O(n) proven; average-case and tautology issues |
| Code Quality | **8/10** | Clean Pulse idioms; minor issues with unconditional writes |
| Proof Quality | **9/10** | Zero admits; well-structured invariants; moderate Z3 reliance |
| Documentation | **7/10** | Accurate with one stale path; understates gaps |
| **Overall** | **6.5/10** | Solid mechanical verification of what exists; critical functional properties unproven |
