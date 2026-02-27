# Audit Report: Chapter 21 — Disjoint Sets (Union-Find)

**Date:** 2025-07-17
**Auditor:** Copilot (automated)
**Scope:** `ch21-disjoint-sets/` — 6 files, 1960 total lines
**Verification status:** All 6 `.checked` files present in `_cache/` — **all modules verify**

---

## 1. CLRS Fidelity

### CLRS §21.3 Pseudocode (reference)

| CLRS Operation | CLRS Pseudocode | AutoCLRS Implementation | Match? |
|---|---|---|---|
| **MAKE-SET(x)** | `x.p = x; x.rank = 0` | `make_set` (UnionFind.fst:87–153): loop sets `parent[i]=i, rank[i]=0` for `i ∈ [0,n)` | ✅ Faithful (batch version) |
| **FIND-SET(x)** (no compression) | Walk parent pointers to root | `find` (UnionFind.fst:165–215): read-only traversal with fuel=n | ✅ Faithful |
| **FIND-SET(x)** (path compression) | `if x≠x.p then x.p = FIND-SET(x.p); return x.p` | `find_compress` (UnionFind.fst:228–260): one-step compression (`parent[x]=root` only) | ⚠️ **Partial** — compresses only the query node, not all nodes on the path |
| **FIND-SET(x)** (full compression) | Recursive two-pass: all path nodes → root | `find_set` (FullCompress.fst:150–242): iterative two-pass (pass 1: find root; pass 2: `compress_path`) | ✅ Faithful (iterative equivalent of CLRS recursive) |
| **LINK(x,y)** | `if x.rank > y.rank then y.p=x else x.p=y; if x.rank==y.rank then y.rank+=1` | `union_` (UnionFind.fst:272–338): union by rank with `find` inlined | ✅ Faithful |
| **UNION(x,y)** | `LINK(FIND-SET(x), FIND-SET(y))` | `union_` calls `find` for both operands, then performs LINK logic | ✅ Faithful |

### Fidelity Notes

1. **LINK convention:** CLRS LINK lines 4–5 increment the *surviving* root's rank when ranks are equal. In AutoCLRS (line 330–332), the equal-rank case attaches `root_y` under `root_x` and increments `rank[root_x]`. This matches CLRS, choosing `root_x` as survivor (CLRS says "arbitrarily choose").

2. **Rank overflow guard:** Line 332 caps rank increment at `n-1` (`if rank_x < n-1 then rank_x+1 else rank_x`). CLRS has no such guard; however, since `rank < ⌊log₂ n⌋ ≤ n-1`, this guard never fires in valid states. Harmless but unnecessary.

3. **`find_compress` vs CLRS FIND-SET:** The main `find_compress` only sets `parent[x] = root`, *not* all nodes on the find path. This is a weaker optimization than CLRS's full path compression. The `FullCompress.fst` module provides the true CLRS FIND-SET, but `union_` does not call it—it calls the non-compressing `find`.

4. **Pure spec model:** `Spec.fst` provides `pure_find` and `pure_union` as pure F* functions that exactly mirror CLRS logic. This is a clean separation of concerns.

**Fidelity verdict: ✅ High fidelity.** All three CLRS operations are implemented. Full path compression exists but is not wired into `union_`. The main `union_` uses read-only find (no compression), which is a valid CLRS configuration (union-by-rank without path compression).

---

## 2. Specification Strength

### What is proven

| Property | Where | Strength |
|---|---|---|
| **find returns a root** | `find` postcondition (line 182): `is_root s (SZ.v root)` | ✅ Strong |
| **find returns the canonical representative** | `find` postcondition (line 183): `find_root s (SZ.v x) (SZ.v n) == SZ.v root` | ✅ Strong — linked to pure spec |
| **find is read-only** | `find` returns the same ghost sequence `s` | ✅ Strong |
| **make_set produces a forest of singletons** | Postcondition (line 109–111): `is_forest sp n`, all roots, all rank 0 | ✅ Strong |
| **union merges sets** | `union_` postcondition (lines 303–306): one root now points to the other | ✅ Strong |
| **union preserves well_formed** | `union_` postcondition (line 294): `well_formed sp n` | ✅ |
| **Same-set union is identity** | Line 303: `fst res = snd res ==> Seq.equal sp sparent` | ✅ |
| **pure_union correctness** | `pure_union_correctness` (Spec.fst:512–516): after union, `pure_find f' x == pure_find f' y` | ✅ **Key theorem** |
| **Rank invariant preserved** | `pure_union_preserves_rank_invariant` (Spec.fst:335–389) | ✅ |
| **size ≥ 2^rank** | `pure_union_sized_preserves_invariant` (RankBound.fst:317–486) | ✅ |
| **find_set (full compression) postcondition** | FullCompress.fst:165–173: `parent[x]=root, parent[root]=root, well_formed` | ⚠️ See gaps below |

### Specification Gaps

1. **`union_` does not prove `is_forest` preservation.** The postcondition only guarantees `well_formed sp n`, not the stronger `is_forest sp n` (which includes acyclicity/reachability). This means a caller cannot chain unions and then call `find` without re-establishing `is_forest`. **Medium severity** — the `is_forest` property requires proving that attaching one root under another preserves the reachability invariant for all nodes.

2. **`find_compress` does not prove `is_forest` preservation.** The postcondition (line 246) only gives `well_formed sp n`, not `is_forest`. Same issue — callers cannot compose `find_compress` with `find`.

3. **`find_set` (FullCompress) does not prove `is_forest` preservation.** Same pattern — postcondition is `well_formed`, not `is_forest`.

4. **No `same_set` equivalence relation proven at imperative level.** The pure spec proves `pure_find f' x == pure_find f' y` after union, but the imperative `union_` only proves that one root points to the other — the full transitive find equivalence is not linked.

5. **`uf_invariant_maintained` is vacuous.** (Spec.fst:618–621) The lemma's postcondition is `ensures True` — it proves nothing. The comment acknowledges this.

**Specification strength verdict: ✅ Good for individual operations, ⚠️ Weak for composition.** The `is_forest` gap prevents chaining operations at the imperative level without re-establishing the acyclicity invariant.

---

## 3. Complexity Analysis

### What is proven

| Claim | File | Status |
|---|---|---|
| **Find worst-case O(n) without compression** | Complexity.fst:17,23–25 | ✅ Trivial (`find_worst n = n`, `find_worst n <= n`) |
| **Union is O(1)** | Complexity.fst:27–30 | ✅ Trivial |
| **Sequence of m finds is O(m·n)** | Complexity.fst:33–40 | ✅ Trivial |
| **Rank bound: rank[x] ≤ ⌊log₂ n⌋** | RankBound.fst:509–541 | ⚠️ **Commented out** (depends on `CLRS.Common.Complexity.log2_floor`) |
| **size ≥ 2^rank (key lemma for rank bound)** | RankBound.fst:71–75, 317–486 | ✅ Fully proven and verified |
| **Find terminates with fuel=n** | Spec.fst:192–197 (counting argument) | ✅ Proven without assuming `ranks_bounded` |
| **Find terminates (alternative proof)** | FindTermination.fst:72–76 | ✅ Proven (assumes `ranks_bounded` as precondition) |
| **Amortized O(α(n))** | — | ❌ **Not attempted** |

### Complexity Notes

1. **The `Complexity.fst` module is superficial.** It defines constant functions and proves trivial bounds (`n ≤ n`, `1 ≤ 1`). It does not model amortized complexity or the inverse Ackermann function.

2. **The logarithmic rank bound proof is structurally complete but commented out** (RankBound.fst:490–633). The proof logic is correct: it uses `size ≥ 2^rank` (verified) plus `size ≤ n` (from `is_valid_uf_sized`) to derive `rank ≤ log₂(n)`. The dependency on `CLRS.Common.Complexity.log2_floor` exists and is verified in `common/`. Uncommenting should work.

3. **The height ≤ rank bound is incomplete** even in the commented section. `height_le_rank` (line 590–595) only proves `height ≤ n` (trivially from fuel), not the tight `height ≤ rank[root] ≤ log₂(n)`. The comment at line 616 acknowledges this gap.

4. **Amortized O(α(n)) is not addressed anywhere.** This is the main CLRS §21.4 result and would require potential-function-based analysis, which is extremely challenging to formalize.

**Complexity verdict: ⚠️ Partial.** The key building block (`size ≥ 2^rank`) is proven. The rank ≤ log₂(n) bound is correctly structured but commented out. The amortized inverse-Ackermann bound is absent.

---

## 4. Code Quality

### Strengths

- **Clean architecture:** Pure spec (`Spec.fst`) separated from imperative implementation (`UnionFind.fst`), with supporting proofs in dedicated modules.
- **Pulse idioms used correctly:** Fractional permissions for read-only `find`, mutable references for loop variables, ghost sequences for specification.
- **Loop invariants are explicit and well-structured** in all loops.
- **SNIPPET markers** for key signatures enable documentation extraction.
- **Proof modularity:** FindTermination, RankBound, FullCompress are self-contained modules.

### Issues

1. **Duplicated type definitions.** `uf_forest`, `is_valid_uf`, `rank_invariant`, `ranks_bounded`, and `pure_find_fuel` are copy-pasted across `Spec.fst`, `FindTermination.fst`, and `RankBound.fst`. These should share a common module to avoid drift.

2. **`well_formed` is defined differently in `FullCompress.fst`** (line 36: `Seq.length parent >= n`) vs `UnionFind.fst` (line 37: `n <= Seq.length parent`). Semantically equivalent but syntactically inconsistent; `FullCompress.fst` also omits `n > 0` from `well_formed`.

3. **`union_` uses SZ.t arithmetic for rank** without proving overflow safety for edge cases. The `if (rank_x <^ SZ.sub n 1sz)` guard (line 332) is defensive but makes the rank capped at `n-1` rather than proven safe.

4. **`compress_path` loop invariant** (FullCompress.fst:94–104) does not track that intermediate nodes on the path are compressed. It only maintains `well_formed` and `is_root_at root`. This means the loop's compression effect (beyond the final `parent[x] = root` write) is not captured in the postcondition.

5. **Naming:** `union_` (with trailing underscore) is non-standard. Pulse likely reserves `union` as a keyword, so this is acceptable but should be documented.

6. **Section numbering** in `Spec.fst` jumps from §5 to §8 (skipping §6, §7), suggesting deleted sections.

**Code quality verdict: ✅ Good overall.** Main concerns are type duplication and the incomplete compression postcondition.

---

## 5. Proof Quality — Admits and Assumes

### Formal Search Results

A comprehensive search for `admit`, `assume`, `sorry`, `Admit`, `Assume` in executable code (excluding comments) across all 6 files found:

| File | Line | Keyword | Context |
|---|---|---|---|
| — | — | — | **None found in executable code** |

### Commented-Out Code

The following section is **commented out** in `RankBound.fst` (lines 490–633):
- `rank_logarithmic_bound_sized` — the log₂(n) rank bound
- `tree_height`, `height_le_rank` — height bound lemmas
- `union_by_rank_logarithmic_find`, `find_logarithmic_complexity` — summary theorems

This code depends on `CLRS.Common.Complexity.log2_floor` which is available but the `open` is commented out (line 18: `// open CLRS.Common.Complexity`). The commented code contains no admits; the proof structure is complete.

### `assert (False)` / `unreachable`

| File | Line | Usage | Justified? |
|---|---|---|---|
| `FullCompress.fst` | 231–232 | `assert (pure False); unreachable ()` — dead branch in `find_set` | ✅ Yes — the branch is provably unreachable (loop invariant contradicts the `else` guard) |
| `RankBound.fst` | 540 | `assert (False)` — contradiction branch in commented `rank_logarithmic_bound_sized` | ✅ Yes — proof by contradiction (rank > log₂(n) leads to 2^rank > n, contradicting size ≤ n) |

### Vacuous Lemmas

| File | Line | Lemma | Issue |
|---|---|---|---|
| `Spec.fst` | 618–621 | `uf_invariant_maintained` | `ensures True` — proves nothing; placeholder |

### Expected Assume (from task description)

The task description mentions "1 assume for rank bound expected." **No such assume exists** — the rank bound section is commented out entirely rather than using an assume. This is a conservative choice: instead of assuming `ranks_bounded`, the `Spec.fst` module proves find termination via a counting argument that avoids needing `ranks_bounded` at all (lines 123–197).

**Proof quality verdict: ✅ Excellent.** Zero admits, zero assumes in verified code. One vacuous placeholder lemma. The commented-out rank bound code is structurally sound.

---

## 6. Documentation Accuracy

### Module Headers

| File | Header Claims | Accurate? |
|---|---|---|
| `UnionFind.fst` | "NO admits. NO assumes." | ✅ Confirmed |
| `UnionFind.fst` | "find_compress sets parent[x] directly to root" | ✅ |
| `Spec.fst` | "Lemma 21.4: rank[x] < rank[parent[x]]" | ✅ Proven (lines 66–69) |
| `Spec.fst` | "logarithmic bound admitted here for brevity" | ⚠️ Misleading — the bound is commented out, not admitted. "Commented out pending module dependency" would be more accurate. |
| `RankBound.fst` | "rank[x] ≤ ⌊log₂ n⌋ where n is the total number of elements" | ⚠️ Claimed in header (line 7) but the proof is commented out |
| `FindTermination.fst` | "We add [ranks_bounded] as a precondition" | ✅ Accurate — it is a precondition, not an assumption |

### Inline Comments

Generally accurate and helpful. The extensive proof strategy comment in `RankBound.fst` (lines 266–290) clearly explains the counting argument for `union_size_bound`.

### Missing Documentation

- No top-level README or design document for the chapter
- No documentation of the relationship between `find`, `find_compress`, and `find_set` — a reader must guess which is the "main" find operation
- The CLRS section references (§21.3, Lemma 21.4, Theorem 21.5) are mentioned but not systematically mapped to code

**Documentation verdict: ⚠️ Adequate but has inaccuracies.** The "admitted for brevity" claim is misleading; the RankBound header over-promises relative to what is verified.

---

## 7. Summary Scorecard

| Dimension | Score | Notes |
|---|---|---|
| CLRS Fidelity | **A** | All operations implemented; full path compression available |
| Specification Strength | **B+** | Strong per-operation specs; `is_forest` preservation gap blocks composition |
| Complexity | **C+** | Key `size ≥ 2^rank` proven; rank bound commented out; no α(n) |
| Code Quality | **B+** | Clean architecture; type duplication; minor inconsistencies |
| Proof Quality | **A** | Zero admits/assumes; all modules verify |
| Documentation | **B** | Mostly accurate; header of RankBound over-claims |

**Overall: B+ — A solid verified implementation with excellent proof hygiene and good CLRS fidelity. The main gaps are the `is_forest` preservation for imperative composition and the commented-out rank bound.**

---

## 8. Task List

### Priority 1 (High) — Correctness Gaps

| # | Task | File | Effort | Status |
|---|---|---|---|---|
| 1.1 | **Prove `union_` preserves `is_forest`** — add `is_forest sp n` to `union_` postcondition. Requires showing that attaching one root under another preserves `has_root_within` for all nodes. | `UnionFind.fst:293` | Medium | ✅ Done — pigeonhole-based path tightening + depth increase proof (~200 lines) |
| 1.2 | **Prove `find_compress` preserves `is_forest`** — the one-step compression `parent[x]=root` preserves reachability for all nodes. | `UnionFind.fst:240–252` | Medium | ✅ Done — `compress_preserves_is_forest` lemma |
| 1.3 | **Wire full compression into `union_`** or provide a `find_compress_full` that calls `find_set` and proves `is_forest` preservation. Currently `union_` uses non-compressing `find`. | `UnionFind.fst`, `FullCompress.fst` | Medium-High | ⏳ Pending |
| 2.1 | **Uncomment rank bound proof** — add `open CLRS.Common.Complexity` (line 18) and uncomment lines 490–633. The proof should verify as-is since `log2_floor` and `lemma_log2_floor_bound` exist in `common/`. | `RankBound.fst` | Low | ✅ Done |
| 2.2 | **Prove tight height ≤ rank[root] ≤ log₂(n)** — the current commented proof only achieves `height ≤ n`. Proving `path_length ≤ rank[root]` requires an inductive argument that each parent step increases rank. | `RankBound.fst:559–595` | Medium | ✅ Done — `height_le_root_rank` + `union_by_rank_logarithmic_find` now proves `tree_height ≤ log₂(n)` |
| 2.3 | **Strengthen `uf_invariant_maintained`** — replace `ensures True` with an actual inductive proof over operation sequences, or remove the placeholder. | `Spec.fst:618–621` | Medium | ✅ Done — `apply_unions` + inductive proof |
| 2.4 | **Prove `find_set` preserves `is_forest`** — `compress_path` and `find_set` only guarantee `well_formed` in postcondition. | `FullCompress.fst:77–84, 163–173` | Medium | ✅ Done — `upd_preserves_is_forest` (pigeonhole-based, works for any node) |
| 3.1 | **Extract shared types to a common module** — `uf_forest`, `is_valid_uf`, `rank_invariant`, `pure_find_fuel` are duplicated in Spec, FindTermination, and RankBound. Create `CLRS.Ch21.UnionFind.Types.fst`. | Multiple | Low-Medium | ⏳ Pending |
| 3.2 | **Fix section numbering** in `Spec.fst` — jumps from §5 to §8. | `Spec.fst` | Trivial | ✅ Done |
| 3.3 | **Fix documentation claim** — change "admitted here for brevity" to "proof commented out pending module integration" in `Spec.fst` header (line 13) and update `RankBound.fst` header to note the commented-out status. | `Spec.fst:13`, `RankBound.fst:1–10` | Trivial | ✅ Done |
| 3.4 | **Unify `well_formed` definitions** across `UnionFind.fst` and `FullCompress.fst` — ensure both include `n > 0` and use the same syntactic form. | `FullCompress.fst:35–37` | Trivial | ✅ Done |
| 3.5 | **Remove defensive rank overflow guard** — since `rank ≤ log₂(n) < n-1` is provable, the `if rank_x < n-1` guard on line 332 is dead code. Once task 2.1 is done, this can be replaced with a proof that `rank_x + 1` fits in `SZ.t`. | `UnionFind.fst:332` | Low | 🔒 Blocked — needs rank invariant in `union_` precondition or link to pure spec (task 4.2) |
| 3.6 | **Add chapter README** documenting the module structure, which find variant to use, and CLRS section mapping. | New file | Low | ✅ Done |
| 4.2 | **Link imperative and pure specs** — prove that the imperative `union_` + `find` sequence produces the same partition as `pure_union` + `pure_find`. This is a refinement proof connecting the Pulse code to the pure F* model. | New module | High | ⏳ Pending |

### Defer

| # | Task | File | Effort |
|---|---|---|---|
| 4.1 | **Formalize amortized O(α(n)) bound** — CLRS §21.4 potential-function analysis. Would require defining Ackermann function, inverse Ackermann, and potential function. | New module | Very High |

---

*End of audit.*
