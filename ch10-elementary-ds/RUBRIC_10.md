# Chapter 10: Elementary Data Structures — Rubric Compliance

**Source:** `ch10-elementary-ds/` (15 source files, ~3,138 lines)
**Canonical rubric:** `RUBRIC.md`
**Existing audit:** `AUDIT_CH10.md`
**Date:** 2025-07-18

---

## Current File Inventory

| # | File | Lines | Rubric Role | Notes |
|---|------|------:|-------------|-------|
| 1 | `CLRS.Ch10.Stack.fsti` | 75 | **Impl.fsti** | Public interface for Stack — `stack_inv`, all op signatures with SNIPPET markers |
| 2 | `CLRS.Ch10.Stack.fst` | 274 | **Impl.fst** | Pulse implementation of array-based Stack (push/pop/peek/empty/create) |
| 3 | `CLRS.Ch10.Stack.Test.fst` | 34 | Test | Basic push/pop/peek smoke test |
| 4 | `CLRS.Ch10.Queue.fsti` | 86 | **Impl.fsti** | Public interface for Queue — `queue_inv`, all op signatures with SNIPPET markers |
| 5 | `CLRS.Ch10.Queue.fst` | 418 | **Impl.fst** | Pulse implementation of circular-buffer Queue (enqueue/dequeue/empty/create) |
| 6 | `CLRS.Ch10.Queue.Test.fst` | 79 | Test | FIFO ordering + wraparound test |
| 7 | `CLRS.Ch10.SinglyLinkedList.Base.fst` | 137 | Shared base | Extracted `node`, `dlist`, `is_dlist`, ghost boilerplate, `remove_first` |
| 8 | `CLRS.Ch10.SinglyLinkedList.fst` | 119 | **Impl.fst** | Heap-allocated SLL: insert/search/delete (imports Base) |
| 9 | `CLRS.Ch10.SinglyLinkedList.Complexity.fst` | 144 | **Complexity.fst** | Ghost-tick instrumented SLL ops with exact bounds |
| 10 | `CLRS.Ch10.SinglyLinkedList.Test.fst` | 44 | Test | Insert/search/delete round-trip test |
| 11 | `CLRS.Ch10.DLL.fst` | 1006 | **Impl.fst** | True DLL with `dls` segment predicate, all ops + delete-by-index |
| 12 | `CLRS.Ch10.DLL.Test.fst` | 47 | Test | Insert/search/delete round-trip test for DLL |
| 13 | `CLRS.Ch10.DS.Spec.fst` | 355 | **Spec.fst** | Pure functional specs for Stack, Queue, LinkedList (LIFO/FIFO lemmas) |
| 14 | `CLRS.Ch10.LinkedList.Spec.fst` | 224 | **Spec.fst** | Pure linked-list spec (17 lemmas + theorem) |
| 15 | `CLRS.Ch10.DataStructures.Complexity.fst` | 96 | **Complexity.fst** | Op-count constants + trivial lemmas for Stack/Queue/LinkedList |

---

## Algorithms Covered

| Data Structure | CLRS Section | Impl File(s) | Spec File(s) | Status |
|---------------|-------------|--------------|--------------|--------|
| **Stack** (array-based) | §10.1 | `Stack.fst`/`.fsti` | `DS.Spec.fst` (stack section) | ✅ Complete — .fsti present |
| **Queue** (circular buffer) | §10.1 | `Queue.fst`/`.fsti` | `DS.Spec.fst` (queue section) | ✅ Complete — .fsti present |
| **Singly-Linked List** | §10.2 | `SinglyLinkedList.fst`, `SinglyLinkedList.Base.fst` | `LinkedList.Spec.fst`, `DS.Spec.fst` | 🔶 No `.fsti` interface |
| **Doubly-Linked List** | §10.2 | `DLL.fst` | `LinkedList.Spec.fst` | 🔶 No `.fsti` interface |

---

## Rubric Compliance Matrix

The canonical rubric requires each algorithm to have: **Spec.fst**, **Lemmas.fst/fsti**, **Complexity.fst/fsti**, **Impl.fst**, **Impl.fsti**.

### Stack

| Rubric Artifact | Required Name | Actual File | Status |
|----------------|--------------|-------------|--------|
| Spec.fst | `CLRS.Ch10.Stack.Spec.fst` | `CLRS.Ch10.DS.Spec.fst` (stack section) | 🔶 Exists but combined with Queue/LL in one file |
| Lemmas.fst | `CLRS.Ch10.Stack.Lemmas.fst` | `CLRS.Ch10.DS.Spec.fst` (8 LIFO lemmas) | 🔶 Lemmas present but not in dedicated file |
| Lemmas.fsti | `CLRS.Ch10.Stack.Lemmas.fsti` | — | ❌ Missing |
| Complexity.fst | `CLRS.Ch10.Stack.Complexity.fst` | `CLRS.Ch10.DataStructures.Complexity.fst` (stack constants) | 🔶 Trivial definitions only; no ghost-tick proofs |
| Complexity.fsti | `CLRS.Ch10.Stack.Complexity.fsti` | — | ❌ Missing |
| Impl.fst | `CLRS.Ch10.Stack.Impl.fst` | `CLRS.Ch10.Stack.fst` | 🔶 Named `Stack.fst` not `Stack.Impl.fst` |
| Impl.fsti | `CLRS.Ch10.Stack.Impl.fsti` | **`CLRS.Ch10.Stack.fsti`** | ✅ **Conformant** — full interface with `stack_inv`, all op signatures, SNIPPET markers |

### Queue

| Rubric Artifact | Required Name | Actual File | Status |
|----------------|--------------|-------------|--------|
| Spec.fst | `CLRS.Ch10.Queue.Spec.fst` | `CLRS.Ch10.DS.Spec.fst` (queue section) | 🔶 Exists but combined |
| Lemmas.fst | `CLRS.Ch10.Queue.Lemmas.fst` | `CLRS.Ch10.DS.Spec.fst` (12 FIFO lemmas) | 🔶 Lemmas present but not in dedicated file |
| Lemmas.fsti | `CLRS.Ch10.Queue.Lemmas.fsti` | — | ❌ Missing |
| Complexity.fst | `CLRS.Ch10.Queue.Complexity.fst` | `CLRS.Ch10.DataStructures.Complexity.fst` (queue constants) | 🔶 Trivial definitions only |
| Complexity.fsti | `CLRS.Ch10.Queue.Complexity.fsti` | — | ❌ Missing |
| Impl.fst | `CLRS.Ch10.Queue.Impl.fst` | `CLRS.Ch10.Queue.fst` | 🔶 Named `Queue.fst` not `Queue.Impl.fst` |
| Impl.fsti | `CLRS.Ch10.Queue.Impl.fsti` | **`CLRS.Ch10.Queue.fsti`** | ✅ **Conformant** — full interface with `queue_inv`, all op signatures, SNIPPET markers, design-choice comment |

### Singly-Linked List

| Rubric Artifact | Required Name | Actual File | Status |
|----------------|--------------|-------------|--------|
| Spec.fst | `CLRS.Ch10.SinglyLinkedList.Spec.fst` | `CLRS.Ch10.LinkedList.Spec.fst` | 🔶 Present but not rubric-named |
| Lemmas.fst | `CLRS.Ch10.SinglyLinkedList.Lemmas.fst` | `CLRS.Ch10.LinkedList.Spec.fst` (17 lemmas) | 🔶 Combined with spec |
| Lemmas.fsti | `CLRS.Ch10.SinglyLinkedList.Lemmas.fsti` | — | ❌ Missing |
| Complexity.fst | `CLRS.Ch10.SinglyLinkedList.Complexity.fst` | **`CLRS.Ch10.SinglyLinkedList.Complexity.fst`** | ✅ **Conformant** — ghost-tick exact bounds for insert/search/delete |
| Complexity.fsti | `CLRS.Ch10.SinglyLinkedList.Complexity.fsti` | — | ❌ Missing |
| Impl.fst | `CLRS.Ch10.SinglyLinkedList.Impl.fst` | `CLRS.Ch10.SinglyLinkedList.fst` | 🔶 Named without `.Impl` suffix |
| Impl.fsti | `CLRS.Ch10.SinglyLinkedList.Impl.fsti` | — | ❌ Missing |

### Doubly-Linked List

| Rubric Artifact | Required Name | Actual File | Status |
|----------------|--------------|-------------|--------|
| Spec.fst | `CLRS.Ch10.DLL.Spec.fst` | `CLRS.Ch10.LinkedList.Spec.fst` (shared with SLL) | 🔶 Present but shared/not rubric-named |
| Lemmas.fst | `CLRS.Ch10.DLL.Lemmas.fst` | — | ❌ Missing (DLL-specific lemmas are inline in `DLL.fst`) |
| Lemmas.fsti | `CLRS.Ch10.DLL.Lemmas.fsti` | — | ❌ Missing |
| Complexity.fst | `CLRS.Ch10.DLL.Complexity.fst` | — | ❌ Missing (O(1)/O(n) is structural, not proven with ghost ticks) |
| Complexity.fsti | `CLRS.Ch10.DLL.Complexity.fsti` | — | ❌ Missing |
| Impl.fst | `CLRS.Ch10.DLL.Impl.fst` | `CLRS.Ch10.DLL.fst` | 🔶 Named without `.Impl` suffix |
| Impl.fsti | `CLRS.Ch10.DLL.Impl.fsti` | — | ❌ Missing |

---

## Summary Scoreboard

| Artifact | Stack | Queue | SinglyLinkedList | DoublyLinkedList |
|----------|:-----:|:-----:|:----------------:|:----------------:|
| Spec.fst | 🔶 | 🔶 | 🔶 | 🔶 |
| Lemmas.fst | 🔶 | 🔶 | 🔶 | ❌ |
| Lemmas.fsti | ❌ | ❌ | ❌ | ❌ |
| Complexity.fst | 🔶 | 🔶 | ✅ | ❌ |
| Complexity.fsti | ❌ | ❌ | ❌ | ❌ |
| Impl.fst | 🔶 | 🔶 | 🔶 | 🔶 |
| Impl.fsti | ✅ | ✅ | ❌ | ❌ |

**Legend:** ✅ = Conformant, 🔶 = Content exists but naming/structure deviates, ❌ = Missing

---

## Detailed Action Items

### Already Conformant (no action needed)

1. **`Stack.fsti`** — Full `Impl.fsti` with `stack_inv` predicate, all 5 operation signatures (`create_stack`, `stack_empty`, `push`, `pop`, `peek`), SNIPPET markers, and proper module structure.

2. **`Queue.fsti`** — Full `Impl.fsti` with `queue_inv` predicate, all 4 operation signatures (`create_queue`, `queue_empty`, `enqueue`, `dequeue`), SNIPPET markers, and a design-choice comment documenting the 3-field deviation from CLRS.

3. **`SinglyLinkedList.Complexity.fst`** — Proper ghost-tick instrumented operations with exact bounds (`insert_cost = 1`, `search_cost n = n`, `delete_cost n = n + 1`). Correctly named.

4. **`SinglyLinkedList.Base.fst`** — Shared definitions extracted per audit recommendation T-2 (eliminates prior duplication).

5. **All files: 0 admits, 0 assumes** — Proof quality is excellent across the board.

### Priority 1 — Create Missing `.fsti` Interface Files

| Action | Description | Effort |
|--------|-------------|--------|
| **A-1** | Create `CLRS.Ch10.SinglyLinkedList.Impl.fsti` — Extract `is_dlist` predicate and op signatures from `SinglyLinkedList.fst` | Medium |
| **A-2** | Create `CLRS.Ch10.DLL.Impl.fsti` — Extract `dls`/`dll` predicates and op signatures from `DLL.fst` | Medium |
| **A-3** | Create `CLRS.Ch10.SinglyLinkedList.Lemmas.fsti` — Signature file for `LinkedList.Spec.fst` SLL lemmas | Low |
| **A-4** | Create `CLRS.Ch10.Stack.Lemmas.fsti` — Signature file for stack LIFO lemmas from `DS.Spec.fst` | Low |
| **A-5** | Create `CLRS.Ch10.Queue.Lemmas.fsti` — Signature file for queue FIFO lemmas from `DS.Spec.fst` | Low |

### Priority 2 — Split Combined Files into Rubric-Named Modules

| Action | Description | Effort |
|--------|-------------|--------|
| **A-6** | Split `DS.Spec.fst` into `Stack.Spec.fst`, `Queue.Spec.fst`, `LinkedList.Spec.fst` (or keep combined with aliases) | Medium |
| **A-7** | Rename `Stack.fst` → `Stack.Impl.fst` (or add `Stack.Impl.fst` re-export) | Low |
| **A-8** | Rename `Queue.fst` → `Queue.Impl.fst` (or add re-export) | Low |
| **A-9** | Rename `SinglyLinkedList.fst` → `SinglyLinkedList.Impl.fst` | Low |
| **A-10** | Rename `DLL.fst` → `DLL.Impl.fst` | Low |

### Priority 3 — Add Missing Complexity Artifacts

| Action | Description | Effort |
|--------|-------------|--------|
| **A-11** | Create `CLRS.Ch10.Stack.Complexity.fst` with ghost-tick instrumented push/pop | Medium |
| **A-12** | Create `CLRS.Ch10.Queue.Complexity.fst` with ghost-tick instrumented enqueue/dequeue | Medium |
| **A-13** | Create `CLRS.Ch10.DLL.Complexity.fst` with ghost-tick instrumented insert/search/delete | Medium |
| **A-14** | Create `.fsti` files for each Complexity module above | Low |

### Priority 4 — CLRS Fidelity Gaps (from AUDIT_CH10.md)

| Action | Audit Ref | Description |
|--------|-----------|-------------|
| **A-15** | F-1 | Add refinement lemma connecting imperative append-push to pure cons-push |
| **A-16** | F-6 | Implement true O(1) LIST-DELETE-by-pointer for DLL |
| **A-17** | F-5 | (Optional) Implement sentinel-based circular DLL per CLRS §10.2 Fig 10.4 |

---

## Quality Checks

| Check | Result | Details |
|-------|--------|---------|
| **Zero admits/assumes** | ✅ Pass | Grep confirms 0 admits, 0 assumes across all 15 files |
| **Solver options** | ✅ Pass | Only `#push-options "--z3rlimit 40"` in `Queue.fst` (line 361); well-scoped |
| **SNIPPET markers** | ✅ Pass | Present in `Stack.fsti`, `Queue.fsti`, `SinglyLinkedList.Base.fst`, `SinglyLinkedList.fst`, `DLL.fst`, `DS.Spec.fst`, `DataStructures.Complexity.fst` |
| **Code duplication** | ✅ Resolved | `SinglyLinkedList.Base.fst` extracts shared definitions (audit T-2 completed) |
| **Misleading names** | ✅ Resolved | `DoublyLinkedList.Complexity*` renamed to `SinglyLinkedList.Complexity*` (audit T-1 completed) |
| **Test coverage** | ✅ Pass | Tests exist for all 4 data structures: `Stack.Test`, `Queue.Test`, `SinglyLinkedList.Test`, `DLL.Test` |
| **`.fsti` for Stack** | ✅ Conformant | Full interface with invariant + 5 op signatures |
| **`.fsti` for Queue** | ✅ Conformant | Full interface with invariant + 4 op signatures + design-choice comment |
| **`.fsti` for SLL** | ❌ Missing | No interface file; ops are defined directly in `.fst` |
| **`.fsti` for DLL** | ❌ Missing | No interface file; 1006-line `.fst` contains everything |
| **Rubric naming** | 🔶 Partial | Files use `Stack.fst` not `Stack.Impl.fst`; specs are combined not per-algorithm |
