# Audit Report: Chapter 10 — Elementary Data Structures

**Scope:** `ch10-elementary-ds/` (18 source files, 3,720 lines)  
**Date:** 2025-07-17  
**Auditor:** Copilot

---

## Executive Summary

Chapter 10 provides verified implementations of **stacks**, **queues**, **singly-linked lists**, and **doubly-linked lists** in Pulse, together with pure functional specifications, complexity bounds, and test harnesses. The code is **admit-free and assume-free** — all 3,720 lines carry machine-checked proofs. Functional correctness is well-established. The main concerns are: (a) CLRS fidelity gaps in the stack/queue array conventions and the absence of sentinel-based DLL, (b) massive code duplication across three singly-linked-list variants, and (c) documentation that is partially stale.

| Metric | Status |
|--------|--------|
| Admits / Assumes | **0** (excellent) |
| CLRS Fidelity | Moderate — deviations documented below |
| Spec Strength | Strong for all data structures |
| Complexity | Proven O(1)/O(n) as expected |
| Code Quality | Significant duplication in linked-list variants |
| Documentation | Partially stale (README references deprecated APIs) |

---

## 1. CLRS Fidelity

### 1.1 Stack (§10.1)

| CLRS | Implementation | Verdict |
|------|----------------|---------|
| Array `S[1..n]`, 1-indexed | `Vec t` (0-indexed) | ✅ Minor — 0-based is idiomatic |
| `S.top` = index of topmost element | `top` = index of *next free slot* (0 = empty) | ⚠️ Off-by-one from CLRS convention where `S.top` points to the most recently inserted element. Functionally equivalent but differs from textbook. |
| PUSH: `S.top = S.top+1; S[S.top] = x` | Write at `top`, then increment | ✅ Equivalent (order swapped for 0-based indexing) |
| POP: `S.top = S.top-1; return S[S.top+1]` | Decrement `top`, read at `top` | ✅ Equivalent |
| STACK-EMPTY: `S.top == 0` | `top_val == 0sz` | ✅ Exact match |
| Overflow error on push when full | Precondition `L.length contents < capacity` | ✅ Modeled as precondition rather than runtime error — appropriate for verified code |

**Logical model:** Contents are stored as `list t` where list-append models push (element at end = top). CLRS models top at `S.top`, bottom at `S[1]`. The implementation stores elements array-first-to-last matching list-first-to-last, with the *last* element being the top. This is a valid encoding but reverses the conventional mental model where `head` of the spec list = top of stack. The `DS.Spec.fst` pure spec uses the standard convention (`push x s = x :: s`), creating a mismatch with the imperative implementation where push appends.

**Finding F-1:** The imperative stack spec (`Stack.fsti`) models push as *append* (`L.append contents [x]`), while the pure spec (`DS.Spec.fst`) models push as *cons* (`x :: s`). These are semantically equivalent (the lists are read from opposite ends) but they are not connected by any refinement lemma.

### 1.2 Queue (§10.1)

| CLRS | Implementation | Verdict |
|------|----------------|---------|
| Array `Q[1..n]`, at most n−1 elements | `Vec t` + explicit `size` box, up to capacity elements | ⚠️ CLRS wastes one slot to distinguish full/empty; implementation uses separate `size` counter. Valid design but different from textbook. |
| `Q.head`, `Q.tail` | `head`, `tail`, `size` boxes | ⚠️ Extra `size` field not in CLRS |
| ENQUEUE: write at `tail`, advance `tail` with mod | Same, using if-branch for wraparound | ✅ Equivalent |
| DEQUEUE: read at `head`, advance `head` with mod | Same, using if-branch for wraparound | ✅ Equivalent |
| Empty when `Q.head == Q.tail` | Empty when `size == 0` | ⚠️ Different empty test |
| Overflow/underflow as runtime errors | Modeled as preconditions | ✅ Appropriate |

**Finding F-2:** The queue uses a 3-field design (head + tail + size) instead of CLRS's 2-field design (head + tail). The extra `size` field simplifies the invariant but deviates from the textbook. A comment noting this design choice would be helpful.

### 1.3 Linked List (§10.2)

**Array-based "LinkedList" (LinkedList.fst/fsti):**

| CLRS | Implementation | Verdict |
|------|----------------|---------|
| Pointer-based doubly-linked list | Array-based sequential list | ❌ Major deviation — CLRS §10.2 describes pointer-based lists |
| LIST-INSERT at head, O(1) | Append at end, O(1) amortized | ⚠️ Not head-insert |
| LIST-DELETE given pointer, O(1) | Not implemented | ❌ Missing |
| LIST-SEARCH, O(n) | Linear scan, O(n) | ✅ Correct |

**Finding F-3:** `LinkedList.fst` is an array-based list (essentially a growable array), not a pointer-based linked list. It should be renamed or documented as a simplified variant. The file header already notes "simplified from true doubly-linked list" but the module name is misleading.

**Singly-Linked List (SinglyLinkedList.fst):**

| CLRS | Implementation | Verdict |
|------|----------------|---------|
| LIST-INSERT at head | `list_insert x head` — insert at head | ✅ Exact match |
| LIST-SEARCH by traversal | `list_search head k` — recursive traversal | ✅ Exact match |
| LIST-DELETE given pointer, O(1) | `list_delete head k` — delete by *key*, O(n) | ⚠️ CLRS LIST-DELETE takes a pointer, not a key. This is LIST-DELETE preceded by LIST-SEARCH, which is the common combined operation. |

**Finding F-4:** `SinglyLinkedList.fst` is named "singly" but the file header says "originally mislabelled as DoublyLinkedList". The node type has only `next` (no `prev`), confirming it is singly-linked. The name is now correct.

**True DLL (DLL.fst):**

| CLRS | Implementation | Verdict |
|------|----------------|---------|
| Node: key, prev, next | `node = { key: int; prev: option (box node); next: option (box node) }` | ✅ Exact match |
| LIST-INSERT at head | `list_insert hd_ref tl_ref x` | ✅ Exact match (updates both head and tail refs) |
| LIST-SEARCH | `list_search hd tl k` | ✅ Correct |
| LIST-DELETE given pointer, O(1) | `list_delete hd_ref tl_ref k` — by key, O(n) | ⚠️ Same as SLL: delete-by-key, not delete-by-pointer |
| LIST-DELETE-NODE at index | `list_delete_node hd_ref tl_ref x i` | ✅ Novel extension beyond CLRS |
| LIST-SEARCH returning pointer | `list_search_ptr hd tl k` | ✅ Useful extension |
| DLS segment predicate | `dls p l prev_ptr tail last_ptr` | ✅ Rich segment predicate enabling compositional reasoning |
| DLS append | `dls_append` | ✅ Useful for modular proofs |
| Sentinel-based DLL (Fig 10.4) | Not implemented | ⚠️ CLRS §10.2 sentinels variant is absent |

**Finding F-5:** No sentinel-based circular DLL is implemented. CLRS §10.2 describes this as a simplification using `L.nil`. This is a low-priority gap since the non-sentinel version is strictly more general.

**Finding F-6:** True O(1) LIST-DELETE (given a pointer to the node) is not provided as a standalone operation. `list_delete` and `list_delete_node` both do O(n) traversal. The DLL `dls` predicate with its `factor_dls`/`unfactor_dls` machinery could support O(1) delete if given a way to split the predicate at the node, but this is not exposed.

---

## 2. Specification Strength

### Stack
- **Invariant (`stack_inv`):** Maps array prefix `arr[0..top)` to logical list element-by-element. ✅ Strong.
- **LIFO property:** Proven in `DS.Spec.fst` via `lemma_stack_lifo_pop_push` and `lemma_stack_lifo_stack_preserved`. ✅ Complete.
- **push postcondition:** `stack_inv s (hide (L.append contents [x]))` — precisely specifies new contents. ✅
- **pop postcondition:** `L.append xs [x] == reveal contents` — precisely decomposes old contents. ✅
- **peek postcondition:** `exists init. L.append init [x] == reveal contents` — slightly weak; could be strengthened to `x == L.last contents`. Minor.

### Queue
- **Invariant (`queue_inv`):** Circular buffer with modular indexing: `arr[(head+i) % cap] == contents[i]` for all `i < size`. ✅ Strong — handles wraparound correctly.
- **FIFO property:** Proven in `DS.Spec.fst` via `lemma_queue_fifo_single` and `lemma_queue_dequeue_preserves_contents`. ✅
- **enqueue postcondition:** `queue_inv q (hide (L.append contents [x]))` ✅
- **dequeue postcondition:** `reveal contents == x :: xs` ✅ Precise.

### Linked List (Array-based)
- **Invariant (`list_inv`):** Array prefix maps to list. ✅ Same structure as stack.
- **Search postcondition:** Returns `Some idx` with index validity and element match, or `None` with `~(L.mem key contents)`. ✅ Strong.
- **Insert postcondition:** Appends element. ✅
- **Missing:** No delete operation. ❌

### Singly-Linked List
- **Predicate (`is_dlist`):** Recursive separation-logic predicate linking heap structure to `list int`. ✅ Textbook-quality.
- **Insert postcondition:** `is_dlist new_head (x :: 'l)` ✅ Precise.
- **Search postcondition:** `found <==> L.mem k 'l` ✅ Precise.
- **Delete postcondition:** `is_dlist new_head (remove_first k 'l)` ✅ Precise.
- **Memory:** Freed nodes are properly deallocated via `Box.free`. ✅

### DLL
- **Predicate (`dls`/`dll`):** DLS segment predicate tracks prev/next pointers for non-empty segments. `dll` wraps with `None` endpoints. ✅ Compositional and expressive.
- **All operations** have tight postconditions matching logical list operations. ✅
- **delete_in_dls**: Returns a `delete_result` predicate that handles both empty and non-empty results. ✅ Clean design.
- **list_delete_node** (index-based): Postcondition uses `remove_at i l`. ✅ Novel.

### Pure Specs
- **`LinkedList.Spec.fst`:** 17 lemmas + 1 theorem covering insert/search/delete interactions. ✅ Comprehensive.
- **`DS.Spec.fst`:** Stack (8 lemmas), Queue (12 lemmas), LinkedList (9 lemmas). ✅ Thorough.
- **`DataStructures.Complexity.fst`:** 11 trivial lemmas about constant operation counts. Low value — these are definitional equalities.

---

## 3. Complexity Analysis

| Data Structure | Operation | Expected | Proven | Where |
|---------------|-----------|----------|--------|-------|
| Stack | push | O(1) | ✅ Constant-time code path | Stack.fst:185-218 |
| Stack | pop | O(1) | ✅ Constant-time code path | Stack.fst:221-263 |
| Stack | peek | O(1) | ✅ Constant-time code path | Stack.fst:266-294 |
| Stack | empty | O(1) | ✅ Constant-time code path | Stack.fst:167-182 |
| Queue | enqueue | O(1) | ✅ Constant-time code path | Queue.fst:297-358 |
| Queue | dequeue | O(1) | ✅ Constant-time code path | Queue.fst:362-438 |
| Queue | empty | O(1) | ✅ Constant-time code path | Queue.fst:279-294 |
| SLL | insert | O(1) | ✅ Ghost ticks: `cf == c0 + 1` | Complexity.fst:158-173 |
| SLL | search | O(n) | ✅ Ghost ticks: `cf - c0 <= |l|` | Complexity.fst:177-208 |
| SLL | delete | O(n) | ✅ Ghost ticks: `cf - c0 <= |l|` | Complexity.fst:218-262 |
| DLL | insert | O(1) | ✅ Code path is constant | DLL.fst:389-430 |
| DLL | search | O(n) | ✅ Recursive traversal | DLL.fst:437-508 |
| DLL | delete | O(n) | ✅ Recursive traversal | DLL.fst:716-863 |
| DLL | delete_node (index) | O(n) | ✅ Recursive traversal to index | DLL.fst:883-972 |

**Enhanced complexity (`DoublyLinkedList.Complexity.Enhanced.fst`):**
- Defines pure cost functions: `insert_cost = 1`, `search_cost n = n`, `delete_cost n = n + 1`.
- Proves exact bounds using ghost tick counters. ✅

**Finding F-7:** Stack and queue complexity is *structural* (no loops, constant operations) but not proven via ghost tick counters like the linked-list variants. For uniformity, ghost-tick instrumented versions could be added, though this is low priority since the O(1) property is self-evident from the code.

**Finding F-8:** `DataStructures.Complexity.fst` provides only trivial lemmas (e.g., `stack_push_ops = 1` where `stack_push_ops` is *defined* as 1). These lemmas prove nothing beyond definitional equality and add no verification value. Consider removing or replacing with something connected to the actual implementations.

---

## 4. Code Quality

### 4.1 Massive Code Duplication

**Critical finding:** Three files contain near-identical code for the singly-linked-list predicate and ghost boilerplate:

| Definition | SinglyLinkedList.fst | Complexity.fst | Complexity.Enhanced.fst |
|-----------|---------------------|----------------|------------------------|
| `node` type | ✅ Lines 22-26 | ✅ Lines 40-47 | ✅ Lines 43-49 |
| `dlist` type | ✅ Line 29 | ✅ Line 50 | ✅ Line 52 |
| `is_dlist` predicate | ✅ Lines 34-42 | ✅ Lines 54-61 | ✅ Lines 56-63 |
| `elim_is_dlist_nil` | ✅ Lines 46-54 | ✅ Lines 65-74 | ✅ Lines 67-75 |
| `intro_is_dlist_nil` | ✅ Lines 56-62 | ✅ Lines 76-81 | ✅ Lines 77-83 |
| `intro_is_dlist_cons` | ✅ Lines 64-73 | ✅ Lines 83-92 | ✅ Lines 85-94 |
| `is_dlist_cases` | ✅ Lines 76-84 | ✅ Lines 95-103 | ✅ Lines 97-105 |
| `cases_of_is_dlist` | ✅ Lines 86-106 | ✅ Lines 104-125 | ✅ Lines 106-127 |
| `is_dlist_case_none` | ✅ Lines 108-119 | ✅ Lines 127-138 | ✅ Lines 129-140 |
| `is_dlist_case_some` | ✅ Lines 121-133 | ✅ Lines 140-152 | ✅ Lines 142-154 |
| `remove_first` | ✅ Lines 196-199 | ✅ Lines 211-214 | ✅ Lines 229-232 |

**~120 lines duplicated 3×** = ~240 lines of pure duplication. Additionally, `remove_first` is defined in 4 files (also in `DLL.fst` line 596).

**Finding F-9 (High Priority):** Extract shared definitions (`node`, `dlist`, `is_dlist`, all ghost helpers, `remove_first`) into a common module (e.g., `CLRS.Ch10.SinglyLinkedList.Base.fsti/fst`) and have the three files import it.

### 4.2 File Organization

The directory has **5 distinct linked-list implementations**:

1. `LinkedList.fst` — array-based, simplified, no delete
2. `SinglyLinkedList.fst` — heap-allocated singly-linked, full ops
3. `DLL.fst` — heap-allocated doubly-linked, full ops + segment predicate
4. `DoublyLinkedList.Complexity.fst` — singly-linked with ghost ticks (despite the "DoublyLinkedList" name!)
5. `DoublyLinkedList.Complexity.Enhanced.fst` — same as (4) with tighter bounds

**Finding F-10 (Medium Priority):** Files (4) and (5) are named `DoublyLinkedList.Complexity` but their node type has only `next` (no `prev`). They are singly-linked implementations. The naming is misleading. Should be renamed to `SinglyLinkedList.Complexity[.Enhanced]`.

### 4.3 Helper Lemma Duplication

`lemma_index_append`, `lemma_append_length` appear in both `Stack.fst` and `Queue.fst`. These could be factored into the `common/` directory.

### 4.4 Proof Techniques

- Stack/Queue: Uses `fold`/`unfold` of slprops with manual lemma invocation. Clean style.
- SinglyLinkedList: Uses `match` on `option` with `norewrite` pattern and ghost `cases_of_is_dlist`. Boilerplate-heavy but mechanical.
- DLL: Sophisticated `factor_dls`/`unfactor_dls` pattern for reading head node while preserving segment predicate. Well-designed.
- `delete_result` in DLL: Custom intermediate predicate for handling empty/non-empty results. Clean abstraction.
- Only one `#push-options` in the entire directory: `--z3rlimit 40` for `Queue.dequeue` (line 361). Proofs are tight.

---

## 5. Proof Quality

### 5.1 Admits and Assumes

**None.** Zero admits, zero assumes, zero sorry across all 3,720 lines. This is the strongest possible proof quality for a verified library.

Verified by grep:
```
grep -rn "admit\|assume\|sorry\|Admit\|ASSUME" *.fst *.fsti
```
Only hits are comments declaring "0 admits" and "NO admits".

### 5.2 Solver Options

| File | Option | Line |
|------|--------|------|
| Queue.fst | `#push-options "--z3rlimit 40"` | 361 |

This is modest and well-scoped (only for `dequeue`). No global rlimit inflation.

### 5.3 Proof Structure

- **Stack:** 7 helper lemmas (list-append indexing, init/last decomposition). All self-contained, well-documented.
- **Queue:** 10 helper lemmas (modular arithmetic, wraparound, circular indexing). Clean separation of concerns.
- **DLL:** Complex but well-structured ghost machinery. `factor_dls`/`unfactor_dls` is the key innovation enabling node-level operations on segment predicates. `dls_append` enables compositional reasoning.
- **Complexity variants:** Ghost tick counter (`GR.ref nat`) cleanly separates cost tracking from functional correctness. Ticks are placed at comparison points.

---

## 6. Documentation & Comments

### 6.1 README.md

**Finding F-11:** The README only covers the Stack and is partially stale:
- Line 18: Shows `A.array t` and `R.ref SZ.t` but the actual code uses `V.vec t` and `B.box SZ.t`.
- Line 28: Claims "The array stores elements in reverse order: `arr[i]` corresponds to `list[top-1-i]`" — this is **incorrect**. The actual invariant (Stack.fsti:32-33) stores `arr[i] == list[i]`, i.e., same order.
- Line 46: Claims push postcondition is `x :: old_contents` — **incorrect**. It is `L.append old_contents [x]`.
- Line 52: Claims pop postcondition is `old_contents == result :: new_contents` — **incorrect**. It is `L.append new_contents [result] == old_contents`.
- Line 74: Mentions "Admitted Proofs" — **stale**. There are no admits in the current code.
- Line 109: Warns about `A.alloc` and `R.alloc` being "deprecated and unsound" — **stale**. Code now uses `V.alloc` and `B.alloc`.

### 6.2 In-code Documentation

- Stack/Queue: Well-commented with clear CLRS references. ✅
- SinglyLinkedList: Has CLRS pseudocode in comments for LIST-INSERT, LIST-SEARCH. ✅
- DLL: Has CLRS section references and operation descriptions. ✅
- Complexity files: Have clear module-level docstrings. ✅
- `DS.Spec.fst`: Comprehensive docstrings with SNIPPET markers. ✅
- `LinkedList.Spec.fst`: Numbered sections. ✅

### 6.3 SNIPPET Markers

Well-placed `//SNIPPET_START`/`//SNIPPET_END` markers for documentation extraction in: Stack.fsti, Queue.fsti, SinglyLinkedList.fst, DLL.fst, DS.Spec.fst, DataStructures.Complexity.fst. ✅

---

## 7. Summary of Findings

| ID | Finding | Severity | Category |
|----|---------|----------|----------|
| F-1 | Imperative stack push = append; pure spec push = cons; no refinement connecting them | Low | Spec Gap |
| F-2 | Queue uses 3-field design (head+tail+size) vs CLRS 2-field (head+tail); not documented | Low | CLRS Fidelity |
| F-3 | `LinkedList.fst` is array-based, not pointer-based; misleading module name | Medium | Naming |
| F-4 | `SinglyLinkedList.fst` header mentions "originally mislabelled" — clean up comment | Low | Documentation |
| F-5 | No sentinel-based circular DLL (CLRS §10.2, Fig 10.4) | Low | CLRS Coverage |
| F-6 | No true O(1) LIST-DELETE given pointer; all deletes are O(n) | Medium | CLRS Fidelity |
| F-7 | Stack/Queue lack ghost-tick complexity proofs (unlike linked-list) | Low | Uniformity |
| F-8 | `DataStructures.Complexity.fst` lemmas are trivially true by definition | Low | Code Quality |
| F-9 | ~120 lines of ghost boilerplate duplicated 3× across SLL/Complexity files | **High** | Duplication |
| F-10 | `DoublyLinkedList.Complexity[.Enhanced]` are actually singly-linked | **High** | Naming |
| F-11 | README.md is stale: wrong types, wrong invariant description, mentions admits that don't exist | Medium | Documentation |

---

## 8. Actionable Task List

### Priority 1 — Critical (naming/duplication)

- [ ] **T-1: Fix misleading module names.** Rename `DoublyLinkedList.Complexity.fst` → `SinglyLinkedList.Complexity.fst` and `DoublyLinkedList.Complexity.Enhanced.fst` → `SinglyLinkedList.Complexity.Enhanced.fst`. These files use a singly-linked `node` type (no `prev` field). [F-10]

- [ ] **T-2: Extract shared SLL definitions.** Create `CLRS.Ch10.SinglyLinkedList.Base.fsti` containing: `node`, `dlist`, `is_dlist`, `is_dlist_cases`, `elim_is_dlist_nil`, `intro_is_dlist_nil`, `intro_is_dlist_cons`, `cases_of_is_dlist`, `is_dlist_case_none`, `is_dlist_case_some`, `remove_first`. Have `SinglyLinkedList.fst`, `SinglyLinkedList.Complexity.fst`, and `SinglyLinkedList.Complexity.Enhanced.fst` import it. Saves ~240 lines. [F-9]

### Priority 2 — Medium (correctness/fidelity)

- [ ] **T-3: Update README.md.** Fix all stale content: correct types (`V.vec`/`B.box`), correct invariant description (same-order, not reverse), correct push/pop specs, remove "Admitted Proofs" section, remove deprecated API warning. [F-11]

- [ ] **T-4: Rename or document `LinkedList.fst`.** Either rename to `ArrayBasedList.fst` or add prominent module-level comment explaining this is an array-based simplification, not the pointer-based linked list of CLRS §10.2. [F-3]

- [ ] **T-5: Add `list_delete` to `LinkedList.fst`.** The array-based list has insert and search but no delete. Either add it or document why it's omitted. [F-3]

- [ ] **T-6: Implement true O(1) pointer-based LIST-DELETE for DLL.** CLRS LIST-DELETE takes a pointer to the node and performs O(1) pointer surgery. The current `list_delete` does key-based search. The DLL `dls` predicate machinery (factor/unfactor) could support this with a `split_at_node` ghost operation. [F-6]

### Priority 3 — Low (polish/uniformity)

- [ ] **T-7: Add refinement lemma connecting imperative and pure stack specs.** Show that the imperative `L.append contents [x]` push convention is equivalent to the pure `x :: s` convention (via list reversal). [F-1]

- [ ] **T-8: Document queue 3-field design choice.** Add a comment in `Queue.fsti` noting the deviation from CLRS's 2-field (head+tail) design and why `size` was added. [F-2]

- [ ] **T-9: Factor common helper lemmas.** Move `lemma_index_append` and `lemma_append_length` (duplicated in Stack.fst and Queue.fst) to `common/`. [F-9]

- [ ] **T-10: Clean up SinglyLinkedList.fst header comment.** Remove "originally mislabelled" note, since the name is now correct. [F-4]

- [ ] **T-11: Consider sentinel DLL.** Implement CLRS §10.2 sentinel variant (circular DLL with `L.nil`) as an optional extension. [F-5]

- [ ] **T-12: Add ghost-tick complexity for Stack/Queue.** For uniformity with linked-list complexity proofs, add instrumented versions. [F-7]

- [ ] **T-13: Evaluate `DataStructures.Complexity.fst`.** The 11 lemmas prove trivially true statements (`1 = 1`, `n <= n`). Consider either removing or connecting to actual implementation cost bounds. [F-8]

- [ ] **T-14: Add test for SinglyLinkedList and DLL.** Currently only `Stack.Test`, `Queue.Test`, and `LinkedList.Test` exist. The SLL and DLL implementations have no test files. [Testing Gap]

---

## Appendix: File Inventory

| File | Lines | Purpose | Admits |
|------|-------|---------|--------|
| `CLRS.Ch10.Stack.fsti` | 75 | Stack interface | 0 |
| `CLRS.Ch10.Stack.fst` | 294 | Stack implementation | 0 |
| `CLRS.Ch10.Stack.Test.fst` | 34 | Stack test | 0 |
| `CLRS.Ch10.Queue.fsti` | 80 | Queue interface | 0 |
| `CLRS.Ch10.Queue.fst` | 438 | Queue implementation (z3rlimit 40 for dequeue) | 0 |
| `CLRS.Ch10.Queue.Test.fst` | 79 | Queue test (incl. wraparound) | 0 |
| `CLRS.Ch10.LinkedList.fsti` | 59 | Array-based list interface | 0 |
| `CLRS.Ch10.LinkedList.fst` | 183 | Array-based list (no delete) | 0 |
| `CLRS.Ch10.LinkedList.Spec.fst` | 224 | Pure linked-list spec (17 lemmas + theorem) | 0 |
| `CLRS.Ch10.LinkedList.Test.fst` | 28 | Linked list test | 0 |
| `CLRS.Ch10.SinglyLinkedList.fst` | 239 | Heap-allocated SLL (insert/search/delete) | 0 |
| `CLRS.Ch10.DLL.fst` | 1006 | True DLL with dls segment predicate | 0 |
| `CLRS.Ch10.DoublyLinkedList.Complexity.fst` | 262 | SLL + ghost ticks (misnamed "Doubly") | 0 |
| `CLRS.Ch10.DoublyLinkedList.Complexity.Enhanced.fst` | 291 | SLL + precise cost functions (misnamed "Doubly") | 0 |
| `CLRS.Ch10.DS.Spec.fst` | 332 | Pure specs: Stack/Queue/LinkedList | 0 |
| `CLRS.Ch10.DataStructures.Complexity.fst` | 96 | Op-count constants + trivial lemmas | 0 |
| **Total** | **3,720** | | **0** |
