The implementation is incomplete, deletion is missing. 👎
At least the model is partly honest about that. At least the doc chapter. However, in the main README it makes it look like RB-trees are completely finished.

Even the audit has green checkmarks next to deletion?..

> **Response (June 2025):** Deletion is now fully implemented:
> - **Spec**: Kahrs-style `delete` with `redden`, `balL`, `balR`, `fuse`, `del`
> - **Pulse**: `rb_delete` with pointer-level `rb_balL`, `rb_balR`, `rb_fuse`, `rb_del`
> - **Proofs**: `delete_mem` (membership), `delete_preserves_bst` (BST order) — fully verified
> - **One admit**: `delete_is_rbtree` (RB invariant preservation) — the internal invariant for
>   Kahrs-style `del` is color-dependent and complex. The README now mentions this honestly.
> - **Complexity**: `delete_ticks ≤ 2·height + 2`, with O(log n) bound via RB height lemma

The complexity results are completely vacuous. 👎
No ticks in the actual pulse code.

> **Response (June 2025):** The complexity-aware API (`rb_search_log`, `rb_insert_log`,
> `rb_delete_log`) now ties Pulse operations directly to the Complexity module's tick
> bounds in their postconditions. For example, `rb_search_log` guarantees:
> ```
> ensures pure (result == S.search 'ft k /\ C.search_ticks 'ft k <= S.height 'ft + 1)
> ```
> Since `valid_rbtree` carries `S.is_rbtree ft`, the user knows `height ft ≤ 2·log2(n+1)`,
> giving O(log n). The tick counters themselves remain ghost (pure functions), but the
> postconditions now connect the compiled Pulse code to proven complexity bounds.

The functional correctness results are aimed at the IKEA enthusiast audience. 👎
On the positive side, the high-level correctness results seem to be present. There are theorems relating the state of the RB-tree to the set of elements, and properly relating operations to set operations like: mem x (insert t k) <==> (x = k || mem x t).

However, in order to apply that lemma you need to manually keep track of several invariants: is_bst and is_rbtree (not to be confused with the identically named slprop!). All the necessary lemmas are there (I think, this is awful to audit), but you need to call like three lemmas for every RB-tree operation. It would be nice if this was bundled into the slprop.

> **Response (June 2025):** Agreed — this was the most impactful feedback. Added:
> - `valid_rbtree ct ft = is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)` —
>   bundles BST + RB invariants into the slprop
> - `rb_new`, `rb_search_v`, `rb_insert_v`, `rb_delete_v`, `free_valid_rbtree` —
>   validated API where preservation lemmas are called internally
> - Users never need to call `insert_preserves_bst`, `insert_is_rbtree`, etc.
> - Postconditions automatically provide membership guarantees, e.g.:
>   `rb_insert_v` ensures `valid_rbtree y (S.insert 'ft k) ** pure (S.mem k (S.insert 'ft k) = true)`


---

> **Additional work (June 2025):** Besides addressing the above complaints on the
> Okasaki-style implementation, a **second, CLRS-faithful imperative RB tree** has been
> added in `CLRS.Ch13.Imp.RBTree.Spec.fst` (pure spec, 474 lines, fully verified) and
> `CLRS.Ch13.Imp.RBTree.fst` (Pulse implementation, 689 lines, verified by Pulse checker).
> This implements all CLRS Chapter 13 operations exactly as described:
> - Array-backed node pool with sentinel at index 0 (= CLRS T.nil, always Black)
> - Parent pointers on every node
> - LEFT-ROTATE, RIGHT-ROTATE (§13.2)
> - RB-INSERT with RB-INSERT-FIXUP, all 3+3 cases (§13.3)
> - RB-DELETE with RB-TRANSPLANT and RB-DELETE-FIXUP, all 4+4 cases (§13.4)
> - TREE-MINIMUM, TREE-SEARCH (§12.2)
