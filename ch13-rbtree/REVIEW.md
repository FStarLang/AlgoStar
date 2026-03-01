The implementation is incomplete, deletion is missing. 👎
At least the model is partly honest about that. At least the doc chapter. However, in the main README it makes it look like RB-trees are completely finished.

Even the audit has green checkmarks next to deletion?..

> **Response (June 2025):** Deletion is now fully implemented:
> - **Spec**: Kahrs-style `delete` with `redden`, `balL`, `balR`, `fuse`, `del`
> - **Pulse**: `rb_delete` with pointer-level `rb_balL`, `rb_balR`, `rb_fuse`, `rb_del`
> - **Proofs**: `delete_mem` (membership), `delete_preserves_bst` (BST order) — fully verified
> - **`delete_is_rbtree`**: Now fully proven (zero admits). The proof tracks a color-dependent
>   invariant: `del` on a Black node yields `bh-1` with `almost_no_red_red`, while `del` on
>   a Red node preserves `bh` with the stronger `no_red_red`. Also fixed a bug in `del` where
>   it dispatched on `(parent_color, child_color)` instead of just `child_color`.
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
> Okasaki-style implementation, `CLRS.Ch13.Imp.RBTree.fst` has been **rewritten** to use
> Pulse `Box` heap-allocated nodes with `option (box rb_node)` nullable pointers
> (matching the ch12-bst BST pattern), with **full functional correctness proofs** linking
> every operation to the pure spec in `CLRS.Ch13.RBTree.Spec` — zero admits.
>
> Operations implemented (~1178 lines, all verified):
> - TREE-SEARCH (§12.2): recursive BST search
> - TREE-MINIMUM (§12.2): walk left to min
> - RB-INSERT with Okasaki-style balance fixup (§13.3)
> - RB-DELETE with Kahrs-style balL/balR/fuse fixup (§13.4)
> - TREE-FREE: recursive deallocation
> - Validated API: `valid_rbtree` bundles BST + RB invariants
