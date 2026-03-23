# Prim Imperative MST — Remaining Work

## Status: 3 admits in CLRS.Ch23.Prim.Impl.fst

### Admit 1 (line ~800): prim_safe_add_vertex, minimality

Inside `arrow_to_impl` closure. Need: `new_edge.w ≤ e'.w` for all crossing edges.

- [x] Step 1a: `weights_edge_in_graph` — weight entry → graph edge (PROVEN)
- [x] Step 1b: `¬reachable old_es pu u` — path induction through MST-only edges (PROVEN)
- [ ] Step 1c: `new_edge.w ≤ e'.w` — minimality via key invariant
  - Need: bridge `e'.w` (graph edge) to `weights_seq[e'.u*n+e'.v]` via `weights_to_adj_preserves`
  - Need: determine which endpoint of `e'` is non-MST (at least one, since ¬reachable)
  - Chain: `key[u] ≤ key[non-MST] ≤ weights[MST*n+non-MST] = e'.w`
- [x] Step 1d: `greedy_step_safe` call + `subset_edges_transitive` chain (PROVEN)
- [x] u=source case (PROVEN)

### Admit 2 (line ~1023): Pulse fn body calling prim_safe_add_vertex

After `A.op_Array_Assignment in_mst u 1sz`, need to call `prim_safe_add_vertex`
with proper arguments. Need to establish all preconditions from loop state:

- [ ] Step 2a: Track extract-min minimality in extract-min loop invariant
  - `forall v < n. in_mst[v]=0 ==> key[u] ≤ key[v]`
- [ ] Step 2b: Track key invariant through outer loop  
  - `forall v w. v non-MST, w in-MST, weight(w,v) valid ==> key[v] ≤ weight(w,v)`
  - Maintained by update loop: `key[v] = min(key[v], weight(u,v))` for new MST vertex u
- [ ] Step 2c: Track parent[v] in MST for all in-MST non-source v
  - `forall v. v in-MST, v ≠ source ==> parent[v] in-MST`
- [ ] Step 2d: Track valid_weights from fn precondition
- [ ] Step 2e: Track key[u] > 0 (follows from key invariant: key = weight > 0)

### Admit 3 (line ~1125): Post-loop prim_mst_result establishment

After outer loop exits, derive prim_mst_result from prim_safe.

- [ ] Step 3a: Prove all non-source vertices in MST at loop end
  - For connected graph: each iteration adds one vertex (extract-min finds one)
  - Track `|in_mst vertices| = iter + 1` or just `iter = n → all in MST`
- [ ] Step 3b: `mst_edges_all_in` converts mst_edges_so_far to edges_from_parent_key (PROVEN helper)
- [ ] Step 3c: Derive is_mst from prim_safe + spanning tree properties
  - `prim_safe_elim` → `∃T. is_mst T ∧ subset_edges edges T`
  - Need `is_spanning_tree g edges` (subset g.edges, n-1 edges, connected, acyclic)
  - Need `noRepeats_edge edges` (from `lemma_pure_prim_noRepeats` pattern)
  - Apply `Bridge.safe_spanning_tree_is_mst g edges`
- [ ] Step 3d: `reveal_opaque prim_mst_result` inside `arrow_to_impl`

## Proven helpers (zero admits)

- `mst_edges_so_far`: edges for in-MST vertices only
- `mst_edges_all_in`: when all in MST, equals edges_from_parent_key
- `mst_edges_none_in`: when no non-source in MST, equals []
- `mst_edges_ext`: extensionality for non-MST vertex key/parent changes  
- `mst_edges_mem_implies_in_mst`: edge membership → in-MST vertex
- `mst_edges_in_mst_implies_mem`: in-MST vertex → edge membership
- `mst_edges_add_subset`: old MST edges ⊆ new MST edges when vertex added
- `subset_from_mem`: pointwise mem_edge → subset_edges
- `weights_edge_in_graph`: weight entry → graph edge
- `weights_to_adj_well_formed`: symmetric weights → well_formed_adj
- `prim_safe_init`, `prim_safe_elim`, `prim_safe_update_non_mst`
- `prim_mst_result`, `prim_mst_result_elim`

## Build performance

- Prim.Impl.fst: **30 seconds** via make
- fstar-mcp server at `http://127.0.0.1:3000/`: **18-30 seconds** incremental
