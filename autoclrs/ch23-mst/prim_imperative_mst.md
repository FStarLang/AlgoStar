# Prim Imperative MST — Remaining Work

## Status: 2 admits in CLRS.Ch23.Prim.Impl.fst (core greedy proof DONE)

### Admit 1 (line ~1077): Pulse fn body calling prim_safe_add_vertex

Need to establish prim_safe_add_vertex preconditions from Pulse loop state.
Currently tracked in outer loop: prim_safe, prim_kpc, parent_valid, all_keys_bounded.

Missing — need new opaque loop invariants:
- [ ] Extract-min minimality: `key[u] ≤ key[v]` for all non-MST v
  (track in extract-min inner loop, carry to outer loop body)
- [ ] Key invariant: `key[v] ≤ weights[w*n+v]` for MST w, non-MST v
  (init: key=infinity, trivially true; maintained by update loop: key[v]=min(old,weight(u,v)))
- [ ] Parent-in-MST: `in_mst[parent[v]]=1` for all in-MST non-source v
  (init: only source in MST; step: parent[v] set to u which is in MST)
- [ ] valid_weights, no_zero_edges from fn prim precondition (carry through)
- [ ] key[u] > 0 (follows from key invariant: key = min weight from MST, weights > 0)
- [ ] in_mst[u] ≠ 1 (extract-min picks non-MST vertex)
- [ ] key[u] < infinity (extract-min found finite key)

### Admit 2 (line ~1189): Post-loop prim_mst_result derivation

After outer loop exits, derive prim_mst_result from prim_safe.

- [ ] All non-source vertices in MST at loop end (connected graph → each iter adds one)
- [ ] mst_edges_all_in conversion (PROVEN helper)
- [ ] Spanning tree properties: n-1 edges, connected, acyclic, subset g.edges
- [ ] noRepeats_edge (from parent tree structure or pigeonhole)
- [ ] safe_spanning_tree_is_mst → is_mst

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
