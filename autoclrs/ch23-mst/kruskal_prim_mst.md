# Kruskal & Prim MST — Shared Infrastructure and Progress

## Reusable Lemmas (currently in Kruskal.Impl.fst, should be in shared module)

- [x] `pigeonhole_edges`: subset + same length + noRepeats → reverse subset
- [x] `remove_edge_first` + length/mem/subset lemmas
- [x] `all_connected_from_superset`: connectivity lifts to supersets
- [x] `edge_in_list_reachable`: mem_edge → reachable
- [x] `all_edges_distinct_append_single`: noRepeats + new element → noRepeats for append
- [x] `aed_eq_noRepeats`: all_edges_distinct == Bridge.noRepeats_edge

## Reusable from Bridge (already generic)

- [x] `greedy_step_safe`: adding min cross-component edge preserves safety
- [x] `safe_spanning_tree_is_mst`: safe spanning tree IS an MST
- [x] `noRepeats_edge`: no duplicate edges predicate

## Kruskal is_mst — COMPLETE ✅

- [x] Build fixes (Defs intro lemma, quantifier gaps)
- [x] Graph-theory lemmas (find_same_along_path, adj_pos, etc.)
- [x] Loop invariant: all_edges_distinct + (connected ⟹ ec == round)
- [x] Post-loop: derive_is_mst_post_loop (pigeonhole approach)
- [x] kruskal_mst_result gives is_mst
- [x] ImplTest asserts is_mst

## Prim is_mst — IN PROGRESS

### Done
- [x] Add key_parent_consistent to prim_correct (opaque prim_kpc wrapper)
- [x] Track prim_kpc through all three loops
- [x] ImplTest updated

### Factoring: Move reusable lemmas to shared module
- [ ] Create CLRS.Ch23.MST.Lemmas.fst with pigeonhole, remove_edge_first, etc.
- [ ] Update Kruskal.Impl to use shared module
- [ ] Prim.Impl imports shared module

### Prim-specific lemmas needed
- [ ] `edges_from_parent_key_length`: length = n-1 (straightforward recursion)
- [ ] `edges_from_parent_key_no_self_loops`: parent[v] ≠ v for non-source (from key_parent_consistent + no_self_loops)
- [ ] `edges_from_parent_key_subset_graph`: edges are in adj_to_graph (from key_parent_consistent + valid_weights)
- [ ] `edges_from_parent_key_noRepeats`: no duplicate edges (each edge unique by vertex v)

### Prim loop invariant strengthening
- [ ] Define `prim_safety_inv`: track edges_safe through outer loop
  - Init: empty edge set is safe (subset of any MST)
  - Step: use greedy_step_safe with cut = (in_mst, not-in_mst)
  - Need: show selected vertex u's edge is minimum weight crossing cut
- [ ] Track `prim_tree_inv`: accumulated edges form a tree
  - Acyclic: parent tree has no cycles
  - Connected: each vertex reachable from source via parent edges
- [ ] Track vertex count: iter == number of vertices added

### Post-loop derivation
- [ ] From prim_safety_inv: edges_safe
- [ ] From prim_tree_inv + iter==n: is_spanning_tree
- [ ] Combine: safe_spanning_tree_is_mst → is_mst
- [ ] Add conditional is_mst to prim_correct
- [ ] Export prim_mst_result_elim in Impl.fsti

### ImplTest
- [ ] Assert is_mst for test graph from imperative prim output
