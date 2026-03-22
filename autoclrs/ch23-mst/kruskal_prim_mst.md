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

## Prim is_mst — Pure spec MST proven ✅, imperative bridge IN PROGRESS

### Done
- [x] Add key_parent_consistent to prim_correct (opaque prim_kpc wrapper)
- [x] Track prim_kpc through all three loops
- [x] Add well_formed_adj_intro, has_edge_intro, adj_to_graph_edges to Prim.Spec
- [x] Strengthen adj_to_graph_edges_valid to include e.u <> e.v
- [x] Add pure_prim_is_mst to Prim.Spec (1 admit: noRepeats_edge)
- [x] Create ImplTestHelper with test_prim_mst
- [x] ImplTest calls test_prim_mst() → is_mst for pure_prim output

### Remaining admit
- [ ] noRepeats_edge for pure_prim output (in pure_prim_is_mst)
  - Known true: each edge has unique child vertex, no 2-cycles in parent tree
  - Proof needs tracking addition order through pure_prim recursion
