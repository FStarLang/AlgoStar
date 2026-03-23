# Prim Imperative MST — Remaining Work

## Status: 3 admits in CLRS.Ch23.Prim.Impl.fst

### Admit 1 (line 664): prim_safe_add_vertex, u ≠ source case

Inside `arrow_to_impl` closure with `symmetric_weights` and `all_connected` available.
Need to apply `Bridge.greedy_step_safe` on `new_edge` and `old_es` to get
`∃T'. is_mst T' ∧ subset_edges (new_edge :: old_es) T'`, then chain with
`subset_edges new_es (new_edge :: old_es)` via `subset_edges_transitive`.

#### Step 1a: Prove new_edge ∈ g.edges
- `key_parent_consistent` gives `key[u] = weights[parent[u]*n+u]`
- `key[u] < infinity` (from precondition)
- `key[u] > 0` (need to prove: weight of a real edge is positive)
- `weights_to_adj_preserves` (exists in Impl.fst) bridges weights_seq → adj matrix
- `adj_to_graph_has_edge` (in Spec.fsti) gives mem_edge for adj matrix
- With `symmetric_weights`: ensure `pu < u` or `u < pu` for adj_to_graph_has_edge
  (adj_to_graph only emits u < v edges; use edge_eq symmetry)
- Need helper: `weights_edge_in_graph weights_seq n pu u`
  → `mem_edge {pu, u, key[u]} g.edges`

#### Step 1b: Prove ¬reachable old_es pu u
- Every edge in old_es has both endpoints in MST (from mst_edges_mem_implies_in_mst)
- u is not in MST (from precondition: `in_mst_old[u] ≠ 1`)
- Any path in old_es from pu to u would visit u — contradiction
- Need lemma: `mst_edges_endpoints_in_mst` (for all e in old_es, e.u and e.v are in MST)
- Then: if reachable old_es pu u, the path has subset_edges path old_es,
  and path ends at u. Last edge has one endpoint = u. But u not in MST, contradiction.
- Actually: need to prove this for all edges on the path, not just in old_es.
  Use `edge_eq_endpoints` + `mst_edges_mem_implies_in_mst` for each path edge.

#### Step 1c: Prove new_edge.w ≤ e'.w for all crossing graph edges e'
- Crossing edge e' has e'.u in MST, e'.v not in MST (or vice versa via edge_eq)
- `key[e'.v] ≤ weight(e'.u, e'.v)` from key invariant precondition
- `key[u] ≤ key[e'.v]` from extract-min precondition
- Need to connect graph edge weight to weights_seq: for mem_edge e' g.edges,
  `e'.w = adj_matrix[e'.u][e'.v]` which maps back to weights_seq entry
- With symmetric_weights: `e'.w = weights_seq[e'.u*n+e'.v]`
- Chain: `new_edge.w = key[u] ≤ key[e'.v] ≤ weights[e'.u*n+e'.v] = e'.w`

#### Step 1d: Apply greedy_step_safe and chain subsets
- Call `Bridge.greedy_step_safe g old_es new_edge` with steps 1a-1c
- Get `∃T'. is_mst T' ∧ subset_edges (new_edge :: old_es) T'`
- Have `subset_edges new_es (new_edge :: old_es)` (already proven)
- Apply `subset_edges_transitive new_es (new_edge :: old_es) T'`
- Get `∃T'. is_mst T' ∧ subset_edges new_es T'` → `prim_safe ... in_mst_new ...`

### Admit 2 (line 869): Pulse fn body calling prim_safe_add_vertex

After `A.op_Array_Assignment in_mst u 1sz`, need to call `prim_safe_add_vertex`
with proper arguments. Need to establish all preconditions:

#### Step 2a: Track extract-min minimality
- The extract-min loop finds u = argmin key[v] among non-MST vertices
- Need to track this in the extract-min loop invariant:
  `(min_key > 0 ==> forall v. v < scan_pos ∧ in_mst[v]=0 ==> key[u] ≤ key[v])`
- After loop: `forall v. v < n ∧ in_mst[v]=0 ==> key[u] ≤ key[v]`

#### Step 2b: Track key invariant through update loop
- Before iteration i: key[v] ≤ weight(w,v) for all MST vertices w processed so far
- After adding MST vertex w and updating: key[v] = min(key[v], weight(w,v))
- Need opaque predicate `prim_key_inv` tracked through outer loop
- Init: key = infinity for non-source → vacuously true (no MST vertices have edges yet)
- Step: after update loop, key[v] ≤ weight(w,v) for the newly added w is ensured by
  the update condition (key[v] = min(old_key[v], weight(w,v)))

#### Step 2c: Track parent[u] in MST
- parent[u] is set during update loop when key[u] is updated
- parent[u] = w where w is the MST vertex that gave minimum weight
- w is in MST at the time parent[u] is set
- parent[u] stays the same (not updated again unless a better weight found,
  but only from MST vertices)
- Need to track `in_mst[parent[v]] = 1` for non-MST vertices with finite key

### Admit 3 (line 981): Post-loop prim_mst_result establishment

After outer loop exits (iter = n), derive prim_mst_result from prim_safe.

#### Step 3a: Prove all non-source vertices are in MST at loop end
- For connected graph: each iteration adds one new vertex (extract-min finds one)
- After n iterations: all n vertices in MST
- Need to track `|{v : in_mst[v]=1}| = iter + 1` (including source)
- Or simpler: track `iter = n` at loop exit + connected → all in MST

#### Step 3b: Convert mst_edges_so_far to edges_from_parent_key
- `mst_edges_all_in` (already proven): when all non-source have in_mst=1,
  mst_edges_so_far = edges_from_parent_key
- Need `forall v. v <> source ==> in_mst[v] = 1` (from step 3a)

#### Step 3c: Derive is_mst from prim_safe + spanning tree properties
- `prim_safe_elim` gives `∃T. is_mst T ∧ subset_edges edges T`
- Need `is_spanning_tree g edges` (subset g.edges, n-1 edges, connected, acyclic)
- `noRepeats_edge edges` (from parent tree structure, similar to pure_prim proof)
- Apply `Bridge.safe_spanning_tree_is_mst g edges`

#### Step 3d: Establish prim_mst_result predicate
- `reveal_opaque` + the is_mst derivation from 3c
- Inside `arrow_to_impl` conditioned on symmetric + connected
