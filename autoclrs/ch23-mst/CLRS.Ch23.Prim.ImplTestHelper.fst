(*
   Proves the MST theorem for the concrete 3-vertex triangle test graph
   using the pure Prim specification.
   NO admits.
*)
module CLRS.Ch23.Prim.ImplTestHelper

open FStar.Mul
open FStar.Seq
open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module Seq = FStar.Seq

let test_adj : adj_matrix = Seq.seq_of_list [
  Seq.seq_of_list [0; 1; 3];
  Seq.seq_of_list [1; 0; 2];
  Seq.seq_of_list [3; 2; 0]
]

#push-options "--fuel 10 --ifuel 10 --z3rlimit 10"

let test_well_formed () : Lemma (well_formed_adj test_adj 3) =
  assert_norm (Seq.length test_adj == 3);
  assert_norm (Seq.length (Seq.index test_adj 0) == 3);
  assert_norm (Seq.length (Seq.index test_adj 1) == 3);
  assert_norm (Seq.length (Seq.index test_adj 2) == 3);
  introduce forall (u: nat). u < 3 ==> Seq.length (Seq.index test_adj u) = 3
  with introduce _ ==> _ with _. (if u = 0 then () else if u = 1 then () else ());
  assert_norm (Seq.index (Seq.index test_adj 0) 0 = 0);
  assert_norm (Seq.index (Seq.index test_adj 0) 1 = 1);
  assert_norm (Seq.index (Seq.index test_adj 0) 2 = 3);
  assert_norm (Seq.index (Seq.index test_adj 1) 0 = 1);
  assert_norm (Seq.index (Seq.index test_adj 1) 1 = 0);
  assert_norm (Seq.index (Seq.index test_adj 1) 2 = 2);
  assert_norm (Seq.index (Seq.index test_adj 2) 0 = 3);
  assert_norm (Seq.index (Seq.index test_adj 2) 1 = 2);
  assert_norm (Seq.index (Seq.index test_adj 2) 2 = 0);
  well_formed_adj_intro test_adj 3

let test_connected () : Lemma (all_connected 3 (adj_to_edges test_adj 3)) =
  test_well_formed ();
  adj_to_graph_edges test_adj 3;
  let g = adj_to_graph test_adj 3 in
  let es = g.edges in
  // Establish has_edge for concrete edges
  assert_norm (Seq.index (Seq.index test_adj 0) 1 = 1);
  assert_norm (1 <> infinity);
  assert_norm (Seq.length (Seq.index test_adj 0) == 3);
  has_edge_intro test_adj 3 0 1;
  adj_to_graph_has_edge test_adj 3 0 1;
  assert_norm (Seq.index (Seq.index test_adj 1) 2 = 2);
  assert_norm (2 <> infinity);
  assert_norm (Seq.length (Seq.index test_adj 1) == 3);
  has_edge_intro test_adj 3 1 2;
  adj_to_graph_has_edge test_adj 3 1 2;
  let e01 : edge = {u=0; v=1; w=1} in
  let e12 : edge = {u=1; v=2; w=2} in
  edge_eq_reflexive e01;
  edge_eq_reflexive e12;
  // Build paths using graph edges
  assert (is_path_from_to [] 0 0);
  assert (subset_edges [] es);
  assert (is_path_from_to [e01] 0 1);
  assert (subset_edges [e01] es);
  assert (is_path_from_to [e01; e12] 0 2);
  assert (subset_edges [e01; e12] es)

let test_valid_edges () : Lemma
  (forall (e: edge). mem_edge e (adj_to_graph test_adj 3).edges ==>
    e.u < 3 /\ e.v < 3 /\ e.u <> e.v)
  = let aux (e: edge) : Lemma
      (requires mem_edge e (adj_to_graph test_adj 3).edges)
      (ensures e.u < 3 /\ e.v < 3 /\ e.u <> e.v)
      = adj_to_graph_edges_valid test_adj 3 e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The MST theorem: pure_prim produces MST for the test graph
let test_prim_mst () : Lemma
  (is_mst (adj_to_graph test_adj 3) (pure_prim test_adj 3 0))
  = test_well_formed ();
    test_connected ();
    test_valid_edges ();
    pure_prim_is_mst test_adj 3 0

#pop-options

open FStar.SizeT
module SZ = FStar.SizeT
open CLRS.Ch23.Prim.Impl
open CLRS.Ch23.Prim.Defs

let tw : Seq.seq SZ.t = Seq.seq_of_list [0sz; 1sz; 3sz; 1sz; 0sz; 2sz; 3sz; 2sz; 0sz]

// Direct case analysis: given key = tw[parent*3+v] with parent<3,
// enumerate all possibilities
#push-options "--z3rlimit 5"
let key_from_parent_1 (k p: nat)
  : Lemma (requires p < 3 /\ k < 65535 /\
                    k == SZ.v (Seq.index tw (p * 3 + 1)))
          (ensures (p == 0 /\ k == 1) \/ (p == 1 /\ k == 0) \/ (p == 2 /\ k == 2))
  = assert_norm (SZ.v (Seq.index tw 1) == 1);
    assert_norm (SZ.v (Seq.index tw 4) == 0);
    assert_norm (SZ.v (Seq.index tw 7) == 2)

let key_from_parent_2 (k p: nat)
  : Lemma (requires p < 3 /\ k < 65535 /\
                    k == SZ.v (Seq.index tw (p * 3 + 2)))
          (ensures (p == 0 /\ k == 3) \/ (p == 1 /\ k == 2) \/ (p == 2 /\ k == 0))
  = assert_norm (SZ.v (Seq.index tw 2) == 3);
    assert_norm (SZ.v (Seq.index tw 5) == 2);
    assert_norm (SZ.v (Seq.index tw 8) == 0)
#pop-options

// Instantiate key_parent_consistent at specific vertex
let kpc_at (ks ps ws: Seq.seq SZ.t) (v: nat)
  : Lemma
    (requires key_parent_consistent ks ps ws 3 0 /\
              Seq.length ks == 3 /\ Seq.length ps == 3 /\ Seq.length ws == 9 /\
              parent_valid ps 3 /\ v < 3 /\ v <> 0 /\
              SZ.v (Seq.index ks v) < SZ.v CLRS.Ch23.Prim.Defs.infinity)
    (ensures SZ.v (Seq.index ks v) == SZ.v (Seq.index ws (SZ.v (Seq.index ps v) * 3 + v)))
  = ()

// Main lemma: combine kpc instantiation with case analysis
// prim_correct doesn't uniquely determine the output without is_mst.
// With key < infinity, kpc gives k = tw[p*3+v].
// Case analysis shows all valid (k,p) pairs. 
// The ensures just says k1=1,p1=0,k2=2,p2=1 — Z3 must eliminate other possibilities.
// Elimination: k1=0 → self-loop (p1=1), excluded because we assert k1==1.
// Actually the ensures is the CONCLUSION. Z3 must DERIVE it.
// Without is_mst, k1=0/p1=1 and k1=2/p1=2 are both valid. prim_correct allows all.
// We CANNOT derive unique values from prim_correct alone!
// We need prim_mst_result to force the minimum.
// For now, settle for proving key/parent CONSISTENCY (k matches the weight).
#push-options "--z3rlimit 5"
let prim_consistent_output (ks ps ws: Seq.seq SZ.t)
  : Lemma
    (requires prim_correct ks ps ws 3 0 /\ ws == tw /\
              SZ.v (Seq.index ks 1) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
              SZ.v (Seq.index ks 2) < SZ.v CLRS.Ch23.Prim.Defs.infinity)
    (ensures (let k1 = SZ.v (Seq.index ks 1) in let p1 = SZ.v (Seq.index ps 1) in
              let k2 = SZ.v (Seq.index ks 2) in let p2 = SZ.v (Seq.index ps 2) in
              ((p1 == 0 /\ k1 == 1) \/ (p1 == 1 /\ k1 == 0) \/ (p1 == 2 /\ k1 == 2)) /\
              ((p2 == 0 /\ k2 == 3) \/ (p2 == 1 /\ k2 == 2) \/ (p2 == 2 /\ k2 == 0))))
  = kpc_at ks ps ws 1;
    kpc_at ks ps ws 2;
    key_from_parent_1 (SZ.v (Seq.index ks 1)) (SZ.v (Seq.index ps 1));
    key_from_parent_2 (SZ.v (Seq.index ks 2)) (SZ.v (Seq.index ps 2))
#pop-options

// With prim_consistent_output giving 3 possibilities per vertex (9 total),
// and is_mst forcing minimum total weight:
// k1+k2 must be minimized. Possible totals:
//   (1,3)=4  (1,2)=3  (1,0)=1  (0,3)=3  (0,2)=2  (0,0)=0  (2,3)=5  (2,2)=4  (2,0)=2
// Self-loop cases (k=0): p=v, edge (v,v) weight 0. These create self-loops
// which aren't valid MST edges. But prim_correct doesn't exclude them.
// However, is_mst says the edges form a spanning tree = connected + acyclic + n-1 edges.
// Self-loop edges make the tree non-spanning (vertex not reachable through non-self edges).
// Without explicitly using is_mst, prim_correct constrains to the 3 cases per vertex.
// The Prim algorithm specifically picks minimum keys, so it picks k1=1, k2=2.
// We can verify this from prim_correct: the ensures of prim_correct does NOT
// guarantee uniqueness. To get uniqueness, we need is_mst.
//
// For this test, prim_consistent_output + finite keys is sufficient to verify
// that the output is ONE OF the valid parent trees. The C test driver
// verifies the EXACT values at runtime.

/// Pin down unique MST: no self-loops + minimum total weight → k1=1, k2=2
#push-options "--z3rlimit 5"
let prim_unique_output (ks ps ws: Seq.seq SZ.t)
  : Lemma
    (requires prim_correct ks ps ws 3 0 /\ ws == tw /\
              SZ.v (Seq.index ks 1) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
              SZ.v (Seq.index ks 2) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
              SZ.v (Seq.index ps 1) <> 1 /\
              SZ.v (Seq.index ps 2) <> 2 /\
              SZ.v (Seq.index ks 1) + SZ.v (Seq.index ks 2) <= 3)
    (ensures
      SZ.v (Seq.index ks 1) == 1 /\ SZ.v (Seq.index ps 1) == 0 /\
      SZ.v (Seq.index ks 2) == 2 /\ SZ.v (Seq.index ps 2) == 1)
  = prim_consistent_output ks ps ws
#pop-options


#push-options "--fuel 4 --ifuel 2 --z3rlimit 5"
let efpk_3 (ps ks: Seq.seq SZ.t)
  : Lemma (requires Seq.length ps == 3 /\ Seq.length ks == 3)
          (ensures edges_from_parent_key ps ks 3 0 0 ==
                   [{u=SZ.v (Seq.index ps 1); v=1; w=SZ.v (Seq.index ks 1)};
                    {u=SZ.v (Seq.index ps 2); v=2; w=SZ.v (Seq.index ks 2)}])
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 150 --split_queries always"
let mst_edge_facts (ps ks ws: Seq.seq SZ.t)
  : Lemma
    (requires Seq.length ps == 3 /\ Seq.length ks == 3 /\ Seq.length ws == 9 /\ ws == tw /\
              is_mst (CLRS.Ch23.Prim.Spec.adj_to_graph (weights_to_adj_matrix ws 3) 3)
                     (edges_from_parent_key ps ks 3 0 0))
    (ensures SZ.v (Seq.index ps 1) <> 1 /\ SZ.v (Seq.index ps 2) <> 2 /\
             SZ.v (Seq.index ks 1) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
             SZ.v (Seq.index ks 2) < SZ.v CLRS.Ch23.Prim.Defs.infinity)
  = efpk_3 ps ks;
    let adj = weights_to_adj_matrix ws 3 in
    let g = CLRS.Ch23.Prim.Spec.adj_to_graph adj 3 in
    let e1 : edge = {u=SZ.v (Seq.index ps 1); v=1; w=SZ.v (Seq.index ks 1)} in
    let e2 : edge = {u=SZ.v (Seq.index ps 2); v=2; w=SZ.v (Seq.index ks 2)} in
    edge_eq_reflexive e1; edge_eq_reflexive e2;
    mem_edge_subset e1 (edges_from_parent_key ps ks 3 0 0) g.edges;
    mem_edge_subset e2 (edges_from_parent_key ps ks 3 0 0) g.edges;
    CLRS.Ch23.Prim.Spec.adj_to_graph_edges_valid adj 3 e1;
    CLRS.Ch23.Prim.Spec.adj_to_graph_edges_valid adj 3 e2;
    CLRS.Ch23.Prim.Spec.well_formed_adj_intro adj 3;
    CLRS.Ch23.Prim.Spec.adj_to_graph_edge_weight adj 3 e1;
    CLRS.Ch23.Prim.Spec.adj_to_graph_edge_weight adj 3 e2;
    assert_norm (SZ.v (Seq.index tw 0) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 1) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 2) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 3) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 4) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 5) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 6) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 7) < SZ.v CLRS.Ch23.Prim.Defs.infinity);
    assert_norm (SZ.v (Seq.index tw 8) < SZ.v CLRS.Ch23.Prim.Defs.infinity)
#pop-options

/// Witness: [{u=0;v=1;w=1}; {u=1;v=2;w=2}] is a spanning tree with weight 3
#push-options "--fuel 10 --ifuel 10 --z3rlimit 20"
let witness_spanning_tree ()
  : Lemma
    (let adj = weights_to_adj_matrix tw 3 in
     let g = CLRS.Ch23.Prim.Spec.adj_to_graph adj 3 in
     let t : list edge = [{u=0;v=1;w=1}; {u=1;v=2;w=2}] in
     is_spanning_tree g t /\ total_weight t == 3)
  = let adj = weights_to_adj_matrix tw 3 in
    let g = CLRS.Ch23.Prim.Spec.adj_to_graph adj 3 in
    let e01 : edge = {u=0; v=1; w=1} in
    let e12 : edge = {u=1; v=2; w=2} in
    let t : list edge = [e01; e12] in
    CLRS.Ch23.Prim.Spec.adj_to_graph_edges adj 3;
    CLRS.Ch23.Prim.Spec.well_formed_adj_intro adj 3;
    // Both edges are in the graph
    CLRS.Ch23.Prim.Spec.has_edge_intro adj 3 0 1;
    CLRS.Ch23.Prim.Spec.adj_to_graph_has_edge adj 3 0 1;
    CLRS.Ch23.Prim.Spec.has_edge_intro adj 3 1 2;
    CLRS.Ch23.Prim.Spec.adj_to_graph_has_edge adj 3 1 2;
    edge_eq_reflexive e01; edge_eq_reflexive e12;
    // Connectivity: paths from 0 to all vertices
    assert (is_path_from_to ([] <: list edge) 0 0);
    assert (subset_edges ([] <: list edge) t);
    assert (is_path_from_to [e01] 0 1);
    assert (subset_edges [e01] t);
    assert (is_path_from_to [e01; e12] 0 2);
    assert (subset_edges [e01; e12] t);
    // Acyclicity: build up from empty list
    acyclic_when_unreachable 3 [] e12;
    acyclic_when_unreachable 3 [e12] e01
#pop-options

/// Total weight: from is_mst + witness spanning tree, k1+k2 ≤ 3
#push-options "--fuel 4 --ifuel 2 --z3rlimit 5"
let mst_total_weight (ks ps ws: Seq.seq SZ.t)
  : Lemma
    (requires Seq.length ps == 3 /\ Seq.length ks == 3 /\ Seq.length ws == 9 /\ ws == tw /\
              is_mst (CLRS.Ch23.Prim.Spec.adj_to_graph (weights_to_adj_matrix ws 3) 3)
                     (edges_from_parent_key ps ks 3 0 0))
    (ensures SZ.v (Seq.index ks 1) + SZ.v (Seq.index ks 2) <= 3)
  = efpk_3 ps ks;
    witness_spanning_tree ()
#pop-options

#push-options "--z3rlimit 5"
let mst_test_facts (ps ks ws: Seq.seq SZ.t)
  : Lemma
    (requires prim_correct ks ps ws 3 0 /\ ws == tw /\
              prim_mst_result ps ks ws 3 0 /\
              symmetric_weights ws 3 /\
              all_connected 3 (CLRS.Ch23.Prim.Spec.adj_to_edges (weights_to_adj_matrix ws 3) 3))
    (ensures
      SZ.v (Seq.index ks 1) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
      SZ.v (Seq.index ks 2) < SZ.v CLRS.Ch23.Prim.Defs.infinity /\
      SZ.v (Seq.index ps 1) <> 1 /\
      SZ.v (Seq.index ps 2) <> 2 /\
      SZ.v (Seq.index ks 1) + SZ.v (Seq.index ks 2) <= 3)
  = prim_mst_result_elim ps ks ws 3 0;
    mst_edge_facts ps ks ws;
    mst_total_weight ks ps ws
#pop-options
