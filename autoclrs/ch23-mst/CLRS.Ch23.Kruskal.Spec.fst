(*
   CLRS Chapter 23: Kruskal's Algorithm - Pure Specification
   
   This module provides a pure functional specification of Kruskal's MST algorithm.
   Key components:
   1. Edge sorting
   2. Pure Kruskal algorithm specification
   3. Correctness properties using cut property from CLRS.Ch23.MST.Spec
   
   Connected component logic is in CLRS.Ch23.Kruskal.Components.
*)

module CLRS.Ch23.Kruskal.Spec

open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Components

(*** Edge Sorting ***)

// Properties of sorted edges
let rec insert_edge_mem (e e': edge) (sorted: list edge)
  : Lemma (ensures mem_edge e' (insert_edge e sorted) <==>
                   (edge_eq e e' || mem_edge e' sorted))
  = match sorted with
    | [] -> ()
    | hd :: tl ->
      if e.w <= hd.w then ()
      else insert_edge_mem e e' tl

let rec sort_edges_mem (e: edge) (edges: list edge)
  : Lemma (ensures mem_edge e (sort_edges edges) <==> mem_edge e edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | hd :: tl ->
      sort_edges_mem e tl;
      insert_edge_mem hd e (sort_edges tl)

// Sorted list contains same edges as original
let rec sort_edges_subset_forward (edges: list edge)
  : Lemma (ensures subset_edges (sort_edges edges) edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_subset_forward rest;
      // Need to show: every edge in (insert_edge e (sort_edges rest)) is in (e :: rest)
      let rec insert_forward (e: edge) (sorted: list edge) (orig: list edge)
        : Lemma (requires subset_edges sorted orig)
                (ensures subset_edges (insert_edge e sorted) (e :: orig))
                (decreases sorted)
        = match sorted with
          | [] -> 
            mem_edge_hd e orig
          | hd :: tl ->
            if e.w <= hd.w then begin
              mem_edge_hd e orig;
              subset_edges_cons (hd :: tl) e orig
            end else begin
              insert_forward e tl orig;
              assert (mem_edge hd sorted);
              mem_edge_subset hd sorted orig;
              subset_edges_cons (insert_edge e tl) hd (e :: orig)
            end
      in
      insert_forward e (sort_edges rest) rest

let rec sort_edges_subset_backward (edges: list edge)
  : Lemma (ensures subset_edges edges (sort_edges edges))
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_subset_backward rest;
      // Need: subset_edges (e :: rest) (insert_edge e (sort_edges rest))
      // We have: subset_edges rest (sort_edges rest)
      // We need to show: 
      // 1. mem_edge e (insert_edge e (sort_edges rest))
      // 2. subset_edges rest (insert_edge e (sort_edges rest))
      
      // Part 1: e is in insert_edge e sorted for any sorted
      let rec e_in_insert (e: edge) (sorted: list edge)
        : Lemma (ensures mem_edge e (insert_edge e sorted))
                (decreases sorted)
        = match sorted with
          | [] -> mem_edge_hd e []
          | hd :: tl ->
            if e.w <= hd.w then mem_edge_hd e (hd :: tl)
            else e_in_insert e tl
      in
      e_in_insert e (sort_edges rest);
      
      // Part 2: rest ⊆ sort_edges rest ⊆ insert_edge e (sort_edges rest)
      let rec sorted_subset_insert (e: edge) (sorted: list edge)
        : Lemma (ensures subset_edges sorted (insert_edge e sorted))
                (decreases sorted)
        = match sorted with
          | [] -> ()
          | hd :: tl ->
            if e.w <= hd.w then begin
              subset_edges_reflexive (hd :: tl);
              subset_edges_cons (hd :: tl) e (hd :: tl)
            end else begin
              sorted_subset_insert e tl;
              subset_edges_cons tl hd (insert_edge e tl)
            end
      in
      sorted_subset_insert e (sort_edges rest);
      subset_edges_transitive rest (sort_edges rest) (insert_edge e (sort_edges rest))

let sort_edges_subset (edges: list edge)
  : Lemma (ensures subset_edges (sort_edges edges) edges /\
                   subset_edges edges (sort_edges edges))
  = sort_edges_subset_forward edges;
    sort_edges_subset_backward edges

let rec insert_maintains_sorted (e: edge) (sorted: list edge)
  : Lemma (requires is_sorted_by_weight sorted)
          (ensures is_sorted_by_weight (insert_edge e sorted))
  = match sorted with
    | [] -> ()
    | hd :: tl ->
      if e.w <= hd.w then ()
      else begin
        insert_maintains_sorted e tl;
        match tl with
        | [] -> ()
        | hd' :: tl' -> ()
      end

let rec sort_edges_sorted (edges: list edge)
  : Lemma (ensures is_sorted_by_weight (sort_edges edges))
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_sorted rest;
      insert_maintains_sorted e (sort_edges rest)

(*** Correctness Properties ***)

// Property 1: Kruskal maintains forest invariant
let lemma_kruskal_step_preserves_forest (e: edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_step e forest n) n)
  = // kruskal_step adds e only when conditions hold; otherwise returns forest
    if e.u < n && e.v < n &&
       not (same_component_dec forest e.u e.v) &&
       not (mem_edge e forest)
    then begin
      // same_component_dec = false => ~(same_component forest e.u e.v)
      // by contrapositive of same_component_dec_complete
      let cp () : Lemma (requires same_component forest e.u e.v)
                        (ensures same_component_dec forest e.u e.v = true)
        = same_component_dec_complete forest e.u e.v
      in
      FStar.Classical.move_requires cp ();
      assert (~(same_component forest e.u e.v));
      assert (~(reachable forest e.u e.v));
      // Use acyclic_when_unreachable from MST.Spec
      acyclic_when_unreachable n forest e
    end

let rec lemma_kruskal_process_preserves_forest 
    (sorted_edges: list edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_process sorted_edges forest n) n)
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      lemma_kruskal_step_preserves_forest e forest n;
      lemma_kruskal_process_preserves_forest rest (kruskal_step e forest n) n

// Property 2: All edges in result are from the graph
let lemma_kruskal_step_edges_from_graph 
    (e: edge) (forest: list edge) (graph_edges: list edge) (n: nat)
  : Lemma (requires subset_edges forest graph_edges /\ mem_edge e graph_edges)
          (ensures subset_edges (kruskal_step e forest n) graph_edges)
  = ()

let rec lemma_kruskal_process_edges_from_graph 
    (sorted_edges: list edge) (forest: list edge) (graph_edges: list edge) (n: nat)
  : Lemma (requires subset_edges forest graph_edges /\ 
                    subset_edges sorted_edges graph_edges)
          (ensures subset_edges (kruskal_process sorted_edges forest n) graph_edges)
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      lemma_kruskal_step_edges_from_graph e forest graph_edges n;
      lemma_kruskal_process_edges_from_graph rest (kruskal_step e forest n) graph_edges n

// Property 3: Safe Edge Property via Cut Property
// When Kruskal adds an edge (u,v), it's because u and v are in different components.
// This means the cut S = {vertices reachable from u} separates u from v.
// The cut respects current forest A (no edge in A crosses the cut by definition of components).
// Since edges are processed in sorted order, (u,v) is the lightest edge seen so far
// that crosses this particular cut.

let lemma_kruskal_step_safe_edge (g: graph) (e: edge) (forest: list edge) 
  : Lemma (requires 
            e.u < g.n /\ e.v < g.n /\
            mem_edge e g.edges /\
            is_forest forest g.n /\
            subset_edges forest g.edges /\
            ~(same_component forest e.u e.v) /\
            not (mem_edge e forest) /\
            // Edges before e in sorted order have higher or equal weight
            (forall (e': edge). 
              mem_edge e' g.edges /\ 
              not (mem_edge e' forest) /\ 
              ~(same_component forest e'.u e'.v) ==>
              e.w <= e'.w) /\
            // All graph edges have valid endpoints
            (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
            // Forest is subset of some MST
            (exists (mst: list edge). is_mst g mst /\ subset_edges forest mst))
          (ensures 
            // After adding e, still subset of some MST
            (exists (mst: list edge). is_mst g mst /\ subset_edges (e :: forest) mst))
  = // Define cut: S = component containing e.u
    // We use the decidable version for the cut definition
    let s : cut = fun v -> same_component_dec forest e.u v in
    
    // The edge e crosses this cut
    // same_component_dec forest e.u e.u = true (by definition, since u = u)
    // ~(same_component forest e.u e.v) => same_component_dec forest e.u e.v = false
    // (by contrapositive of same_component_dec_sound)
    let cp_sound () : Lemma (requires same_component_dec forest e.u e.v = true)
                            (ensures same_component forest e.u e.v)
      = same_component_dec_sound forest e.u e.v
    in
    FStar.Classical.move_requires cp_sound ();
    assert (same_component_dec forest e.u e.v = false);
    assert (same_component_dec forest e.u e.u = true);
    assert (crosses_cut e s);
    
    // The cut respects forest A
    // For each edge e' in forest: e' connects two vertices that are
    // reachable from each other via forest edges, hence in the same component.
    // So same_component_dec forest e.u (e'.u) = same_component_dec forest e.u (e'.v)
    // meaning e' doesn't cross the cut.
    let rec lemma_forest_respects_own_cut (f: list edge) (forest_full: list edge) (u: nat)
      : Lemma (requires subset_edges f forest_full)
              (ensures respects f (fun v -> same_component_dec forest_full u v))
              (decreases f)
      = match f with
        | [] -> ()
        | hd :: tl ->
          lemma_forest_respects_own_cut tl forest_full u;
          // hd is in forest_full. hd connects hd.u and hd.v.
          // So same_component forest_full hd.u hd.v (via the single edge hd)
          assert (mem_edge hd forest_full);
          edge_gives_reachability forest_full hd.u hd.v hd;
          // same_component_dec forest_full u hd.u and same_component_dec forest_full u hd.v
          // must have the same truth value (since hd.u and hd.v are connected):
          // Case 1: both true (u reaches hd.u and hd.v)
          // Case 2: both false (u reaches neither hd.u nor hd.v)
          // In either case, crosses_cut hd s = false
          if same_component_dec forest_full u hd.u then begin
            // u reaches hd.u. hd.u reaches hd.v. So u reaches hd.v.
            same_component_dec_sound forest_full u hd.u;
            same_component_transitive forest_full u hd.u hd.v;
            same_component_dec_complete forest_full u hd.v
          end else begin
            // u doesn't reach hd.u.
            // If u reached hd.v, then u reaches hd.u (via hd.v -> hd.u), contradiction
            if same_component_dec forest_full u hd.v then begin
              same_component_dec_sound forest_full u hd.v;
              same_component_symmetric forest_full hd.u hd.v;
              same_component_transitive forest_full u hd.v hd.u;
              same_component_dec_complete forest_full u hd.u
              // Now same_component_dec forest_full u hd.u = true, contradicting the else branch
            end
          end
    in
    subset_edges_reflexive forest;
    lemma_forest_respects_own_cut forest forest e.u;
    
    // Edge e is light: since cut respects forest, no forest edge crosses the cut.
    // Combined with precondition that e.w <= e'.w for all non-forest edges crossing
    // the cut, e is a light edge.
    // is_light_edge requires: forall e'. mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    // For e' in forest: ~(crosses_cut e' s) (from respects), so vacuously true
    // For e' not in forest: e.w <= e'.w from precondition
    //   But precondition uses ~(same_component forest e'.u e'.v), not crosses_cut e' s
    //   Need: crosses_cut e' s => ~(same_component forest e'.u e'.v) when e' ∉ forest
    //   Actually not exactly... the precondition says:
    //   e.w <= e'.w when e' ∈ g.edges, e' ∉ forest, ~(same_component forest e'.u e'.v)
    //   For light_edge we need: e.w <= e'.w when e' ∈ g.edges, crosses_cut e' s
    //   crosses_cut e' s means same_component_dec forest e.u (e'.u) ≠ same_component_dec forest e.u (e'.v)
    //   Case: e' in forest => doesn't cross cut, vacuous ✓
    //   Case: e' not in forest, crosses cut:
    //     same_component_dec forest e.u (e'.u) ≠ same_component_dec forest e.u (e'.v)
    //     so ~(same_component forest e'.u e'.v):
    //     If same_component forest e'.u e'.v, then 
    //       same_component_dec_complete => same_component_dec forest e.u (e'.u) = true iff same_component_dec forest e.u (e'.v) = true
    //       contradicting the crossing. So ~(same_component forest e'.u e'.v).
    //     Then precondition gives e.w <= e'.w. ✓
    introduce forall (e': edge). mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    with introduce _ ==> _ with _. begin
      if mem_edge e' forest then begin
        // e' in forest => doesn't cross cut (from respects)
        let rec respects_implies (f: list edge) (e': edge) (s: cut)
          : Lemma (requires respects f s /\ mem_edge e' f)
                  (ensures not (crosses_cut e' s))
                  (decreases f)
          = match f with
            | [] -> ()
            | hd :: tl ->
              if edge_eq e' hd then begin
                edge_eq_endpoints e' hd;
                assert (not (crosses_cut hd s))
              end else
                respects_implies tl e' s
        in
        respects_implies forest e' s
        // e' doesn't cross cut, contradicting precondition crosses_cut e' s = true
      end else begin
        // e' not in forest, crosses cut
        // Need: ~(same_component forest e'.u e'.v)
        // crosses_cut e' s => same_component_dec forest e.u e'.u ≠ same_component_dec forest e.u e'.v
        // If same_component forest e'.u e'.v were true, by same_component_dec_complete
        // we'd have same_component_dec forest e.u e'.u = same_component_dec forest e.u e'.v
        // (both true or both false, since transitivity), contradicting crossing.
        let cp ()
          : Lemma (requires same_component forest e'.u e'.v) (ensures False)
          = if same_component_dec forest e.u e'.u then begin
              same_component_dec_sound forest e.u e'.u;
              same_component_transitive forest e.u e'.u e'.v;
              same_component_dec_complete forest e.u e'.v
            end else begin
              if same_component_dec forest e.u e'.v then begin
                same_component_dec_sound forest e.u e'.v;
                same_component_symmetric forest e'.u e'.v;
                same_component_transitive forest e.u e'.v e'.u;
                same_component_dec_complete forest e.u e'.u
              end
            end
        in
        FStar.Classical.move_requires cp ()
      end
    end;
    assert (is_light_edge e s g);
    // Apply cut property: A ∪ {e} ⊆ some MST
    cut_property g forest e s

(*** Main Correctness Theorem ***)

// Helper: same_component is monotone — adding edges preserves reachability
let same_component_mono (edges: list edge) (e: edge) (u v: nat)
  : Lemma (requires same_component edges u v)
          (ensures same_component (e :: edges) u v)
  = eliminate exists (path: list edge). subset_edges path edges /\ is_path_from_to path u v
    returns same_component (e :: edges) u v
    with _. begin
      subset_edges_cons path e edges
    end

// Kruskal process maintains: every graph edge with valid endpoints either is in forest
// or has its endpoints in the same component of the forest
let rec lemma_kruskal_process_maximal_forest
    (sorted_edges all_sorted: list edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n /\
                    (forall (e: edge). mem_edge e all_sorted /\ ~(mem_edge e sorted_edges) /\
                      e.u < n /\ e.v < n ==>
                      mem_edge e forest \/ same_component forest e.u e.v) /\
                    (exists (prefix: list edge). all_sorted == prefix @ sorted_edges))
          (ensures (let result = kruskal_process sorted_edges forest n in
                    (forall (e: edge). mem_edge e all_sorted /\ e.u < n /\ e.v < n ==>
                      mem_edge e result \/ same_component result e.u e.v)))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      let forest' = kruskal_step e forest n in
      lemma_kruskal_step_preserves_forest e forest n;
      
      if e.u < n && e.v < n && 
         not (same_component_dec forest e.u e.v) &&
         not (mem_edge e forest) then begin
        assert (forest' == e :: forest);
        introduce forall (e': edge). mem_edge e' all_sorted /\ ~(mem_edge e' rest) /\
                            e'.u < n /\ e'.v < n ==>
                    mem_edge e' forest' \/ same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then ()
          else if mem_edge e' forest then ()
          else begin
            assert (~(mem_edge e' sorted_edges));
            assert (same_component forest e'.u e'.v);
            same_component_mono forest e e'.u e'.v
          end
        end;
        
        eliminate exists (prefix: list edge). all_sorted == prefix @ (e :: rest)
          returns (exists (prefix': list edge). all_sorted == prefix' @ rest)
          with _. begin
            List.Tot.Properties.append_assoc prefix [e] rest;
            assert (all_sorted == (prefix @ [e]) @ rest)
          end;
        
        lemma_kruskal_process_maximal_forest rest all_sorted forest' n
      end else begin
        assert (forest' == forest);
        introduce forall (e': edge). mem_edge e' all_sorted /\ ~(mem_edge e' rest) /\
                            e'.u < n /\ e'.v < n ==>
                    mem_edge e' forest' \/ same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then begin
            edge_eq_endpoints e' e;
            if mem_edge e forest then begin
              edge_eq_symmetric e' e;
              mem_edge_eq e e' forest
            end
            else if not (e.u < n && e.v < n) then ()
            else if same_component_dec forest e.u e.v then begin
              same_component_dec_sound forest e.u e.v;
              assert ((e'.u = e.u /\ e'.v = e.v) \/ (e'.u = e.v /\ e'.v = e.u));
              if e'.u = e.u && e'.v = e.v then ()
              else same_component_symmetric forest e.u e.v
            end else ()
          end else begin
            assert (~(mem_edge e' sorted_edges));
            ()
          end
        end;
        
        eliminate exists (prefix: list edge). all_sorted == prefix @ (e :: rest)
          returns (exists (prefix': list edge). all_sorted == prefix' @ rest)
          with _. begin
            List.Tot.Properties.append_assoc prefix [e] rest;
            assert (all_sorted == (prefix @ [e]) @ rest)
          end;
        
        lemma_kruskal_process_maximal_forest rest all_sorted forest' n
      end

// MST invariant: kruskal_process maintains "forest is subset of some MST"
// This needs the "minimum weight among unused cross-component edges" property
// which follows from processing edges in sorted order.
let rec lemma_kruskal_process_mst_invariant
    (g: graph) (sorted_edges: list edge) (forest: list edge)
  : Lemma (requires 
            is_forest forest g.n /\
            subset_edges forest g.edges /\
            (exists (mst: list edge). is_mst g mst /\ subset_edges forest mst) /\
            subset_edges sorted_edges g.edges /\
            is_sorted_by_weight sorted_edges /\
            // All graph edges have valid endpoints
            (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
            // Every graph edge not in sorted_edges with valid endpoints
            // is either in the forest or connects same-component vertices
            (forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' sorted_edges) /\
              ~(mem_edge e' forest) ==>
              same_component forest e'.u e'.v))
          (ensures (let result = kruskal_process sorted_edges forest g.n in
            (exists (mst: list edge). is_mst g mst /\ subset_edges result mst)))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      let forest' = kruskal_step e forest g.n in
      lemma_kruskal_step_preserves_forest e forest g.n;
      
      if e.u < g.n && e.v < g.n && 
         not (same_component_dec forest e.u e.v) &&
         not (mem_edge e forest) then begin
        // e was added. Need to show: forest' = e :: forest is subset of some MST
        // Use lemma_kruskal_step_safe_edge
        
        // Establish: e has minimum weight among unused cross-component edges
        // For any e' in g.edges that's not in forest and crosses different components:
        //   - If e' is in sorted_edges (i.e., in rest): e.w <= e'.w (from sorted order)
        //   - If e' is not in sorted_edges: from precondition, same_component forest e'.u e'.v
        //     So ~(same_component forest e'.u e'.v) is false, vacuously true.
        introduce forall (e': edge). 
          mem_edge e' g.edges /\ not (mem_edge e' forest) /\ ~(same_component forest e'.u e'.v) ==>
          e.w <= e'.w
        with introduce _ ==> _ with _. begin
          // e' is in g.edges, not in forest, different components
          if mem_edge e' (e :: rest) then begin
            // e' is in sorted_edges = e :: rest
            if edge_eq e' e then begin
              edge_eq_endpoints e' e
            end else begin
              // e' is in rest. Since sorted_edges is sorted and e is the head:
              // e.w <= rest head.w <= ... <= e'.w
              assert (mem_edge e' rest);
              // Need: first element of sorted list ≤ any element
              let rec sorted_head_le_all (hd: edge) (tl: list edge) (e': edge)
                : Lemma (requires is_sorted_by_weight (hd :: tl) /\ mem_edge e' tl)
                        (ensures hd.w <= e'.w)
                        (decreases tl)
                = match tl with
                  | [] -> ()
                  | hd2 :: tl2 ->
                    if edge_eq e' hd2 then edge_eq_endpoints e' hd2
                    else begin
                      sorted_head_le_all hd2 tl2 e';
                      ()
                    end
              in
              sorted_head_le_all e rest e'
            end
          end else begin
            // e' is not in sorted_edges, not in forest, in g.edges.
            // From precondition: same_component forest e'.u e'.v.
            // But ~(same_component forest e'.u e'.v) from outer. Contradiction.
            assert (same_component forest e'.u e'.v)
          end
        end;
        
        // Apply safe edge lemma
        // Establish ~(same_component forest e.u e.v) from same_component_dec = false
        let dec_complete_contra () 
          : Lemma (requires same_component forest e.u e.v)
                  (ensures same_component_dec forest e.u e.v = true)
          = same_component_dec_complete forest e.u e.v
        in
        FStar.Classical.move_requires dec_complete_contra ();
        assert (~(same_component forest e.u e.v));
        assert (e.u < g.n /\ e.v < g.n);
        assert (mem_edge e g.edges);
        assert (is_forest forest g.n);
        assert (subset_edges forest g.edges);
        lemma_kruskal_step_safe_edge g e forest;
        // Now: exists mst. is_mst g mst /\ subset_edges (e :: forest) mst
        
        // For the IH: we need the "already processed" edges to satisfy the invariant
        // For e' not in rest, not in forest', with valid endpoints:
        //   same_component forest' e'.u e'.v
        // Case 1: e' not in (e :: rest) => e' not in sorted_edges =>
        //   same_component forest e'.u e'.v (from precondition) =>
        //   same_component forest' e'.u e'.v (monotone, forest ⊆ forest')
        // Case 2: e' = e (edge_eq) => e is in forest' = e :: forest. So mem_edge e' forest' (via edge_eq).
        //   But we need ~(mem_edge e' forest') to trigger the precondition, so vacuously true.
        
        // Establish IH precondition
        assert (forest' == e :: forest);
        introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' rest) /\
          ~(mem_edge e' forest') ==>
          same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          // e' is not in rest and not in forest'
          // If edge_eq e' e: then e' is in forest' (since e is head of forest'). Contradiction.
          if edge_eq e' e then begin
            edge_eq_symmetric e' e;
            mem_edge_eq e e' (e :: forest);
            assert (mem_edge e' forest')
            // contradicts ~(mem_edge e' forest')
          end else begin
            // e' is not e, and e' is not in rest
            // So e' is not in (e :: rest) = sorted_edges
            assert (~(mem_edge e' sorted_edges));
            // From precondition (if not in forest): same_component forest e'.u e'.v
            if mem_edge e' forest then begin
              // e' in forest but not in forest' = e :: forest? Impossible.
              assert (mem_edge e' (e :: forest))
            end else begin
              assert (same_component forest e'.u e'.v);
              same_component_mono forest e e'.u e'.v
            end
          end
        end;
        
        // subset_edges
        lemma_kruskal_step_edges_from_graph e forest g.edges g.n;
        
        // sorted rest
        assert (is_sorted_by_weight rest);
        
        lemma_kruskal_process_mst_invariant g rest forest'
      end else begin
        // e was NOT added. forest' = forest. MST invariant preserved trivially.
        
        // For the IH: processed edges invariant
        introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' rest) /\
          ~(mem_edge e' forest') ==>
          same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then begin
            edge_eq_endpoints e' e;
            if mem_edge e forest then begin
              edge_eq_symmetric e' e;
              mem_edge_eq e e' forest
            end else if not (e.u < g.n && e.v < g.n) then begin
              // e'.u < g.n /\ e'.v < g.n (from valid endpoints precondition)
              // but e endpoints = e' endpoints (from edge_eq). Contradiction.
              assert (mem_edge e' g.edges);
              assert (e'.u < g.n /\ e'.v < g.n)
            end else if same_component_dec forest e.u e.v then begin
              same_component_dec_sound forest e.u e.v;
              if e'.u = e.u && e'.v = e.v then ()
              else same_component_symmetric forest e.u e.v
            end else ()
          end else begin
            assert (~(mem_edge e' sorted_edges));
            ()
          end
        end;
        
        assert (is_sorted_by_weight rest);
        
        lemma_kruskal_process_mst_invariant g rest forest'
      end

// ==========================================
// Simple path extraction for main theorems
// ==========================================

// Helper: path traversal connectivity
let rec path_edges_connected_implies_endpoints_connected
    (path: list edge) (result: list edge) (u v: nat)
  : Lemma (requires is_path_from_to path u v /\
                    (forall (e: edge). mem_edge e path ==>
                      mem_edge e result \/ same_component result e.u e.v))
          (ensures same_component result u v)
          (decreases path)
  = match path with
    | [] -> same_component_reflexive result u
    | e :: rest ->
      if e.u = u then begin
        path_edges_connected_implies_endpoints_connected rest result e.v v;
        if mem_edge e result then begin
          edge_gives_reachability result u e.v e;
          same_component_transitive result u e.v v
        end else begin
          assert (e.u = u);
          same_component_transitive result u e.v v
        end
      end else begin
        assert (e.v = u);
        path_edges_connected_implies_endpoints_connected rest result e.u v;
        if mem_edge e result then begin
          edge_gives_reachability result u e.u e;
          same_component_transitive result u e.u v
        end else begin
          same_component_symmetric result e.u e.v;
          same_component_transitive result u e.u v
        end
      end

let rec subset_edges_valid_endpoints (path: list edge) (g_edges: list edge) (n: nat)
  : Lemma (requires subset_edges path g_edges /\
                    (forall (e: edge). mem_edge e g_edges ==> e.u < n /\ e.v < n))
          (ensures (forall (e: edge). mem_edge e path ==> e.u < n /\ e.v < n))
          (decreases path)
  = match path with
    | [] -> ()
    | e :: rest -> subset_edges_valid_endpoints rest g_edges n

let path_next (e: edge) (current: nat) : nat =
  if e.u = current then e.v else e.u

let rec vertex_visited (path: list edge) (current target: nat) : Tot bool (decreases path)
  = current = target ||
    (match path with
     | [] -> false
     | e :: rest -> vertex_visited rest (path_next e current) target)

let rec path_skip_to (path: list edge) (current target: nat) 
  : Tot (list edge) (decreases path)
  = if current = target then path
    else match path with
      | [] -> []
      | e :: rest -> path_skip_to rest (path_next e current) target

let rec path_skip_to_valid (path: list edge) (current target finish: nat)
  : Lemma (requires is_path_from_to path current finish /\
                    vertex_visited path current target)
          (ensures is_path_from_to (path_skip_to path current target) target finish)
          (decreases path)
  = if current = target then ()
    else match path with
      | e :: rest -> path_skip_to_valid rest (path_next e current) target finish

let rec path_skip_to_subset (path: list edge) (current target: nat) (es: list edge)
  : Lemma (requires subset_edges path es)
          (ensures subset_edges (path_skip_to path current target) es)
          (decreases path)
  = if current = target then ()
    else match path with
      | [] -> ()
      | e :: rest -> path_skip_to_subset rest (path_next e current) target es

let rec path_skip_to_shorter (path: list edge) (current target: nat)
  : Lemma (requires current <> target /\ vertex_visited path current target)
          (ensures length (path_skip_to path current target) < length path)
          (decreases path)
  = match path with
    | e :: rest ->
      let next = path_next e current in
      if next = target then ()
      else path_skip_to_shorter rest next target

// Remove revisits to start vertex u
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec remove_start_revisit (path: list edge) (es: list edge) (u v: nat)
  : Pure (list edge)
         (requires is_path_from_to path u v /\ subset_edges path es /\ u <> v)
         (ensures fun path' -> is_path_from_to path' u v /\ subset_edges path' es /\ 
                               Cons? path' /\ length path' <= length path /\
                               ~(vertex_visited (List.Tot.tl path') 
                                 (path_next (List.Tot.hd path') u) u))
         (decreases length path)
  = let hd :: tl = path in
    let next = path_next hd u in
    if next = u then
      remove_start_revisit tl es u v
    else if vertex_visited tl next u then begin
      path_skip_to_valid tl next u v;
      path_skip_to_subset tl next u es;
      path_skip_to_shorter tl next u;
      remove_start_revisit (path_skip_to tl next u) es u v
    end else
      path
#pop-options

// After remove_start_revisit, all edges in tl have endpoints ≠ u
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec no_visit_means_no_u_endpoints (path: list edge) (current u finish: nat)
  : Lemma (requires is_path_from_to path current finish /\
                    current <> u /\ ~(vertex_visited path current u))
          (ensures forall (e: edge). mem_edge e path ==> e.u <> u /\ e.v <> u)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      let next = path_next hd current in
      // vertex_visited (hd::tl) current u = (current = u) || vertex_visited tl next u
      // current <> u, so ~(vertex_visited tl next u)
      // Also: next <> u (since vertex_visited tl next u starts with next=u check)
      assert (next <> u);
      assert (hd.u <> u /\ hd.v <> u);
      if Cons? tl then
        no_visit_means_no_u_endpoints tl next u finish
      else ()
#pop-options

// Edge with u-endpoint not mem_edge of edges without u-endpoints
let rec edge_with_u_not_in_no_u_list (e: edge) (path: list edge) (u: nat)
  : Lemma (requires (e.u = u \/ e.v = u) /\
                    (forall (e': edge). mem_edge e' path ==> e'.u <> u /\ e'.v <> u))
          (ensures ~(mem_edge e path))
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      // edge_eq e hd checks {e.u,e.v} = {hd.u,hd.v} (same weight)
      // e has u endpoint, hd has no u endpoint. So can't match.
      edge_with_u_not_in_no_u_list e tl u

// mem_edge subset: if e in A and subset_edges A B then e in B
let rec mem_edge_of_subset (e: edge) (a b: list edge)
  : Lemma (requires mem_edge e a /\ subset_edges a b)
          (ensures mem_edge e b)
          (decreases a)
  = match a with
    | hd :: tl ->
      if edge_eq e hd then begin
        // mem_edge hd b (from subset_edges)
        // edge_eq e hd => edge_eq hd e (symmetric)
        // mem_edge hd b /\ edge_eq hd e => mem_edge e b
        edge_eq_symmetric e hd;
        mem_edge_eq hd e b
      end else mem_edge_of_subset e tl b

// Simple path extraction: guaranteed to produce edges from the original path
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec extract_simple_path (path: list edge) (u v: nat)
  : Lemma (requires is_path_from_to path u v /\ u <> v)
          (ensures exists (path': list edge). is_path_from_to path' u v /\ 
                    subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
          (decreases length path)
  = // Phase 1: remove revisits to u
    subset_edges_reflexive path;
    let path_nr = remove_start_revisit path path u v in
    assert (is_path_from_to path_nr u v);
    assert (subset_edges path_nr path);
    let hd :: tl = path_nr in
    let next = path_next hd u in
    assert (~(vertex_visited tl next u));
    // hd has u as endpoint
    assert ((hd.u = u /\ next = hd.v) \/ (hd.v = u /\ next = hd.u));
    if next = v then begin
      // Single edge path
      assert (is_path_from_to [hd] u v);
      assert (all_edges_distinct [hd]);
      assert (subset_edges [hd] path_nr);
      subset_edges_transitive [hd] path_nr path
    end else begin
      // tl: path from next to v, next <> u, next <> v
      // All edges in tl have endpoints <> u
      no_visit_means_no_u_endpoints tl next u v;
      // Recursively extract simple path from tl
      assert (length tl < length path_nr);
      assert (length path_nr <= length path);
      extract_simple_path tl next v;
      // IH gives: exists path_tl. simple path from next to v, subset_edges path_tl tl
      // Since subset_edges path_tl tl and all edges in tl have endpoints <> u:
      //   all edges in path_tl have endpoints <> u
      // Since hd has u as endpoint: ~(mem_edge hd path_tl)
      // So hd :: path_tl is all_edges_distinct
      // And is_path_from_to (hd :: path_tl) u v
      
      // We need to work with the existential witness. Use classical logic.
      FStar.Classical.exists_elim 
        (exists (path': list edge). is_path_from_to path' u v /\
          subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
        #_
        #(fun (path_tl: list edge) -> 
          is_path_from_to path_tl next v /\
          subset_edges path_tl tl /\ all_edges_distinct path_tl /\ Cons? path_tl) ()
        (fun (path_tl: list edge{
          is_path_from_to path_tl next v /\
          subset_edges path_tl tl /\ all_edges_distinct path_tl /\ Cons? path_tl}) ->
          // All edges in path_tl are from tl, hence have endpoints <> u
          let rec path_tl_no_u (p: list edge)
            : Lemma (requires subset_edges p tl /\
                              (forall (e: edge). mem_edge e tl ==> e.u <> u /\ e.v <> u))
                    (ensures forall (e: edge). mem_edge e p ==> e.u <> u /\ e.v <> u)
                    (decreases p)
            = match p with
              | [] -> ()
              | e :: rest -> path_tl_no_u rest
          in
          path_tl_no_u path_tl;
          // hd has u as endpoint, path_tl has no u-endpoint edges
          edge_with_u_not_in_no_u_list hd path_tl u;
          assert (~(mem_edge hd path_tl));
          // hd :: path_tl is simple
          assert (all_edges_distinct (hd :: path_tl));
          // hd :: path_tl is a valid path from u to v
          assert (is_path_from_to (hd :: path_tl) u v);
          // subset: path_tl ⊆ tl, tl ⊆ path_nr = hd :: tl ⊆ path
          subset_edges_reflexive tl;
          subset_edges_cons tl hd tl;
          subset_edges_transitive path_tl tl (hd :: tl);
          subset_edges_transitive path_tl path_nr path;
          assert (subset_edges (hd :: path_tl) path)
        )
    end
#pop-options

// Now we can prove: adding edge between reachable vertices creates cycle
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let reachable_means_not_acyclic (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ reachable t e.u e.v /\ 
                    e.u < n /\ e.v < n /\ e.u <> e.v /\ ~(mem_edge e t))
          (ensures ~(acyclic n (e :: t)))
  = // Get a simple path from e.u to e.v in t
    FStar.Classical.exists_elim
      (~(acyclic n (e :: t)))
      #_
      #(fun (path: list edge) -> subset_edges path t /\ is_path_from_to path e.u e.v) ()
      (fun (path: list edge{subset_edges path t /\ is_path_from_to path e.u e.v}) ->
        extract_simple_path path e.u e.v;
        FStar.Classical.exists_elim
          (~(acyclic n (e :: t)))
          #_
          #(fun (sp: list edge) -> is_path_from_to sp e.u e.v /\
              subset_edges sp path /\ all_edges_distinct sp /\ Cons? sp) ()
          (fun (sp: list edge{is_path_from_to sp e.u e.v /\
              subset_edges sp path /\ all_edges_distinct sp /\ Cons? sp}) ->
            // sp: simple path from e.u to e.v, edges from path ⊆ t
            subset_edges_transitive sp path t;
            // Form cycle: sp @ [e] from e.u to e.u
            is_path_append_edge sp e.u e.v e.u e;
            // sp @ [e] subset of e :: t
            subset_edges_cons sp e t;
            subset_edges_append_single sp e (e :: t);
            // all_edges_distinct (sp @ [e]): 
            // - all_edges_distinct sp ✓
            // - e ∉ sp (since sp ⊆ t and e ∉ t)
            let rec e_not_in_sp (p: list edge) 
              : Lemma (requires subset_edges p t /\ ~(mem_edge e t))
                      (ensures ~(mem_edge e p))
                      (decreases p)
              = match p with
                | [] -> ()
                | hd :: tl -> 
                  if edge_eq e hd then begin
                    // edge_eq e hd and mem_edge hd t (from subset_edges)
                    // => mem_edge e t (via edge_eq_symmetric + mem_edge_eq)
                    edge_eq_symmetric e hd;
                    mem_edge_eq hd e t
                    // But ~(mem_edge e t). Contradiction.
                  end else e_not_in_sp tl
            in
            e_not_in_sp sp;
            // all_edges_distinct on append
            let rec distinct_append_single (p: list edge) (e0: edge)
              : Lemma (requires all_edges_distinct p /\ ~(mem_edge e0 p))
                      (ensures all_edges_distinct (p @ [e0]))
                      (decreases p)
              = match p with
                | [] -> ()
                | hd :: tl ->
                  distinct_append_single tl e0;
                  // Need: ~(mem_edge hd (tl @ [e0]))
                  mem_edge_append hd tl [e0];
                  // mem_edge hd (tl @ [e0]) <==> mem_edge hd tl || mem_edge hd [e0]
                  // ~(mem_edge hd tl) from all_edges_distinct (hd :: tl)
                  // mem_edge hd [e0] = edge_eq hd e0
                  // If edge_eq hd e0: mem_edge e0 p (since hd ∈ p). Contradicts ~(mem_edge e0 p).
                  if edge_eq hd e0 then begin
                    mem_edge_hd hd tl;
                    mem_edge_eq hd e0 (hd :: tl)
                  end else ()
            in
            distinct_append_single sp e;
            // Now we have a simple cycle in e :: t
            let cycle = sp @ [e] in
            assert (is_path_from_to cycle e.u e.u);
            assert (Cons? cycle);
            assert (subset_edges cycle (e :: t));
            assert (all_edges_distinct cycle);
            // This contradicts acyclic n (e :: t)
            assert (e.u < n);
            // acyclic n (e :: t) says: for all v < n, cycle ⊆ (e::t), Cons? cycle, 
            //   all_edges_distinct cycle ==> ~(is_path_from_to cycle v v)
            // Instantiate with v = e.u: gives ~(is_path_from_to cycle e.u e.u)
            // But we have is_path_from_to cycle e.u e.u. Contradiction.
            ()
          )
      )
#pop-options

// Connected subset of spanning tree equals the spanning tree
// If result ⊆ mst and result connects all vertices, then all mst edges are in result
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let connected_subset_of_tree_is_tree (g: graph) (result mst: list edge)
  : Lemma (requires is_spanning_tree g mst /\
                    subset_edges result mst /\
                    all_connected g.n result /\
                    acyclic g.n result /\
                    (forall (e: edge). mem_edge e mst ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e mst ==> e.u <> e.v))
          (ensures forall (e: edge). mem_edge e mst ==> mem_edge e result)
  = introduce forall (e: edge). mem_edge e mst ==> mem_edge e result
    with introduce _ ==> _ with _. begin
      // Suppose e ∈ mst. We want e ∈ result.
      // By contradiction: suppose e ∉ result.
      if not (mem_edge e result) then begin
        assert (e.u < g.n /\ e.v < g.n);
        same_component_symmetric result 0 e.u;
        same_component_transitive result e.u 0 e.v;
        assert (reachable result e.u e.v);
        // result is acyclic, e has valid endpoints, e ∉ result, e.u <> e.v
        // => ~(acyclic g.n (e :: result))
        reachable_means_not_acyclic g.n result e;
        // But result ⊆ mst and e ∈ mst, so e :: result ⊆ mst (up to ordering)
        // Actually: subset_edges (e :: result) mst since e ∈ mst and result ⊆ mst
        assert (subset_edges (e :: result) mst);
        // And mst is acyclic (from is_spanning_tree)
        // acyclic n mst and (e :: result) ⊆ mst
        // Any cycle in (e :: result) is also a cycle in mst (by subset)
        // So acyclic n mst => acyclic n (e :: result)
        // This is the key: acyclicity is downward-closed for subsets
        let rec acyclic_subset (a b: list edge) (n: nat)
          : Lemma (requires acyclic n b /\ subset_edges a b)
                  (ensures acyclic n a)
          = introduce forall (v: nat) (cycle: list edge).
              v < n /\ subset_edges cycle a /\ Cons? cycle /\ all_edges_distinct cycle ==>
              ~(is_path_from_to cycle v v)
            with introduce _ ==> _ with _. begin
              subset_edges_transitive cycle a b
            end
        in
        acyclic_subset (e :: result) mst g.n;
        // Now: acyclic g.n (e :: result) AND ~(acyclic g.n (e :: result))
        // Contradiction!
        assert (acyclic g.n (e :: result));
        assert (~(acyclic g.n (e :: result)));
        ()
      end else ()
    end
#pop-options

// No duplicate edges in a list (using edge_eq)
let rec noRepeats_edge (l: list edge) : bool =
  match l with
  | [] -> true
  | hd :: tl -> not (mem_edge hd tl) && noRepeats_edge tl

// Kruskal result has no duplicate edges
let rec lemma_kruskal_process_no_repeats (sorted_edges: list edge) (forest: list edge) (n: nat)
  : Lemma (requires noRepeats_edge forest)
          (ensures noRepeats_edge (kruskal_process sorted_edges forest n))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      if e.u < n && e.v < n && not (same_component_dec forest e.u e.v) && not (mem_edge e forest) then
        lemma_kruskal_process_no_repeats rest (e :: forest) n
      else
        lemma_kruskal_process_no_repeats rest forest n

// Remove first occurrence of edge from list
let rec remove_edge_first (e: edge) (l: list edge) : list edge =
  match l with
  | [] -> []
  | hd :: tl -> if edge_eq e hd then tl else hd :: remove_edge_first e tl

// Length decreases by 1 when removing present edge
let rec remove_edge_first_length (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures length (remove_edge_first e l) = length l - 1)
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then ()
      else remove_edge_first_length e tl

// If e' ∈ l and ~(edge_eq e' e), then e' ∈ remove_edge_first e l
let rec mem_remove_edge_first_other (e' e: edge) (l: list edge)
  : Lemma (requires mem_edge e' l /\ ~(edge_eq e' e))
          (ensures mem_edge e' (remove_edge_first e l))
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then begin
        if edge_eq e' hd then begin
          edge_eq_symmetric e hd;
          assert (edge_eq e' e)
        end else ()
      end else begin
        if edge_eq e' hd then ()
        else mem_remove_edge_first_other e' e tl
      end

// noRepeats_edge a ∧ subset_edges a b ⟹ length a ≤ length b
let rec subset_noRepeats_length_le (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b)
          (ensures length a <= length b)
          (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      let rec prove_subset_tl (p: list edge)
        : Lemma (requires (forall (e:edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            mem_edge_of_subset e (hd :: tl) b;
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            mem_remove_edge_first_other e hd b;
            prove_subset_tl rest
      in
      prove_subset_tl tl;
      subset_noRepeats_length_le tl b'

// Helper: check if edge e is in a list using mem_edge
let mem_edge_in_list (e: edge) (es: list edge) : bool = mem_edge e es

// If both endpoints of e are reachable from root in tl, adding e doesn't create new reachability
#push-options "--z3rlimit 30"
let redundant_edge_reachability (tl: list edge) (e: edge) (root v: nat)
  : Lemma (requires same_component tl root e.u /\ same_component tl root e.v /\
                    same_component (e :: tl) root v)
          (ensures same_component tl root v)
  = if same_component_dec tl root v then
      same_component_dec_sound tl root v
    else begin
      eliminate exists (path: list edge).
        subset_edges path (e :: tl) /\ is_path_from_to path root v
      returns same_component tl root v
      with _. begin
        if root = v then same_component_reflexive tl root
        else begin
          extract_simple_path path root v;
          FStar.Classical.exists_elim 
            (same_component tl root v)
            #_
            #(fun (path': list edge) -> is_path_from_to path' root v /\
                subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
            ()
            (fun path' ->
              subset_edges_transitive path' path (e :: tl);
              if not (mem_edge_in_list e path') then begin
                path_not_using_e_in_t path' e tl
              end else begin
                split_at_first_e path' e tl root v;
                // Postcondition: (reachable tl root e.u /\ reachable tl e.v v) \/
                //                (reachable tl root e.v /\ reachable tl e.u v)
                // From precondition: reachable tl root e.u /\ reachable tl root e.v
                // In either case, we can reach v from root in tl
                assert (reachable tl root e.u);
                assert (reachable tl root e.v);
                // If e.v reaches v, use root->e.v->v
                // If e.u reaches v, use root->e.u->v  
                FStar.Classical.move_requires (reachable_transitive tl root e.v) v;
                FStar.Classical.move_requires (reachable_transitive tl root e.u) v;
                // Now we have: reachable tl e.v v ==> reachable tl root v
                //              reachable tl e.u v ==> reachable tl root v
                // One of these must hold from split_at_first_e
                assert ((reachable tl e.v v) \/ (reachable tl e.u v))
              end)
        end
      end
    end
#pop-options

// If neither endpoint of e is reachable from root in tl, adding e doesn't help root
let neither_endpoint_reachability (tl: list edge) (e: edge) (root v: nat)
  : Lemma (requires ~(same_component tl root e.u) /\ ~(same_component tl root e.v) /\
                    same_component (e :: tl) root v)
          (ensures same_component tl root v)
  = eliminate exists (path: list edge).
      subset_edges path (e :: tl) /\ is_path_from_to path root v
    returns same_component tl root v
    with _. begin
      if root = v then same_component_reflexive tl root
      else begin
        extract_simple_path path root v;
        FStar.Classical.exists_elim 
          (same_component tl root v)
          #_
          #(fun (path': list edge) -> is_path_from_to path' root v /\
              subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
          ()
          (fun path' ->
            subset_edges_transitive path' path (e :: tl);
            if not (mem_edge_in_list e path') then
              path_not_using_e_in_t path' e tl
            else begin
              split_at_first_e path' e tl root v;
              // Either root reaches e.u in tl or root reaches e.v in tl
              // But we assumed neither! Contradiction.
              assert (reachable tl root e.u \/ reachable tl root e.v);
              ()
            end)
      end
    end

// Bridge edge decomposition: if e.u reachable from root in tl but e.v not,
// then v reachable from root in (e::tl) iff v reachable from root in tl OR v reachable from e.v in tl
let bridge_edge_reachability (tl: list edge) (e: edge) (root v: nat)
  : Lemma (requires same_component tl root e.u /\ ~(same_component tl root e.v) /\
                    same_component (e :: tl) root v)
          (ensures same_component tl root v \/ same_component tl e.v v)
  = if same_component_dec tl root v then
      same_component_dec_sound tl root v
    else begin
      eliminate exists (path: list edge).
        subset_edges path (e :: tl) /\ is_path_from_to path root v
      returns (same_component tl root v \/ same_component tl e.v v)
      with _. begin
        if root = v then begin same_component_reflexive tl root; () end
        else begin
          extract_simple_path path root v;
          FStar.Classical.exists_elim 
            (same_component tl root v \/ same_component tl e.v v)
            #_
            #(fun (path': list edge) -> is_path_from_to path' root v /\
                subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
            ()
            (fun path' ->
              subset_edges_transitive path' path (e :: tl);
              if not (mem_edge_in_list e path') then begin
                path_not_using_e_in_t path' e tl;
                ()
              end else begin
                split_at_first_e path' e tl root v;
                // Case 1: reachable tl root e.u /\ reachable tl e.v v → done
                // Case 2: reachable tl root e.v /\ reachable tl e.u v
                //   root reaches e.v in tl → contradicts hypothesis ~(same_component tl root e.v)
                //   So case 2 leads to contradiction → done trivially
                if same_component_dec tl root v then begin
                  same_component_dec_sound tl root v; ()
                end else begin
                  // We have (reachable tl root e.u ∧ reachable tl e.v v) ∨ 
                  //         (reachable tl root e.v ∧ reachable tl e.u v)
                  // Case 2 gives reachable tl root e.v, contradicts hypothesis
                  // So must be case 1: reachable tl e.v v
                  ()
                end
              end)
        end
      end
    end

// Count vertices in [0,n) satisfying predicate
let rec count_pred (f: nat -> bool) (n: nat) : nat =
  if n = 0 then 0
  else (if f (n - 1) then 1 else 0) + count_pred f (n - 1)

// Count vertices in [0,m) reachable from root in es, restricted to v < n
let count_reachable (es: list edge) (root: nat) (n m: nat) : nat =
  count_pred (fun v -> v < n && same_component_dec es root v) m

let rec count_pred_le (f: nat -> bool) (n: nat)
  : Lemma (ensures count_pred f n <= n) (decreases n)
  = if n = 0 then () else count_pred_le f (n - 1)

// If f1 implies f2, count f1 ≤ count f2
let rec count_pred_mono (f1 f2: (nat -> bool)) (n: nat)
  : Lemma (requires forall (i: nat). i < n ==> f1 i ==> f2 i)
          (ensures count_pred f1 n <= count_pred f2 n)
          (decreases n)
  = if n = 0 then () else count_pred_mono f1 f2 (n - 1)

// If f1 and f2 are disjoint: count (f1 ∨ f2) = count f1 + count f2
let rec count_pred_disjoint_union (f1 f2: (nat -> bool)) (n: nat)
  : Lemma (requires forall (i: nat). i < n ==> ~(f1 i /\ f2 i))
          (ensures count_pred (fun i -> f1 i || f2 i) n = count_pred f1 n + count_pred f2 n)
          (decreases n)
  = if n = 0 then () else count_pred_disjoint_union f1 f2 (n - 1)

// Filter edges by predicate
let rec filter_edges (f: edge -> bool) (es: list edge) : list edge =
  match es with
  | [] -> []
  | e :: rest -> if f e then e :: filter_edges f rest else filter_edges f rest

let rec filter_edges_length (f: edge -> bool) (es: list edge)
  : Lemma (ensures length (filter_edges f es) <= length es) (decreases es)
  = match es with | [] -> () | _ :: rest -> filter_edges_length f rest

// Membership in filtered list: if e ∈ es and f e and f respects edge_eq, then e ∈ filter f es
let rec mem_filter_edges_resp (e: edge) (f: edge -> bool) (es: list edge)
  : Lemma (requires mem_edge e es /\ f e /\
                    (forall (e1 e2: edge). edge_eq e1 e2 ==> f e1 = f e2))
          (ensures mem_edge e (filter_edges f es))
          (decreases es)
  = match es with
    | [] -> ()
    | hd :: rest ->
      if edge_eq e hd then begin
        assert (f hd);
        mem_edge_hd hd (filter_edges f rest)
      end else begin
        mem_filter_edges_resp e f rest;
        if f hd then () else ()
      end

// Subset of filtered edges  
let rec subset_filter_edges (f: edge -> bool) (es: list edge)
  : Lemma (ensures subset_edges (filter_edges f es) es) (decreases es)
  = match es with
    | [] -> ()
    | hd :: rest ->
      subset_filter_edges f rest;
      subset_edges_cons (filter_edges f rest) hd rest

// Disjoint filters have total length ≤ original
let rec disjoint_filter_sum (f1 f2: edge -> bool) (es: list edge)
  : Lemma (requires forall (e: edge). ~(f1 e /\ f2 e))
          (ensures length (filter_edges f1 es) + length (filter_edges f2 es) <= length es)
          (decreases es)
  = match es with | [] -> () | _ :: rest -> disjoint_filter_sum f1 f2 rest

// Path from root stays in root's component: all edges have reachable endpoints
let rec path_stays_in_component (es: list edge) (root: nat) (path: list edge) (u v: nat)
  : Lemma (requires is_path_from_to path u v /\ subset_edges path es /\
                    same_component es root u)
          (ensures forall (pe: edge). mem_edge pe path ==>
                    same_component es root pe.u /\ same_component es root pe.v)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd es);
      let next = if hd.u = u then hd.v else hd.u in
      // hd connects u to next; hd ∈ es
      // Paths [hd] from u to next and from next to u exist via the single edge hd in es
      assert (is_path_from_to [hd] u next);
      subset_edges_reflexive [hd];
      // So u and next are in same component
      assert (same_component es u next);
      // root reaches u, u reaches next → root reaches next
      reachable_transitive es root u next;
      // root reaches hd.u: either hd.u = u (reachable from root) or hd.u = next (reachable)
      assert (hd.u = u \/ hd.u = next);
      (if hd.u = u then () else ());
      reachable_transitive es root u hd.u;
      reachable_transitive es root u hd.v;
      // Recurse on tail
      path_stays_in_component es root tl next v

// Reachability from root using component edges = using all edges
let reachable_uses_component_edges (es: list edge) (root v: nat)
  : Lemma (requires same_component es root v)
          (ensures (let g = fun (e: edge) -> same_component_dec es root e.u &&
                                              same_component_dec es root e.v in
                    same_component (filter_edges g es) root v))
  = let g = fun (e: edge) -> same_component_dec es root e.u &&
                              same_component_dec es root e.v in
    eliminate exists (path: list edge).
      subset_edges path es /\ is_path_from_to path root v
    returns same_component (filter_edges g es) root v
    with _. begin
      same_component_reflexive es root;
      path_stays_in_component es root path root v;
      // All edges in path have endpoints reachable from root
      // So they satisfy g, hence are in filter_edges g es
      // We need: subset_edges path (filter_edges g es)
      let rec path_in_filtered (p: list edge)
        : Lemma (requires subset_edges p es /\
                          (forall (pe: edge). mem_edge pe p ==>
                            same_component es root pe.u /\ same_component es root pe.v))
                (ensures subset_edges p (filter_edges g es))
                (decreases p)
        = match p with
          | [] -> ()
          | hd :: tl_p ->
            assert (same_component es root hd.u);
            assert (same_component es root hd.v);
            same_component_dec_complete es root hd.u;
            same_component_dec_complete es root hd.v;
            assert (g hd);
            // g respects edge_eq: endpoints are same set under edge_eq
            let g_respects_eq (e1 e2: edge) 
              : Lemma (requires edge_eq e1 e2) (ensures g e1 = g e2)
              = edge_eq_endpoints e1 e2;
                // e1 and e2 have same endpoint set
                assert ((e1.u = e2.u /\ e1.v = e2.v) \/ (e1.u = e2.v /\ e1.v = e2.u))
            in
            FStar.Classical.forall_intro_2 (fun e1 -> 
              FStar.Classical.move_requires (g_respects_eq e1));
            mem_filter_edges_resp hd g es;
            path_in_filtered tl_p
      in
      path_in_filtered path
    end

// The component filter respects edge_eq
let component_filter_respects_eq (es: list edge) (root: nat) (e1 e2: edge)
  : Lemma (requires edge_eq e1 e2)
          (ensures (let g = fun (e: edge) -> same_component_dec es root e.u &&
                                              same_component_dec es root e.v in
                    g e1 = g e2))
  = edge_eq_endpoints e1 e2

// Bridge edge decomposition: symmetric version (e.v reachable, e.u not)
let bridge_edge_reachability_sym (tl: list edge) (e: edge) (root v: nat)
  : Lemma (requires same_component tl root e.v /\ ~(same_component tl root e.u) /\
                    same_component (e :: tl) root v)
          (ensures same_component tl root v \/ same_component tl e.u v)
  = if same_component_dec tl root v then
      same_component_dec_sound tl root v
    else begin
      eliminate exists (path: list edge).
        subset_edges path (e :: tl) /\ is_path_from_to path root v
      returns (same_component tl root v \/ same_component tl e.u v)
      with _. begin
        if root = v then begin same_component_reflexive tl root; () end
        else begin
          extract_simple_path path root v;
          FStar.Classical.exists_elim
            (same_component tl root v \/ same_component tl e.u v)
            #_
            #(fun (path': list edge) -> is_path_from_to path' root v /\
                subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
            ()
            (fun path' ->
              subset_edges_transitive path' path (e :: tl);
              if not (mem_edge_in_list e path') then begin
                path_not_using_e_in_t path' e tl; ()
              end else begin
                split_at_first_e path' e tl root v;
                // (reachable tl root e.u /\ reachable tl e.v v) \/
                // (reachable tl root e.v /\ reachable tl e.u v)
                // Case 1: reachable tl root e.u → contradicts ~(same_component tl root e.u)
                // So must be case 2: reachable tl e.u v
                assert (reachable tl root e.u \/ reachable tl e.u v);
                ()
              end)
        end
      end
    end

// Helper: bfs_reach_list with empty edges and singleton frontier returns [u]
let bfs_reach_empty_edges_0 (u: nat)
  : Lemma (ensures bfs_reach_list [] [u] [] 1 == [u])
  = assert (edge_neighbors ([] #edge) u == []);
    List.Tot.Properties.append_nil_l ([] #nat)

// Helper: same_component_dec with no edges only returns true for equal vertices
let same_component_dec_empty_0 (u v: nat)
  : Lemma (ensures same_component_dec [] u v = (u = v))
  = if u = v then ()
    else begin
      bfs_reach_empty_edges_0 u;
      assert (bfs_reach_list [] [u] [] 1 == [u]);
      assert (mem v [u] = (v = u))
    end

// Key counting lemma: number of reachable vertices ≤ 1 + number of edges
// Uses count_reachable to ensure a single lambda symbol in SMT encoding
#push-options "--z3rlimit 50"
let rec count_reachable_bound (es: list edge) (root: nat) (n: nat)
  : Lemma (ensures count_reachable es root n n <= 1 + length es)
          (decreases length es)
  = match es with
    | [] ->
      let rec count_empty (m: nat)
        : Lemma (ensures count_reachable es root n m
                  = (if root < m && root < n then 1 else 0))
                (decreases m)
        = if m = 0 then ()
          else begin
            same_component_dec_empty_0 root (m - 1);
            count_empty (m - 1)
          end
      in
      count_empty n
    | e :: tl ->
      count_reachable_bound tl root n;
      let u_reach = same_component_dec tl root e.u in
      let v_reach = same_component_dec tl root e.v in
      if u_reach && v_reach then begin
        same_component_dec_sound tl root e.u;
        same_component_dec_sound tl root e.v;
        let rec bound_both (m: nat)
          : Lemma (ensures count_reachable es root n m <= count_reachable tl root n m)
                  (decreases m)
          = if m = 0 then ()
            else begin
              bound_both (m - 1);
              if (m - 1) < n && same_component_dec es root (m - 1) then begin
                same_component_dec_sound es root (m - 1);
                redundant_edge_reachability tl e root (m - 1);
                same_component_dec_complete tl root (m - 1)
              end else ()
            end
        in
        bound_both n
      end else if not u_reach && not v_reach then begin
        FStar.Classical.move_requires (same_component_dec_complete tl root) e.u;
        FStar.Classical.move_requires (same_component_dec_complete tl root) e.v;
        let rec bound_neither (m: nat)
          : Lemma (ensures count_reachable es root n m <= count_reachable tl root n m)
                  (decreases m)
          = if m = 0 then ()
            else begin
              bound_neither (m - 1);
              if (m - 1) < n && same_component_dec es root (m - 1) then begin
                same_component_dec_sound es root (m - 1);
                neither_endpoint_reachability tl e root (m - 1);
                same_component_dec_complete tl root (m - 1)
              end else ()
            end
        in
        bound_neither n
      end else begin
        // Bridge case: one endpoint reachable, the other not
        let e_v = if u_reach then e.v else e.u in
        (if u_reach then begin
          same_component_dec_sound tl root e.u;
          FStar.Classical.move_requires (same_component_dec_complete tl root) e.v
        end else begin
          same_component_dec_sound tl root e.v;
          FStar.Classical.move_requires (same_component_dec_complete tl root) e.u
        end);
        assert (~(same_component tl root e_v));

        let g_root = fun (ed: edge) -> same_component_dec tl root ed.u &&
                                        same_component_dec tl root ed.v in
        let g_ev = fun (ed: edge) -> same_component_dec tl e_v ed.u &&
                                      same_component_dec tl e_v ed.v in
        let es_root = filter_edges g_root tl in
        let es_ev = filter_edges g_ev tl in

        introduce forall (ed: edge). ~(g_root ed /\ g_ev ed)
        with begin
          if g_root ed && g_ev ed then begin
            same_component_dec_sound tl root ed.u;
            same_component_dec_sound tl e_v ed.u;
            same_component_symmetric tl root ed.u;
            same_component_symmetric tl e_v ed.u;
            reachable_transitive tl root ed.u e_v;
            same_component_dec_complete tl root e_v;
            assert false
          end else ()
        end;
        disjoint_filter_sum g_root g_ev tl;
        filter_edges_length g_root tl;
        filter_edges_length g_ev tl;
        count_reachable_bound es_root root n;
        count_reachable_bound es_ev e_v n;

        let rec root_comp (m: nat)
          : Lemma (ensures count_reachable tl root n m <= count_reachable es_root root n m)
                  (decreases m)
          = if m = 0 then ()
            else begin
              root_comp (m - 1);
              if (m - 1) < n && same_component_dec tl root (m - 1) then begin
                same_component_dec_sound tl root (m - 1);
                reachable_uses_component_edges tl root (m - 1);
                same_component_dec_complete es_root root (m - 1)
              end else ()
            end
        in
        root_comp n;

        let rec ev_comp (m: nat)
          : Lemma (ensures count_reachable tl e_v n m <= count_reachable es_ev e_v n m)
                  (decreases m)
          = if m = 0 then ()
            else begin
              ev_comp (m - 1);
              if (m - 1) < n && same_component_dec tl e_v (m - 1) then begin
                same_component_dec_sound tl e_v (m - 1);
                reachable_uses_component_edges tl e_v (m - 1);
                same_component_dec_complete es_ev e_v (m - 1)
              end else ()
            end
        in
        ev_comp n;

        introduce forall (i: nat). i < n ==>
          ~((same_component_dec tl root i) && (same_component_dec tl e_v i))
        with begin
          if i < n && same_component_dec tl root i && same_component_dec tl e_v i then begin
            same_component_dec_sound tl root i;
            same_component_dec_sound tl e_v i;
            same_component_symmetric tl e_v i;
            reachable_transitive tl root i e_v;
            same_component_dec_complete tl root e_v;
            assert false
          end else ()
        end;

        introduce forall (v: nat). v < n ==>
          (same_component_dec es root v) ==>
          ((same_component_dec tl root v) \/ (same_component_dec tl e_v v))
        with begin
          if v < n && same_component_dec es root v then begin
            same_component_dec_sound es root v;
            if u_reach then begin
              bridge_edge_reachability tl e root v;
              (if same_component_dec tl root v then ()
               else begin
                 FStar.Classical.move_requires (same_component_dec_complete tl root) v;
                 same_component_dec_complete tl e.v v
               end)
            end else begin
              bridge_edge_reachability_sym tl e root v;
              (if same_component_dec tl root v then ()
               else begin
                 FStar.Classical.move_requires (same_component_dec_complete tl root) v;
                 same_component_dec_complete tl e.u v
               end)
            end
          end
        end;

        let rec count_decomp (m: nat)
          : Lemma (ensures count_reachable es root n m <=
                          count_reachable tl root n m + count_reachable tl e_v n m)
                  (decreases m)
          = if m = 0 then ()
            else count_decomp (m - 1)
        in
        count_decomp n
      end
#pop-options

// A connected graph on n vertices has at least n-1 edges
let connected_min_edges (n: nat) (es: list edge)
  : Lemma (requires n > 0 /\ all_connected n es)
          (ensures length es >= n - 1)
  = let rec count_all (m: nat)
      : Lemma (requires forall (v: nat). v < n ==> same_component es 0 v)
              (ensures count_reachable es 0 n m = min m n)
              (decreases m)
      = if m = 0 then ()
        else begin
          count_all (m - 1);
          if m - 1 < n then begin
            same_component_dec_complete es 0 (m - 1)
          end else ()
        end
    in
    introduce forall (v: nat). v < n ==> same_component es 0 v
    with begin
      if v < n then assert (reachable es 0 v)
    end;
    count_all n;
    count_reachable_bound es 0 n

// noRepeats_edge (Kruskal.Spec) and all_edges_distinct (MST.Spec) are identical definitions
let rec noRepeats_is_all_edges_distinct (l: list edge)
  : Lemma (ensures noRepeats_edge l = all_edges_distinct l)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> noRepeats_is_all_edges_distinct tl

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let theorem_kruskal_produces_spanning_tree (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u <> e.v))
          (ensures (let result = pure_kruskal g in
                    is_spanning_tree g result))
  = let result = pure_kruskal g in
    let sorted = sort_edges g.edges in
    
    // Part 1: Result is a forest (acyclic)
    lemma_kruskal_process_preserves_forest sorted [] g.n;
    assert (acyclic g.n result);
    
    // Part 2: All edges from graph
    sort_edges_subset g.edges;
    lemma_kruskal_process_edges_from_graph sorted [] g.edges g.n;
    assert (subset_edges result g.edges);
    
    // Part 3: Result connects all vertices
    lemma_kruskal_process_maximal_forest sorted sorted [] g.n;
    introduce forall (v: nat). v < g.n ==> reachable result 0 v
    with introduce _ ==> _ with _. begin
      FStar.Classical.exists_elim (reachable result 0 v)
        #_ 
        #(fun (path: list edge) -> subset_edges path g.edges /\ is_path_from_to path 0 v) ()
        (fun (path: list edge{subset_edges path g.edges /\ is_path_from_to path 0 v}) ->
          introduce forall (e: edge). mem_edge e path ==> 
            mem_edge e result \/ same_component result e.u e.v
          with introduce _ ==> _ with _. begin
            mem_edge_of_subset e path g.edges;
            assert (e.u < g.n /\ e.v < g.n);
            sort_edges_mem e g.edges
          end;
          path_edges_connected_implies_endpoints_connected path result 0 v
        )
    end;
    assert (all_connected g.n result);
    
    // Part 4: Result has g.n - 1 edges
    // Direct proof via acyclic_connected_length (no MST existence needed)
    lemma_kruskal_process_no_repeats sorted [] g.n;
    noRepeats_is_all_edges_distinct result;
    introduce forall (e: edge). mem_edge e result ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v
    with introduce _ ==> _ with _. mem_edge_of_subset e result g.edges;
    acyclic_connected_length g.n result
#pop-options

// total_weight of remove_edge_first
let rec total_weight_remove (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures total_weight (remove_edge_first e l) = total_weight l - e.w)
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then ()
      else total_weight_remove e tl

// Helper: if mem_edge e (remove_edge_first x l), then mem_edge e l
let rec mem_remove_edge_first_mem (e x: edge) (l: list edge)
  : Lemma (requires mem_edge e (remove_edge_first x l))
          (ensures mem_edge e l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq x hd then ()
      else if edge_eq e hd then ()
      else mem_remove_edge_first_mem e x tl

// total_weight equality for mutual edge subsets with noRepeats on one side and same length
let rec total_weight_mutual_eq (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b /\
                    (forall (e: edge). mem_edge e b ==> mem_edge e a) /\
                    length a = length b)
          (ensures total_weight a = total_weight b)
          (decreases a)
  = match a with
    | [] -> (match b with | [] -> ())
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      total_weight_remove hd b;
      // total_weight b = total_weight b' + hd.w
      // Need: noRepeats_edge tl, subset_edges tl b'
      // Need: ∀ e ∈ b'. e ∈ tl
      // Need: length tl = length b'
      
      // subset_edges tl b':
      let rec prove_tl_subset (p: list edge)
        : Lemma (requires (forall (e:edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            mem_edge_of_subset e (hd :: tl) b;
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            mem_remove_edge_first_other e hd b;
            prove_tl_subset rest
      in
      prove_tl_subset tl;
      
      // ∀ e ∈ b'. e ∈ tl:
      // Strategy: use the fact that length tl = length b' and subset_edges tl b' 
      // and noRepeats tl. If some e ∈ b' is NOT in tl, then by pigeonhole,
      // tl maps into b' \ {e}, which has length b' - 1, but tl has length b' edges
      // with noRepeats — contradiction with pigeonhole.
      // 
      // More directly: ∀ e ∈ b'. e ∈ b (from mem_remove). e ∈ b ⟹ e ∈ (hd :: tl).
      // So either edge_eq e hd or e ∈ tl.
      // If edge_eq e hd for ALL such e, then all elements of b' are equivalent to hd.
      // But tl ⊆ b' and tl has no element equivalent to hd (noRepeats).
      // So if tl is non-empty, tl has an element not equivalent to hd in b'. Contradiction.
      // If tl is empty, length b' = 0, so b' = []. Fine, vacuously true.
      //
      // Actually the simpler approach: prove it by counting.
      // subset_noRepeats_length_le tl b' gives length tl ≤ length b'.
      // We know length tl = length b'.
      // Every element of b' that's in tl "uses up" one slot.
      // If any element of b' is NOT in tl, then b' has >length tl elements 
      // that need "distinct" matches, but... we need noRepeats on b' for that.
      //
      // Let me try the direct approach:
      introduce forall (e: edge). mem_edge e b' ==> mem_edge e tl
      with introduce _ ==> _ with _. begin
        mem_remove_edge_first_mem e hd b;
        assert (mem_edge e b);
        assert (mem_edge e (hd :: tl));
        // e ∈ (hd :: tl) means edge_eq e hd \/ e ∈ tl
        if mem_edge e tl then ()
        else begin
          // e ∉ tl, so edge_eq e hd
          assert (edge_eq e hd);
          // e ∈ b', e is edge_eq to hd, and e ∉ tl
          // But then: tl maps into b' via subset_edges tl b'.
          // Each edge of tl is NOT edge_eq to hd (from noRepeats).
          // And e IS edge_eq to hd and e ∈ b'.
          // So tl maps into b' minus the positions holding hd-equivalents.
          // But we need a contradiction. 
          // 
          // Consider: if e ∈ b' and edge_eq e hd, then there are ≥2 copies of hd in b
          // (one was removed by remove_edge_first, one remains as e).
          // From subset_edges tl b': length tl ≤ length b' 
          //   (we proved this in subset_noRepeats_length_le).
          // We know length tl = length b'.
          // But tl has no hd-equivalents, so each edge of tl maps to a non-hd-equivalent in b'.
          // If e (which IS hd-equivalent) is in b', then b' has at most (length b' - 1) non-hd-equivalents.
          // So tl can have at most (length b' - 1) edges (pigeonhole into non-hd-equivalents of b').
          // But length tl = length b'. Contradiction!
          //
          // This pigeonhole requires showing the injection maps tl to non-hd-equivalents only.
          // Let me formalize using subset_noRepeats_length_le:
          // Define b'' = remove_edge_first e b' (removing the hd-equivalent from b').
          // Then each edge of tl is in b'' (since tl edges are in b' and not edge_eq hd).
          // So subset_edges tl b''.
          // subset_noRepeats_length_le tl b'' gives length tl ≤ length b''.
          // But length b'' = length b' - 1 = length tl - 1. Contradiction!
          let b'' = remove_edge_first e b' in
          remove_edge_first_length e b';
          let rec tl_subset_b'' (p: list edge)
            : Lemma (requires (forall (x:edge). mem_edge x p ==> mem_edge x tl) /\
                              noRepeats_edge (hd :: tl) /\
                              subset_edges (hd :: tl) b /\
                              mem_edge e b' /\ edge_eq e hd)
                    (ensures subset_edges p b'')
                    (decreases p)
            = match p with
              | [] -> ()
              | x :: rest ->
                assert (mem_edge x tl);
                mem_edge_of_subset x (hd :: tl) b;
                (if edge_eq x hd then begin
                  edge_eq_symmetric x hd;
                  mem_edge_eq hd x tl
                end else ());
                mem_remove_edge_first_other x hd b;
                assert (mem_edge x b');
                // x ∈ b' and ~(edge_eq x hd) and edge_eq e hd
                // Need: ~(edge_eq x e)
                (if edge_eq x e then begin
                  // edge_eq x e and edge_eq e hd ⟹ edge_eq x hd (transitivity via SMT)
                  edge_eq_symmetric e hd;
                  assert (edge_eq hd e);
                  assert (edge_eq x e);
                  // x.u=e.u∧x.v=e.v or x.u=e.v∧x.v=e.u
                  // e.u=hd.u∧e.v=hd.v or e.u=hd.v∧e.v=hd.u  (from edge_eq e hd)
                  // These combine to give edge_eq x hd
                  assert (edge_eq x hd) // should follow from SMT
                end else ());
                mem_remove_edge_first_other x e b';
                tl_subset_b'' rest
          in
          tl_subset_b'' tl;
          subset_noRepeats_length_le tl b'';
          // length tl ≤ length b'' = length b' - 1 = length tl - 1. Contradiction!
          assert false
        end
      end;
      
      total_weight_mutual_eq tl b'

//SNIPPET_START: theorem_kruskal_mst
// Kruskal's algorithm produces a minimum spanning tree
let theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    all_connected g.n g.edges /\
                    (exists (mst: list edge). is_mst g mst) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u <> e.v))
          (ensures (let result = pure_kruskal g in
                    is_mst g result))
//SNIPPET_END: theorem_kruskal_mst
  = theorem_kruskal_produces_spanning_tree g;
    
    let result = pure_kruskal g in
    let sorted = sort_edges g.edges in
    
    // result is a spanning tree
    assert (is_spanning_tree g result);
    
    // MST invariant: result ⊆ some MST
    sort_edges_sorted g.edges;
    sort_edges_subset g.edges;
    introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' sorted) /\
      ~(mem_edge e' ([] #edge)) ==> same_component ([] #edge) e'.u e'.v
    with introduce _ ==> _ with _. begin
      sort_edges_mem e' g.edges
    end;
    lemma_kruskal_process_mst_invariant g sorted [];
    // exists mst'. is_mst g mst' /\ subset_edges result mst'
    FStar.Classical.exists_elim (is_mst g result)
      #_
      #(fun (mst': list edge) -> is_mst g mst' /\ subset_edges result mst') ()
      (fun (mst': list edge{is_mst g mst' /\ subset_edges result mst'}) ->
        // mst' edges inherit valid endpoints and no self-loops
        introduce forall (e: edge). mem_edge e mst' ==> e.u < g.n /\ e.v < g.n
        with introduce _ ==> _ with _. mem_edge_of_subset e mst' g.edges;
        introduce forall (e: edge). mem_edge e mst' ==> e.u <> e.v
        with introduce _ ==> _ with _. mem_edge_of_subset e mst' g.edges;
        connected_subset_of_tree_is_tree g result mst';
        // forall e in mst'. mem_edge e result
        
        // Prove total_weight result = total_weight mst'
        lemma_kruskal_process_no_repeats sorted [] g.n;
        assert (noRepeats_edge result);
        
        // Build subset_edges mst' result from the forall
        let rec build_subset_mst (l: list edge)
          : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e result)
                  (ensures subset_edges l result)
                  (decreases l)
          = match l with | [] -> () | _ :: tl -> build_subset_mst tl
        in
        build_subset_mst mst';

        assert (length result = g.n - 1);
        assert (length mst' = g.n - 1);
        
        total_weight_mutual_eq result mst';
        assert (total_weight result = total_weight mst');
        
        introduce forall (t: list edge). is_spanning_tree g t ==> total_weight result <= total_weight t
        with introduce _ ==> _ with _. ()
      )

(*** Additional Helper Properties ***)

/// Helper: bfs_reach_list with empty edges and singleton frontier returns [u]
let bfs_reach_empty_edges (u: nat)
  : Lemma (ensures bfs_reach_list [] [u] [] 1 == [u])
  = assert (edge_neighbors ([] #edge) u == []);
    List.Tot.Properties.append_nil_l ([] #nat)

/// Helper: same_component_dec with no edges only returns true for equal vertices
let same_component_dec_empty (u v: nat)
  : Lemma (ensures same_component_dec [] u v = (u = v))
  = if u = v then ()
    else begin
      bfs_reach_empty_edges u;
      assert (bfs_reach_list [] [u] [] 1 == [u]);
      assert (mem v [u] = (v = u))
    end

/// Helper: vertices_in_component with empty edges returns [v] when v < n
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let rec vertices_in_component_empty (v: nat) (n: nat) (i: nat{i <= n})
  : Lemma (requires v < n)
          (ensures vertices_in_component [] v n i == (if i <= v && v < n then [v] else []))
          (decreases (n - i))
  = same_component_dec_empty v i;
    if i >= n then ()
    else begin
      vertices_in_component_empty v n (i + 1);
      if i = v then begin
        assert (same_component_dec [] v i = true)
      end else begin
        assert (same_component_dec [] v i = false)
      end
    end
#pop-options

/// Helper: component_of with empty edges is [v] when v < n
let component_of_empty (v: nat) (n: nat)
  : Lemma (requires v < n)
          (ensures component_of [] v n == [v])
  = vertices_in_component_empty v n 0

/// Helper: vertex j is not in component_of [] i n when i <> j and both < n
let not_in_different_component_empty (i j: nat) (n: nat)
  : Lemma (requires i < n /\ j < n /\ i <> j)
          (ensures ~(mem j (component_of [] i n)))
  = component_of_empty i n

/// Helper: build_components with empty edges produces n singletons
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec build_components_empty_length (n: nat) (i: nat{i <= n})
                                      (acc: list (list nat))
  : Lemma (requires
             length acc == i /\
             (forall (j: nat{j < i}). mem [j] acc) /\
             (forall (c: list nat). mem c acc ==> (exists (j: nat{j < i}). c == [j])) /\
             (forall (c: list nat). mem c acc ==> ~(mem i c)))
          (ensures length (build_components [] n i acc) == n)
          (decreases (n - i))
  = if i >= n then ()
    else begin
      component_of_empty i n;
      in_some_component_false i acc;
      assert (in_some_component i acc = false);
      let new_comp = component_of [] i n in
      assert (new_comp == [i]);
      let acc' = new_comp :: acc in
      assert (length acc' == i + 1);
      // Part 1: forall j < i+1, [j] in acc'
      let aux1 (j: nat{j < i + 1}) : Lemma (mem [j] acc')
        = if j = i then () else ()
      in
      FStar.Classical.forall_intro aux1;
      // Part 2: all elements of acc' are singletons for vertices < i+1
      let aux2 (c: list nat) : Lemma (requires mem c acc') 
                                     (ensures exists (j: nat{j < i + 1}). c == [j])
        = if c = [i] then ()
          else begin
            assert (mem c acc);
            eliminate exists (j: nat{j < i}). c == [j]
            returns exists (j: nat{j < i + 1}). c == [j]
            with _. ()
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
      // Part 3: i+1 is not in any component in acc'
      if i + 1 <= n then begin
        let aux3 (c: list nat) : Lemma (requires mem c acc')
                                       (ensures ~(mem (i + 1) c))
          = if c = [i] then ()
            else begin
              assert (mem c acc);
              eliminate exists (j: nat{j < i}). c == [j]
              returns ~(mem (i + 1) c)
              with _. ()
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux3)
      end;
      build_components_empty_length n (i + 1) acc'
    end
#pop-options

// Initially n components (each vertex is its own component)
let lemma_initial_components (n: nat)
  : Lemma (requires n > 0)
          (ensures length (components [] n) = n)
  = build_components_empty_length n 0 []

// Final spanning tree has 1 component
let lemma_spanning_tree_one_component (g: graph) (t: list edge)
  : Lemma (requires is_spanning_tree g t)
          (ensures length (components t g.n) = 1)
  = // all_connected g.n t: forall v < g.n. reachable t 0 v
    // So same_component t 0 v for all v < g.n
    // By BFS completeness: same_component_dec t 0 v = true for all v < g.n
    let n = g.n in
    assert (n > 0);
    assert (all_connected n t);

    // Step 1: same_component_dec t 0 v = true for all v < n
    let aux_dec (v: nat)
      : Lemma (requires v < n) (ensures same_component_dec t 0 v = true)
      = assert (reachable t 0 v);
        same_component_dec_complete t 0 v
    in

    // Step 2: vertices_in_component t 0 n i includes all vertices from i to n-1
    let rec all_in_component (i: nat{i <= n})
      : Lemma (ensures forall (v: nat). i <= v /\ v < n ==>
                        mem v (vertices_in_component t 0 n i))
              (decreases (n - i))
      = if i >= n then ()
        else begin
          aux_dec i;
          assert (same_component_dec t 0 i = true);
          all_in_component (i + 1);
          // vertices_in_component t 0 n i = i :: vertices_in_component t 0 n (i+1)
          // All v with i+1 <= v < n are in the tail (by IH)
          // And i itself is the head
          ()
        end
    in
    all_in_component 0;
    // component_of t 0 n contains all vertices 0..n-1
    assert (forall (v: nat). v < n ==> mem v (component_of t 0 n));

    // Step 3: in_some_component returns true for all v < n when acc = [component_of t 0 n]
    let in_comp_of_0 (v: nat)
      : Lemma (requires v < n)
              (ensures in_some_component v [component_of t 0 n] = true)
      = assert (mem v (component_of t 0 n))
    in

    // Step 4: build_components with i=0 creates exactly [component_of t 0 n]
    // At i=0: 0 is not in acc=[]. Creates component_of t 0 n. acc = [component_of t 0 n].
    // For i=1..n-1: i is in component_of t 0 n, so in_some_component i acc = true. Skip.
    let rec build_one_comp (i: nat{i <= n})
      : Lemma (requires i > 0)
              (ensures build_components t n i [component_of t 0 n] == [component_of t 0 n])
              (decreases (n - i))
      = if i >= n then ()
        else begin
          in_comp_of_0 i;
          assert (in_some_component i [component_of t 0 n] = true);
          build_one_comp (i + 1)
        end
    in

    // At i=0: 0 is not in [], creates component_of t 0 n
    in_some_component_false 0 ([] #(list nat));
    assert (in_some_component 0 ([] #(list nat)) = false);
    // build_components t n 0 [] = build_components t n 1 [component_of t 0 n]
    if n > 1 then build_one_comp 1
    else ()
    // Result: [component_of t 0 n], length = 1
