(*
   CLRS Chapter 23: Prim's MST Algorithm - Pure Specification
   
   This module provides a pure functional specification of Prim's algorithm
   and proves its correctness using the Cut Property from CLRS.Ch23.MST.Spec.
   
   Key correctness properties:
   1. Safe-edge property: Each edge added is safe (via Cut Property)
   2. Result has n-1 edges (one per iteration)
   3. Result is a spanning tree
   4. Result has minimum total weight
*)

module CLRS.Ch23.Prim.Spec

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch23.MST.Spec

(*** Adjacency Matrix Representation ***)

// Well-formed adjacency matrix: square, symmetric
let well_formed_adj (adj: adj_matrix) (n: nat) : prop =
  length adj = n /\
  (forall (u: nat). u < n ==> length (index adj u) = n) /\
  (forall (u v: nat). u < n /\ v < n ==> 
    index (index adj u) v = index (index adj v) u)

let well_formed_adj_intro (adj: adj_matrix) (n: nat)
  : Lemma (requires length adj = n /\
                    (forall (u: nat). u < n ==> length (index adj u) = n) /\
                    (forall (u v: nat). u < n /\ v < n ==>
                      index (index adj u) v = index (index adj v) u))
          (ensures well_formed_adj adj n)
  = ()

// Edge exists in adjacency matrix
let has_edge (adj: adj_matrix) (n: nat) (u v: nat) : bool =
  u < n && v < n && u < length adj && v < length (index adj u) &&
  index (index adj u) v <> infinity

let has_edge_intro (adj: adj_matrix) (n: nat) (u v: nat)
  : Lemma (requires u < n /\ v < n /\ length adj = n /\ length (index adj u) = n /\
                    index (index adj u) v <> infinity)
          (ensures has_edge adj n u v = true)
  = ()

// Weight of edge in adjacency matrix
let edge_weight (adj: adj_matrix) (u v: nat{u < length adj /\ v < length (index adj u)}) : int =
  index (index adj u) v

// Convert adjacency matrix to graph representation
let rec adj_to_edges_row (adj: adj_matrix) (n: nat) (u: nat) (v: nat) 
  : Tot (list edge) (decreases (n - v))
  = if v >= n then []
    else if u < n && v < n && has_edge adj n u v && u < v then
      // Only include u < v to avoid duplicates in undirected graph
      {u = u; v = v; w = edge_weight adj u v} :: adj_to_edges_row adj n u (v + 1)
    else
      adj_to_edges_row adj n u (v + 1)

let rec adj_to_edges_aux (adj: adj_matrix) (n: nat) (u: nat)
  : Tot (list edge) (decreases (n - u))
  = if u >= n then []
    else adj_to_edges_row adj n u 0 @ adj_to_edges_aux adj n (u + 1)

let adj_to_edges (adj: adj_matrix) (n: nat) : list edge =
  adj_to_edges_aux adj n 0

let adj_to_graph (adj: adj_matrix) (n: nat) : graph =
  {n = n; edges = adj_to_edges adj n}

let adj_to_graph_edges (adj: adj_matrix) (n: nat)
  : Lemma (ensures (adj_to_graph adj n).edges == adj_to_edges adj n /\
                   (adj_to_graph adj n).n == n)
  = ()

// All edges produced by adj_to_edges_row have valid endpoints
let rec adj_to_edges_row_valid (adj: adj_matrix) (n: nat) (u: nat) (v: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_edges_row adj n u v))
          (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
          (decreases (n - v))
  = if v >= n then ()
    else if u < n && v < n && has_edge adj n u v && u < v then
      if edge_eq e {u = u; v = v; w = edge_weight adj u v} then
        edge_eq_endpoints e {u = u; v = v; w = edge_weight adj u v}
      else adj_to_edges_row_valid adj n u (v + 1) e
    else adj_to_edges_row_valid adj n u (v + 1) e

// All edges produced by adj_to_edges_aux have valid endpoints
let rec adj_to_edges_aux_valid (adj: adj_matrix) (n: nat) (u: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_edges_aux adj n u))
          (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
          (decreases (n - u))
  = if u >= n then ()
    else begin
      let row = adj_to_edges_row adj n u 0 in
      let rest = adj_to_edges_aux adj n (u + 1) in
      mem_edge_append e row rest;
      if mem_edge e row then adj_to_edges_row_valid adj n u 0 e
      else adj_to_edges_aux_valid adj n (u + 1) e
    end

// All edges in adj_to_graph have valid endpoints
let adj_to_graph_edges_valid (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_graph adj n).edges)
          (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
  = adj_to_edges_aux_valid adj n 0 e

/// Row-level: edge weight equals adj matrix entry
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec adj_to_edges_row_weight (adj: adj_matrix) (n: nat) (u: nat) (v: nat) (e: edge)
  : Lemma (requires well_formed_adj adj n /\ u < n /\ v <= n /\ n > 0 /\
                    mem_edge e (adj_to_edges_row adj n u v) /\ e.u < n /\ e.v < n)
          (ensures e.w = index (index adj e.u) e.v)
          (decreases (n - v))
  = if v >= n then ()
    else if u < n && v < n && has_edge adj n u v && u < v then
      if edge_eq e {u = u; v = v; w = edge_weight adj u v} then begin
        edge_eq_endpoints e {u = u; v = v; w = edge_weight adj u v};
        // e.w = edge_weight adj u v = adj[u][v]
        // {e.u,e.v} = {u,v}. By well_formed (symmetric): adj[e.u][e.v] = adj[u][v]
        ()
      end
      else adj_to_edges_row_weight adj n u (v + 1) e
    else adj_to_edges_row_weight adj n u (v + 1) e

let rec adj_to_edges_aux_weight (adj: adj_matrix) (n: nat) (u: nat) (e: edge)
  : Lemma (requires well_formed_adj adj n /\ u <= n /\ n > 0 /\
                    mem_edge e (adj_to_edges_aux adj n u) /\ e.u < n /\ e.v < n)
          (ensures e.w = index (index adj e.u) e.v)
          (decreases (n - u))
  = if u >= n then ()
    else begin
      mem_edge_append e (adj_to_edges_row adj n u 0) (adj_to_edges_aux adj n (u + 1));
      if mem_edge e (adj_to_edges_row adj n u 0) then
        adj_to_edges_row_weight adj n u 0 e
      else
        adj_to_edges_aux_weight adj n (u + 1) e
    end
#pop-options

let adj_to_graph_edge_weight (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires well_formed_adj adj n /\ n > 0 /\
                    mem_edge e (adj_to_graph adj n).edges /\
                    e.u < n /\ e.v < n /\ length adj = n /\ length (index adj e.u) = n)
          (ensures e.w = index (index adj e.u) e.v)
  = adj_to_edges_aux_weight adj n 0 e

// If has_edge, the edge is in adj_to_edges_row
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec adj_to_graph_row_has_edge (adj: adj_matrix) (n: nat) (u v v0: nat)
  : Lemma (requires u < n /\ v < n /\ u < v /\ v0 <= v /\
                    has_edge adj n u v /\ well_formed_adj adj n)
          (ensures mem_edge ({u = u; v = v; w = edge_weight adj u v})
                            (adj_to_edges_row adj n u v0))
          (decreases (n - v0))
  = if v0 >= n then ()
    else if v0 = v then begin
      edge_eq_reflexive ({u = u; v = v; w = edge_weight adj u v})
    end
    else adj_to_graph_row_has_edge adj n u v (v0 + 1)

let adj_to_graph_aux_has_edge (adj: adj_matrix) (n: nat) (u v: nat)
  : Lemma (requires u < n /\ v < n /\ u < v /\
                    has_edge adj n u v /\ well_formed_adj adj n)
          (ensures mem_edge ({u = u; v = v; w = edge_weight adj u v})
                            (adj_to_edges adj n))
  = adj_to_graph_row_has_edge adj n u v 0;
    let e = {u = u; v = v; w = edge_weight adj u v} in
    let rec aux_mem (u0: nat)
      : Lemma (requires u0 <= u /\ mem_edge e (adj_to_edges_row adj n u 0))
              (ensures mem_edge e (adj_to_edges_aux adj n u0))
              (decreases (n - u0))
      = if u0 >= n then ()
        else begin
          mem_edge_append e (adj_to_edges_row adj n u0 0) (adj_to_edges_aux adj n (u0 + 1));
          if u0 = u then ()
          else begin
            aux_mem (u0 + 1);
            assert (mem_edge e (adj_to_edges_aux adj n (u0 + 1)))
          end
        end
    in
    aux_mem 0

let adj_to_graph_has_edge (adj: adj_matrix) (n: nat) (eu ev: nat)
  : Lemma (requires well_formed_adj adj n /\ eu < n /\ ev < n /\ eu < ev /\
                    has_edge adj n eu ev)
          (ensures mem_edge ({u = eu; v = ev; w = index (index adj eu) ev})
                            (adj_to_graph adj n).edges)
  = adj_to_graph_aux_has_edge adj n eu ev
#pop-options

(*** Prim's Algorithm State ***)

// Check if vertex is in tree
let in_tree (s: vertex_set) (v: nat) : prop =
  v < length s /\ index s v = true

// Count vertices in tree
let rec count_tree_vertices_aux (s: vertex_set) (i: nat)
  : Tot nat (decreases (length s - i))
  = if i >= length s then 0
    else (if index s i then 1 else 0) + count_tree_vertices_aux s (i + 1)

let count_tree_vertices (s: vertex_set) : nat =
  count_tree_vertices_aux s 0

// All vertices in tree
let all_in_tree (s: vertex_set) (n: nat) : bool =
  length s = n && count_tree_vertices s = n

// Create cut from vertex set: true for tree vertices, false for non-tree
let vertex_set_to_cut (s: vertex_set) : cut =
  fun (v: nat) -> v < length s && index s v

(*** Prim's Algorithm: Find Minimum Weight Edge ***)

// Find minimum-weight edge from tree to non-tree vertex
// Returns None if no such edge exists
let rec find_min_edge_from_row
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (u: nat)  // tree vertex (row)
    (v: nat)  // scanning column v
    (current_min: option edge)
  : Tot (option edge) (decreases (n - v))
  = if v >= n then current_min
    else if u < length in_tree && v < length in_tree && 
            index in_tree u && not (index in_tree v) && has_edge adj n u v then
      let w = edge_weight adj u v in
      let new_min = match current_min with
        | None -> Some ({u = u; v = v; w = w})
        | Some e -> if w < e.w then Some ({u = u; v = v; w = w}) else current_min
      in
      find_min_edge_from_row adj n in_tree u (v + 1) new_min
    else
      find_min_edge_from_row adj n in_tree u (v + 1) current_min

let rec find_min_edge_aux
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (u: nat)  // scanning row u
    (current_min: option edge)
  : Tot (option edge) (decreases (n - u))
  = if u >= n then current_min
    else 
      let row_min = find_min_edge_from_row adj n in_tree u 0 None in
      let new_min = match current_min, row_min with
        | None, None -> None
        | Some e, None -> Some e
        | None, Some e -> Some e
        | Some e1, Some e2 -> if e2.w < e1.w then Some e2 else Some e1
      in
      find_min_edge_aux adj n in_tree (u + 1) new_min

// Find minimum-weight edge crossing the cut (tree, non-tree)
let pure_prim_step 
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
  : option edge
  = find_min_edge_aux adj n in_tree 0 None

(*** Prim's Algorithm: Iterative Construction ***)

// Update vertex set by adding vertex v
let add_to_tree (s: vertex_set) (v: nat) : vertex_set =
  if v < length s then upd s v true else s

// Lemma: add_to_tree preserves length
let lemma_add_to_tree_preserves_length (s: vertex_set) (v: nat)
  : Lemma (length (add_to_tree s v) = length s)
  = ()

// Lemma: add_to_tree preserves existing membership
let lemma_add_to_tree_preserves (s: vertex_set) (v: nat) (u: nat)
  : Lemma (requires in_tree s u /\ u <> v)
          (ensures in_tree (add_to_tree s v) u)
  = if v < length s then Seq.lemma_index_upd2 s v true u else ()

// Lemma: add_to_tree adds the target vertex
let lemma_add_to_tree_adds (s: vertex_set) (v: nat)
  : Lemma (requires v < length s)
          (ensures in_tree (add_to_tree s v) v)
  = Seq.lemma_index_upd1 s v true

(*** Helper Predicates and Lemmas ***)

// Predicate: edge is a valid crossing edge (u in tree, v not in tree)
// with correct weight from adjacency matrix
let valid_crossing_edge (e: edge) (its: vertex_set) : prop =
  e.u < length its /\ e.v < length its /\
  index its e.u = true /\ index its e.v = false

let valid_crossing_with_weight (adj: adj_matrix) (n: nat) (e: edge) (its: vertex_set) : prop =
  valid_crossing_edge e its /\
  has_edge adj n e.u e.v /\ e.w = edge_weight adj e.u e.v

// find_min_edge_from_row returns valid crossing edge with correct weight
let rec lemma_find_min_row_valid
    (adj: adj_matrix) (n: nat) (its: vertex_set) (u: nat) (v: nat) (cm: option edge)
  : Lemma (requires (match cm with None -> True | Some e -> valid_crossing_with_weight adj n e its))
          (ensures (match find_min_edge_from_row adj n its u v cm with
                   | None -> True | Some e -> valid_crossing_with_weight adj n e its))
          (decreases (n - v))
  = if v >= n then ()
    else if u < length its && v < length its &&
            index its u && not (index its v) && has_edge adj n u v then
      let w = edge_weight adj u v in
      let nm = match cm with
        | None -> Some ({u = u; v = v; w = w})
        | Some e -> if w < e.w then Some ({u = u; v = v; w = w}) else cm
      in lemma_find_min_row_valid adj n its u (v + 1) nm
    else lemma_find_min_row_valid adj n its u (v + 1) cm

// find_min_edge_aux returns valid crossing edge with correct weight
let rec lemma_find_min_aux_valid
    (adj: adj_matrix) (n: nat) (its: vertex_set) (u: nat) (cm: option edge)
  : Lemma (requires (match cm with None -> True | Some e -> valid_crossing_with_weight adj n e its))
          (ensures (match find_min_edge_aux adj n its u cm with
                   | None -> True | Some e -> valid_crossing_with_weight adj n e its))
          (decreases (n - u))
  = if u >= n then ()
    else begin
      lemma_find_min_row_valid adj n its u 0 None;
      let rm = find_min_edge_from_row adj n its u 0 None in
      let nm = match cm, rm with
        | None, None -> None | Some e, None -> Some e
        | None, Some e -> Some e
        | Some e1, Some e2 -> if e2.w < e1.w then Some e2 else Some e1
      in lemma_find_min_aux_valid adj n its (u + 1) nm
    end

// Minimality: find_min_edge_from_row returns minimum weight
let rec lemma_find_min_row_min
    (adj: adj_matrix) (n: nat) (its: vertex_set) (u: nat) (v: nat) (cm: option edge)
  : Lemma
      (ensures (let result = find_min_edge_from_row adj n its u v cm in
                (match cm, result with
                 | Some _, None -> False | Some c, Some r -> r.w <= c.w | None, _ -> True) /\
                (match result with
                 | Some r ->
                   (forall (v': nat). v <= v' /\ v' < n /\
                     u < length its /\ v' < length its /\
                     index its u = true /\ index its v' = false /\
                     has_edge adj n u v' ==>
                     r.w <= edge_weight adj u v')
                 | None ->
                   (forall (v': nat). v <= v' /\ v' < n ==>
                     ~(u < length its /\ v' < length its /\
                       index its u = true /\ index its v' = false /\
                       has_edge adj n u v')))))
      (decreases (n - v))
  = if v >= n then ()
    else if u < length its && v < length its &&
            index its u && not (index its v) && has_edge adj n u v then
      let w = edge_weight adj u v in
      let nm = match cm with
        | None -> Some ({u = u; v = v; w = w})
        | Some e -> if w < e.w then Some ({u = u; v = v; w = w}) else cm
      in lemma_find_min_row_min adj n its u (v + 1) nm
    else lemma_find_min_row_min adj n its u (v + 1) cm

// Minimality: find_min_edge_aux returns minimum weight
let rec lemma_find_min_aux_min
    (adj: adj_matrix) (n: nat) (its: vertex_set) (u_s: nat) (cm: option edge)
  : Lemma
      (ensures (let result = find_min_edge_aux adj n its u_s cm in
                (match cm, result with
                 | Some _, None -> False | Some c, Some r -> r.w <= c.w | None, _ -> True) /\
                (match result with
                 | Some r ->
                   (forall (u' v': nat). u_s <= u' /\ u' < n /\ v' < n /\
                     u' < length its /\ v' < length its /\
                     index its u' = true /\ index its v' = false /\
                     has_edge adj n u' v' ==>
                     r.w <= edge_weight adj u' v')
                 | None ->
                   (forall (u' v': nat). u_s <= u' /\ u' < n /\ v' < n ==>
                     ~(u' < length its /\ v' < length its /\
                       index its u' = true /\ index its v' = false /\
                       has_edge adj n u' v')))))
      (decreases (n - u_s))
  = if u_s >= n then ()
    else begin
      lemma_find_min_row_min adj n its u_s 0 None;
      let rm = find_min_edge_from_row adj n its u_s 0 None in
      let nm = match cm, rm with
        | None, None -> None | Some e, None -> Some e
        | None, Some e -> Some e
        | Some e1, Some e2 -> if e2.w < e1.w then Some e2 else Some e1
      in lemma_find_min_aux_min adj n its (u_s + 1) nm
    end

(*** Adjacency Matrix Edge Membership Lemmas ***)

// Extract: every edge in adj_to_edges has valid properties
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_adj_row_extract (adj: adj_matrix) (n: nat) (u: nat) (vs: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_edges_row adj n u vs) /\ well_formed_adj adj n)
          (ensures e.u < n /\ e.v < n /\ has_edge adj n e.u e.v /\
                   e.w = edge_weight adj e.u e.v)
          (decreases (n - vs))
  = if vs >= n then ()
    else if u < n && vs < n && has_edge adj n u vs && u < vs then
      (if edge_eq e {u=u;v=vs;w=edge_weight adj u vs} then ()
       else lemma_adj_row_extract adj n u (vs+1) e)
    else lemma_adj_row_extract adj n u (vs+1) e
#pop-options

#push-options "--z3rlimit 20 --fuel 1"
let rec lemma_adj_aux_extract (adj: adj_matrix) (n: nat) (us: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_edges_aux adj n us) /\ well_formed_adj adj n)
          (ensures e.u < n /\ e.v < n /\ has_edge adj n e.u e.v /\
                   e.w = edge_weight adj e.u e.v)
          (decreases (n - us))
  = if us >= n then ()
    else begin
      mem_edge_append e (adj_to_edges_row adj n us 0) (adj_to_edges_aux adj n (us+1));
      if mem_edge e (adj_to_edges_row adj n us 0) then
        lemma_adj_row_extract adj n us 0 e
      else lemma_adj_aux_extract adj n (us+1) e
    end
#pop-options

let lemma_adj_extract (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_edges adj n) /\ well_formed_adj adj n)
          (ensures e.u < n /\ e.v < n /\ has_edge adj n e.u e.v /\
                   e.w = edge_weight adj e.u e.v)
  = lemma_adj_aux_extract adj n 0 e

// If has_edge and u < v, edge is in adj_to_edges_row
let rec lemma_in_adj_row (adj: adj_matrix) (n: nat) (u: nat) (v: nat) (vs: nat)
  : Lemma (requires u < n /\ v < n /\ u < v /\ has_edge adj n u v /\ vs <= v /\
                    well_formed_adj adj n)
          (ensures mem_edge ({u=u;v=v;w=edge_weight adj u v}) (adj_to_edges_row adj n u vs))
          (decreases (n - vs))
  = if vs >= n then ()
    else if vs = v then edge_eq_reflexive ({u=u;v=v;w=edge_weight adj u v})
    else lemma_in_adj_row adj n u v (vs+1)

// Edge in adj_to_edges_row is in adj_to_edges_aux
let rec lemma_in_adj_aux (adj: adj_matrix) (n: nat) (u: nat) (us: nat) (e: edge)
  : Lemma (requires u < n /\ us <= u /\ mem_edge e (adj_to_edges_row adj n u 0))
          (ensures mem_edge e (adj_to_edges_aux adj n us))
          (decreases (n - us))
  = if us >= n then ()
    else if us = u then
      mem_edge_append e (adj_to_edges_row adj n u 0) (adj_to_edges_aux adj n (u+1))
    else begin
      lemma_in_adj_aux adj n u (us+1) e;
      mem_edge_append e (adj_to_edges_row adj n us 0) (adj_to_edges_aux adj n (us+1))
    end

// has_edge implies mem_edge in adj_to_edges
#push-options "--z3rlimit 20"
let lemma_has_edge_in_adj (adj: adj_matrix) (n: nat) (u v: nat)
  : Lemma (requires well_formed_adj adj n /\ u < n /\ v < n /\ u <> v /\ has_edge adj n u v)
          (ensures mem_edge ({u=u;v=v;w=edge_weight adj u v}) (adj_to_edges adj n))
  = if u < v then begin
      lemma_in_adj_row adj n u v 0;
      lemma_in_adj_aux adj n u 0 ({u=u;v=v;w=edge_weight adj u v})
    end else begin
      let canonical = {u=v;v=u;w=edge_weight adj v u} in
      lemma_in_adj_row adj n v u 0;
      lemma_in_adj_aux adj n v 0 canonical;
      assert (edge_eq ({u=u;v=v;w=edge_weight adj u v}) canonical);
      edge_eq_symmetric ({u=u;v=v;w=edge_weight adj u v}) canonical;
      mem_edge_eq canonical ({u=u;v=v;w=edge_weight adj u v}) (adj_to_edges adj n)
    end
#pop-options

(*** Count Helpers ***)

#push-options "--fuel 2"
let rec lemma_count_le_length (s: vertex_set) (i: nat)
  : Lemma (ensures count_tree_vertices_aux s i <= length s - (if i <= length s then i else length s))
          (decreases (length s - i))
  = if i >= length s then () else lemma_count_le_length s (i + 1)
#pop-options

let lemma_count_le (s: vertex_set)
  : Lemma (ensures count_tree_vertices s <= length s)
  = lemma_count_le_length s 0

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_count_lt_has_false (s: vertex_set) (i: nat)
  : Lemma (requires count_tree_vertices_aux s i < length s - i /\ i <= length s)
          (ensures (exists (v: nat). i <= v /\ v < length s /\ index s v = false))
          (decreases (length s - i))
  = if i >= length s then ()
    else if index s i then lemma_count_lt_has_false s (i + 1) else ()
#pop-options

let rec lemma_count_add_new (s: vertex_set) (v: nat) (i: nat)
  : Lemma (requires v < length s /\ index s v = false)
          (ensures count_tree_vertices_aux (add_to_tree s v) i =
                   count_tree_vertices_aux s i + (if i <= v && v < length s then 1 else 0))
          (decreases (length s - i))
  = if i >= length s then (lemma_add_to_tree_preserves_length s v)
    else begin
      lemma_add_to_tree_preserves_length s v;
      if i = v then (Seq.lemma_index_upd1 s v true; lemma_count_add_new s v (i + 1))
      else (Seq.lemma_index_upd2 s v true i; lemma_count_add_new s v (i + 1))
    end

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_count_single_true (n: nat) (start: nat) (i: nat)
  : Lemma (requires start < n /\ i <= n)
          (ensures count_tree_vertices_aux (upd (create n false) start true) i =
                   (if i <= start then 1 else 0))
          (decreases (n - i))
  = if i >= n then ()
    else begin
      if i = start then
        (Seq.lemma_index_upd1 (create n false) start true;
         lemma_count_single_true n start (i + 1))
      else
        (Seq.lemma_index_upd2 (create n false) start true i;
         FStar.Seq.Base.lemma_index_create #bool n false i;
         lemma_count_single_true n start (i + 1))
    end
#pop-options

// If count = length, every index is true
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_all_in_tree_means_all_true (s: vertex_set) (i: nat)
  : Lemma (requires count_tree_vertices_aux s i = length s - i /\ i <= length s)
          (ensures (forall (v: nat). i <= v /\ v < length s ==> index s v = true))
          (decreases (length s - i))
  = if i >= length s then ()
    else begin
      lemma_count_le_length s (i + 1);
      if not (index s i) then begin
        assert (count_tree_vertices_aux s i = count_tree_vertices_aux s (i + 1));
        assert (count_tree_vertices_aux s (i + 1) <= length s - i - 1);
        assert False
      end else begin
        assert (count_tree_vertices_aux s (i + 1) = length s - i - 1);
        lemma_all_in_tree_means_all_true s (i + 1)
      end
    end
#pop-options

(*** Connectivity Lemmas ***)

// Connected graph implies crossing edge exists
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let lemma_connected_implies_crossing_edge
    (adj: adj_matrix) (n: nat) (its: vertex_set)
  : Lemma (requires well_formed_adj adj n /\ length its = n /\
                    all_connected n (adj_to_edges adj n) /\ n > 0 /\
                    (exists (u: nat). u < n /\ index its u = true) /\
                    (exists (v: nat). v < n /\ index its v = false))
          (ensures (exists (u' v': nat). u' < n /\ v' < n /\
                    u' < length its /\ v' < length its /\
                    index its u' = true /\ index its v' = false /\
                    has_edge adj n u' v'))
  = let s = vertex_set_to_cut its in
    let edges = adj_to_edges adj n in
    FStar.Classical.exists_elim
      (exists (u' v': nat). u' < n /\ v' < n /\ u' < length its /\ v' < length its /\
        index its u' = true /\ index its v' = false /\ has_edge adj n u' v')
      #nat #(fun v -> v < n /\ index its v = false) ()
      (fun (v: nat{v < n /\ index its v = false}) ->
        FStar.Classical.exists_elim
          (exists (u' v': nat). u' < n /\ v' < n /\ u' < length its /\ v' < length its /\
            index its u' = true /\ index its v' = false /\ has_edge adj n u' v')
          #nat #(fun u -> u < n /\ index its u = true) ()
          (fun (u: nat{u < n /\ index its u = true}) ->
            reachable_symmetric edges 0 u;
            reachable_transitive edges u 0 v;
            FStar.Classical.exists_elim
              (exists (u' v': nat). u' < n /\ v' < n /\ u' < length its /\ v' < length its /\
                index its u' = true /\ index its v' = false /\ has_edge adj n u' v')
              #(list edge) #(fun path -> subset_edges path edges /\ is_path_from_to path u v) ()
              (fun (path: list edge{subset_edges path edges /\ is_path_from_to path u v}) ->
                path_crosses_when_sides_differ path edges s u v;
                FStar.Classical.exists_elim
                  (exists (u' v': nat). u' < n /\ v' < n /\ u' < length its /\ v' < length its /\
                    index its u' = true /\ index its v' = false /\ has_edge adj n u' v')
                  #edge #(fun e' -> mem_edge e' path /\ mem_edge e' edges /\ crosses_cut e' s) ()
                  (fun (e': edge{mem_edge e' path /\ mem_edge e' edges /\ crosses_cut e' s}) ->
                    lemma_adj_extract adj n e';
                    if s e'.u then begin
                      assert (e'.u < n /\ e'.v < n);
                      assert (e'.u < length its /\ e'.v < length its);
                      assert (index its e'.u = true);
                      assert (index its e'.v = false);
                      assert (has_edge adj n e'.u e'.v)
                    end else begin
                      assert (e'.u < n /\ e'.v < n);
                      assert (e'.u < length its /\ e'.v < length its);
                      assert (index its e'.v = true);
                      assert (index its e'.u = false);
                      assert (has_edge adj n e'.v e'.u)
                    end))))
#pop-options

// If there's a crossing pair, find_min returns Some
let lemma_has_crossing_implies_some
    (adj: adj_matrix) (n: nat) (its: vertex_set) (tree_edges: list edge)
  : Lemma (requires well_formed_adj adj n /\ length its = n /\
                    (exists (u' v': nat). u' < n /\ v' < n /\
                     u' < length its /\ v' < length its /\
                     index its u' = true /\ index its v' = false /\
                     has_edge adj n u' v'))
          (ensures Some? (pure_prim_step adj n its tree_edges))
  = lemma_find_min_aux_min adj n its 0 None

(*** Tree Connectivity ***)

// Every tree vertex is reachable from start via tree_edges
let tree_connected (start: nat) (its: vertex_set) (tree_edges: list edge) : prop =
  forall (v: nat). v < length its /\ index its v = true ==>
    reachable tree_edges start v

// Adding an edge preserves reachability
let lemma_reachable_extend (tree_edges: list edge) (e: edge) (start u: nat)
  : Lemma (requires reachable tree_edges start u)
          (ensures reachable (e :: tree_edges) start u)
  = FStar.Classical.exists_elim (reachable (e :: tree_edges) start u)
      #(list edge) #(fun path -> subset_edges path tree_edges /\ is_path_from_to path start u) ()
      (fun (path: list edge{subset_edges path tree_edges /\ is_path_from_to path start u}) ->
        subset_edges_cons path e tree_edges)

let lemma_single_edge_reachable (e: edge) (es: list edge)
  : Lemma (ensures reachable (e :: es) e.u e.v /\ reachable (e :: es) e.v e.u)
  = edge_eq_reflexive e;
    assert (subset_edges [e] (e :: es));
    assert (is_path_from_to [e] e.u e.v);
    assert (is_path_from_to [e] e.v e.u)

// Tree connectivity extends when adding a crossing edge
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let lemma_tree_connected_extend
    (start: nat) (its: vertex_set) (tree_edges: list edge) (e: edge)
  : Lemma (requires tree_connected start its tree_edges /\
                    valid_crossing_edge e its /\
                    start < length its /\ index its start = true)
          (ensures tree_connected start (add_to_tree its e.v) (e :: tree_edges))
  = let its' = add_to_tree its e.v in
    lemma_add_to_tree_preserves_length its e.v;
    introduce forall (v: nat). v < length its' /\ index its' v = true ==>
      reachable (e :: tree_edges) start v
    with introduce _ ==> _ with _h.
      if v = e.v then begin
        lemma_reachable_extend tree_edges e start e.u;
        lemma_single_edge_reachable e tree_edges;
        reachable_transitive (e :: tree_edges) start e.u e.v
      end else begin
        Seq.lemma_index_upd2 its e.v true v;
        lemma_reachable_extend tree_edges e start v
      end
#pop-options

// Prim's algorithm: iteratively grow tree
let rec pure_prim_aux
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
    (fuel: nat)
  : Tot (list edge) (decreases fuel)
  = if fuel = 0 then tree_edges
    else if all_in_tree in_tree n then tree_edges
    else
      match pure_prim_step adj n in_tree tree_edges with
      | None -> tree_edges  // No more edges (disconnected graph)
      | Some e -> 
        // Add edge to tree and mark destination as in tree
        let in_tree' = add_to_tree in_tree e.v in
        pure_prim_aux adj n in_tree' (e :: tree_edges) (fuel - 1)

// Main Prim's algorithm
let pure_prim (adj: adj_matrix) (n: nat) (start: nat) : list edge =
  if n = 0 || start >= n then []
  else
    let in_tree = create n false in
    let in_tree = upd in_tree start true in
    pure_prim_aux adj n in_tree [] n

// tree_edges is subset of result
#push-options "--z3rlimit 30"
let rec lemma_prim_aux_extends (adj: adj_matrix) (n: nat) (its: vertex_set)
    (tree_edges: list edge) (fuel: nat)
  : Lemma (ensures subset_edges tree_edges (pure_prim_aux adj n its tree_edges fuel))
          (decreases fuel)
  = if fuel = 0 then subset_edges_reflexive tree_edges
    else if all_in_tree its n then subset_edges_reflexive tree_edges
    else match pure_prim_step adj n its tree_edges with
      | None -> subset_edges_reflexive tree_edges
      | Some e ->
        let its' = add_to_tree its e.v in
        let result = pure_prim_aux adj n its' (e :: tree_edges) (fuel - 1) in
        lemma_prim_aux_extends adj n its' (e :: tree_edges) (fuel - 1);
        assert (subset_edges (e :: tree_edges) result);
        subset_edges_reflexive tree_edges;
        subset_edges_cons tree_edges e tree_edges;
        assert (subset_edges tree_edges (e :: tree_edges));
        subset_edges_transitive tree_edges (e :: tree_edges) result
#pop-options

(*** Correctness Properties ***)

// Edge returned by pure_prim_step crosses the cut
let lemma_prim_step_crosses_cut
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
    (e: edge)
  : Lemma (requires Some e == pure_prim_step adj n in_tree tree_edges /\
                    well_formed_adj adj n /\
                    length in_tree = n)
          (ensures crosses_cut e (vertex_set_to_cut in_tree))
  = lemma_find_min_aux_valid adj n in_tree 0 None

// Edge returned by pure_prim_step has valid vertex indices
let lemma_prim_step_bounds
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
    (e: edge)
  : Lemma (requires Some e == pure_prim_step adj n in_tree tree_edges /\
                    well_formed_adj adj n /\
                    length in_tree = n)
          (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
  = lemma_find_min_aux_valid adj n in_tree 0 None

// Edge returned by pure_prim_step is light (minimum weight)
let lemma_prim_step_is_light
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
    (e: edge)
  : Lemma (requires Some e == pure_prim_step adj n in_tree tree_edges /\
                    well_formed_adj adj n /\
                    length in_tree = n)
          (ensures is_light_edge e (vertex_set_to_cut in_tree) (adj_to_graph adj n))
  = let s = vertex_set_to_cut in_tree in
    let g = adj_to_graph adj n in
    // e is valid crossing with correct weight
    lemma_find_min_aux_valid adj n in_tree 0 None;
    assert (valid_crossing_with_weight adj n e in_tree);
    assert (e.w = edge_weight adj e.u e.v);
    // e is in adj_to_edges (since e.w matches)
    lemma_has_edge_in_adj adj n e.u e.v;
    assert (mem_edge ({u=e.u;v=e.v;w=edge_weight adj e.u e.v}) g.edges);
    assert (mem_edge e g.edges);
    // minimality
    lemma_find_min_aux_min adj n in_tree 0 None;
    introduce forall (e': edge). mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    with introduce _ ==> _ with _h. begin
      lemma_adj_extract adj n e';
      if s e'.u then ()
      else begin
        assert (has_edge adj n e'.v e'.u);
        assert (e.w <= edge_weight adj e'.v e'.u);
        assert (edge_weight adj e'.v e'.u = edge_weight adj e'.u e'.v);
        ()
      end
    end

// The cut (tree, non-tree) respects current tree edges
let rec lemma_cut_respects_tree_edges
    (tree_edges: list edge)
    (in_tree_set: vertex_set)
    (n: nat)
  : Lemma (requires length in_tree_set = n /\
                    // All edges in tree_edges connect tree vertices
                    (forall (e: edge). mem_edge e tree_edges ==> 
                      in_tree in_tree_set e.u /\ in_tree in_tree_set e.v))
          (ensures respects tree_edges (vertex_set_to_cut in_tree_set))
  = match tree_edges with
    | [] -> ()
    | e :: rest -> 
      // e connects two tree vertices, so doesn't cross cut
      assert (not (crosses_cut e (vertex_set_to_cut in_tree_set)));
      lemma_cut_respects_tree_edges rest in_tree_set n

// Count edges in result
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec lemma_prim_aux_edge_count
    (adj: adj_matrix)
    (n: nat)
    (in_tree: vertex_set)
    (tree_edges: list edge)
    (fuel: nat)
    (initial_count: nat)
  : Lemma (requires length in_tree = n /\
                    List.Tot.length tree_edges = initial_count /\
                    count_tree_vertices in_tree <= n)
          (ensures List.Tot.length (pure_prim_aux adj n in_tree tree_edges fuel) >= initial_count)
          (decreases fuel)
  = if fuel = 0 then ()
    else if all_in_tree in_tree n then ()
    else
      match pure_prim_step adj n in_tree tree_edges with
      | None -> ()
      | Some e -> 
        let in_tree' = add_to_tree in_tree e.v in
        assert (List.Tot.length (e :: tree_edges) = initial_count + 1);
        lemma_add_to_tree_preserves_length in_tree e.v;
        assert (length in_tree' = n);
        lemma_count_le in_tree';
        assert (count_tree_vertices in_tree' <= n);
        lemma_prim_aux_edge_count adj n in_tree' (e :: tree_edges) (fuel - 1) (initial_count + 1)
#pop-options

// Main correctness: result has n-1 edges AND connects all vertices
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_prim_aux_count_and_conn
    (adj: adj_matrix) (n: nat) (its: vertex_set) (tree_edges: list edge) (fuel: nat) (start: nat)
  : Lemma (requires well_formed_adj adj n /\ length its = n /\ n > 0 /\
                    all_connected n (adj_to_edges adj n) /\
                    fuel >= n - count_tree_vertices its /\
                    count_tree_vertices its > 0 /\ count_tree_vertices its <= n /\
                    List.Tot.length tree_edges = count_tree_vertices its - 1 /\
                    start < n /\ index its start = true /\
                    tree_connected start its tree_edges /\
                    (exists (u: nat). u < n /\ index its u = true))
          (ensures (let result = pure_prim_aux adj n its tree_edges fuel in
                    List.Tot.length result = n - 1 /\
                    all_connected n result))
          (decreases fuel)
  = if fuel = 0 then begin
      assert (count_tree_vertices its = n);
      assert (all_in_tree its n);
      lemma_all_in_tree_means_all_true its 0;
      assert (index its 0 = true);
      assert (reachable tree_edges start 0);
      reachable_symmetric tree_edges start 0;
      introduce forall (v: nat). v < n ==> reachable tree_edges 0 v
      with introduce _ ==> _ with _h. begin
        assert (index its v = true);
        assert (reachable tree_edges start v);
        reachable_transitive tree_edges 0 start v
      end
    end
    else if all_in_tree its n then begin
      // fuel > 0 but all in tree: same as fuel = 0 case
      lemma_all_in_tree_means_all_true its 0;
      assert (index its 0 = true);
      reachable_symmetric tree_edges start 0;
      introduce forall (v: nat). v < n ==> reachable tree_edges 0 v
      with introduce _ ==> _ with _h. begin
        assert (index its v = true);
        reachable_transitive tree_edges 0 start v
      end
    end
    else begin
      lemma_count_le its;
      lemma_count_lt_has_false its 0;
      lemma_connected_implies_crossing_edge adj n its;
      lemma_has_crossing_implies_some adj n its tree_edges;
      let Some e = pure_prim_step adj n its tree_edges in
      lemma_find_min_aux_valid adj n its 0 None;
      let its' = add_to_tree its e.v in
      lemma_count_add_new its e.v 0;
      lemma_add_to_tree_preserves_length its e.v;
      Seq.lemma_index_upd2 its e.v true start;
      lemma_tree_connected_extend start its tree_edges e;
      lemma_prim_aux_count_and_conn adj n its' (e :: tree_edges) (fuel - 1) start
    end
#pop-options

// Wrapper: result has n-1 edges
let lemma_prim_has_n_minus_1_edges
    (adj: adj_matrix)
    (n: nat)
    (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ 
                    well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures List.Tot.length (pure_prim adj n start) = n - 1)
  = let in_tree = upd (create n false) start true in
    lemma_count_single_true n start 0;
    Seq.lemma_index_upd1 (create n false) start true;
    // tree_connected start in_tree []: start is reachable from start via empty path
    assert (is_path_from_to ([] #edge) start start);
    assert (subset_edges ([] #edge) ([] #edge));
    assert (reachable ([] #edge) start start);
    assert (tree_connected start in_tree ([] #edge));
    lemma_prim_aux_count_and_conn adj n in_tree [] n start

// Wrapper: result connects all vertices
let lemma_prim_all_connected
    (adj: adj_matrix)
    (n: nat)
    (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ 
                    well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures all_connected n (pure_prim adj n start))
  = let in_tree = upd (create n false) start true in
    lemma_count_single_true n start 0;
    Seq.lemma_index_upd1 (create n false) start true;
    assert (is_path_from_to ([] #edge) start start);
    assert (subset_edges ([] #edge) ([] #edge));
    assert (reachable ([] #edge) start start);
    assert (tree_connected start in_tree ([] #edge));
    lemma_prim_aux_count_and_conn adj n in_tree [] n start

(*** Safe Edge Property: Each Step Adds Safe Edge ***)

// Invariant: tree_edges is subset of some MST
let prim_invariant 
    (g: graph)
    (tree_edges: list edge)
  : prop
  = exists (t: list edge). is_mst g tree_edges /\ subset_edges tree_edges t

// Single step preserves safety
let lemma_prim_step_preserves_safety
    (adj: adj_matrix)
    (n: nat)
    (in_tree_set: vertex_set)
    (tree_edges: list edge)
    (e: edge)
  : Lemma (requires well_formed_adj adj n /\
                    length in_tree_set = n /\
                    Some e == pure_prim_step adj n in_tree_set tree_edges /\
                    // Current tree_edges is subset of some MST
                    (exists (t: list edge). 
                      is_mst (adj_to_graph adj n) t /\ 
                      subset_edges tree_edges t) /\
                    // All edges in tree_edges connect tree vertices
                    (forall (e': edge). mem_edge e' tree_edges ==>
                      in_tree in_tree_set e'.u /\ in_tree in_tree_set e'.v))
          (ensures // e :: tree_edges is subset of some MST
                   (exists (t: list edge). 
                     is_mst (adj_to_graph adj n) t /\
                     subset_edges (e :: tree_edges) t))
  = let g = adj_to_graph adj n in
    let s = vertex_set_to_cut in_tree_set in
    
    // Prove preconditions for cut_property
    lemma_prim_step_crosses_cut adj n in_tree_set tree_edges e;
    assert (crosses_cut e s);
    
    lemma_prim_step_bounds adj n in_tree_set tree_edges e;
    assert (e.u < g.n /\ e.v < g.n);
    
    lemma_prim_step_is_light adj n in_tree_set tree_edges e;
    assert (is_light_edge e s g);
    
    lemma_cut_respects_tree_edges tree_edges in_tree_set n;
    assert (respects tree_edges s);
    
    // All edges in adj_to_graph have valid endpoints
    introduce forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n
    with introduce _ ==> _ with _. adj_to_graph_edges_valid adj n e';
    
    // Apply cut property (CLRS Corollary 23.2)
    cut_property g tree_edges e s;
    
    // Conclusion: e :: tree_edges ⊆ some MST
    ()

(*** Inductive Correctness: Entire Algorithm ***)

// Prove by induction that pure_prim_aux maintains invariant
let rec lemma_prim_aux_safety
    (adj: adj_matrix)
    (n: nat)
    (in_tree_set: vertex_set)
    (tree_edges: list edge)
    (fuel: nat)
  : Lemma (requires well_formed_adj adj n /\
                    length in_tree_set = n /\
                    // Invariant: tree_edges ⊆ some MST
                    (exists (t: list edge). 
                      is_mst (adj_to_graph adj n) t /\
                      subset_edges tree_edges t) /\
                    // All edges in tree_edges connect tree vertices
                    (forall (e: edge). mem_edge e tree_edges ==>
                      in_tree in_tree_set e.u /\ in_tree in_tree_set e.v))
          (ensures // Result is subset of some MST
                   (exists (t: list edge).
                     is_mst (adj_to_graph adj n) t /\
                     subset_edges (pure_prim_aux adj n in_tree_set tree_edges fuel) t))
          (decreases fuel)
  = if fuel = 0 then ()
    else if all_in_tree in_tree_set n then ()
    else
      match pure_prim_step adj n in_tree_set tree_edges with
      | None -> ()
      | Some e ->
        // Apply step lemma
        lemma_prim_step_preserves_safety adj n in_tree_set tree_edges e;
        
        // Recurse with e :: tree_edges
        let in_tree' = add_to_tree in_tree_set e.v in
        
        // Show: all edges in (e :: tree_edges) connect tree' vertices
        // e crosses the cut: e.u in tree, e.v not
        lemma_find_min_aux_valid adj n in_tree_set 0 None;
        assert (valid_crossing_with_weight adj n e in_tree_set);
        assert (valid_crossing_edge e in_tree_set);
        // e.u <> e.v
        assert (e.u <> e.v);
        // e.u stays in tree' (preservation), e.v is added
        lemma_add_to_tree_preserves in_tree_set e.v e.u;
        lemma_add_to_tree_adds in_tree_set e.v;
        lemma_add_to_tree_preserves_length in_tree_set e.v;
        // For edges in tree_edges: endpoints are in in_tree_set, 
        // thus != e.v (which is not in in_tree_set), so preserved
        introduce forall (e': edge). mem_edge e' (e :: tree_edges) ==>
          in_tree in_tree' e'.u /\ in_tree in_tree' e'.v
        with introduce _ ==> _ with _h. begin
          if edge_eq e' e then begin
            if e'.u = e.u && e'.v = e.v then ()
            else begin
              assert (e'.u = e.v /\ e'.v = e.u);
              lemma_add_to_tree_adds in_tree_set e.v;
              lemma_add_to_tree_preserves in_tree_set e.v e.u
            end
          end else begin
            assert (mem_edge e' tree_edges);
            assert (in_tree in_tree_set e'.u /\ in_tree in_tree_set e'.v);
            assert (e'.u <> e.v);
            assert (e'.v <> e.v);
            lemma_add_to_tree_preserves in_tree_set e.v e'.u;
            lemma_add_to_tree_preserves in_tree_set e.v e'.v
          end
        end;
        
        assert (fuel > 0);
        lemma_prim_aux_safety adj n in_tree' (e :: tree_edges) (fuel - 1)

// Main correctness theorem: result is subset of some MST
let lemma_prim_result_is_safe
    (adj: adj_matrix)
    (n: nat)
    (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    // Graph has an MST (follows from connectivity, assumed here)
                    (exists (t: list edge). is_mst (adj_to_graph adj n) t))
          (ensures (exists (t: list edge).
                     is_mst (adj_to_graph adj n) t /\
                     subset_edges (pure_prim adj n start) t))
  = if n = 0 || start >= n then ()
    else begin
      let in_tree = upd (create n false) start true in
      
      // Base case: empty tree_edges is subset of any MST
      // subset_edges [] t = true for any t, so:
      // We need: exists t. is_mst g t /\ subset_edges [] t
      // From precondition, exists t. is_mst g t. And subset_edges [] t = true.
      // So the invariant holds initially.
      
      // Apply induction
      lemma_prim_aux_safety adj n in_tree [] n
    end

(*** Final Specification ***)

//SNIPPET_START: prim_spec
// Specification: Prim's algorithm produces an MST
let prim_spec 
    (adj: adj_matrix)
    (n: nat)
    (start: nat)
  : Pure (list edge)
    (requires n > 0 /\ start < n /\ 
              well_formed_adj adj n /\
              // Graph is connected
              all_connected n (adj_to_edges adj n) /\
              // Graph has an MST (implied by connectivity)
              (exists (t: list edge). is_mst (adj_to_graph adj n) t))
    (ensures fun result ->
      let g = adj_to_graph adj n in
      // Result has n-1 edges
      List.Tot.length result = n - 1 /\
      // Result is subset of some MST (hence has minimum weight)
      (exists (t: list edge). 
        is_mst g t /\ 
        subset_edges result t) /\
      // Result connects all vertices
      all_connected n result)
//SNIPPET_END: prim_spec
  = let result = pure_prim adj n start in
    lemma_prim_has_n_minus_1_edges adj n start;
    lemma_prim_result_is_safe adj n start;
    lemma_prim_all_connected adj n start;
    result

(*** Summary of Proof Strategy ***)

(*
  The correctness of Prim's algorithm follows from:
  
  1. **Safe-Edge Property** (CLRS Corollary 23.2):
     - At each step, the algorithm maintains a tree T ⊆ some MST
     - The cut S = (tree vertices, non-tree vertices) respects T
     - pure_prim_step finds minimum-weight edge crossing this cut
     - By MST.Spec.cut_property, this edge is safe to add
     - Proved in: lemma_prim_step_preserves_safety
  
  2. **Edge Count + Connectivity** (proved jointly):
     - Algorithm starts with 1 vertex, adds 1 edge per iteration
     - Connected graph ensures find_min always returns Some
     - tree_connected invariant: every tree vertex reachable from start
     - Result has exactly n-1 edges and connects all vertices
     - Proved in: lemma_prim_aux_count_and_conn
  
  3. **Minimum Weight**:
     - By induction using safe-edge property
     - Result is subset of an MST, hence has minimum weight
     - Proved in: lemma_prim_result_is_safe
  
  Remaining admits in MST.Spec (from AGENT4):
  - exchange_is_spanning_tree: standard graph theory exchange lemma
  This is used by cut_property, which is used by our proofs.
  
  Precondition note: prim_spec requires MST existence as precondition.
  This follows from graph connectivity (every connected graph has a
  spanning tree), but the proof requires substantial graph theory
  infrastructure beyond the scope of this module.
*)

(*** pure_prim_is_mst ***)
module Bridge = CLRS.Ch23.Kruskal.Bridge
module Existence = CLRS.Ch23.MST.Existence

/// All endpoints of tree_edges are in in_tree (invariant of pure_prim_aux)
let rec lemma_prim_aux_endpoints_in_tree
    (adj: adj_matrix) (n: nat) (its: vertex_set) (tree_edges: list edge) (fuel: nat) (e: edge)
  : Lemma
    (requires well_formed_adj adj n /\ length its = n /\
              (forall (e': edge). mem_edge e' tree_edges ==>
                e'.u < n /\ e'.v < n /\ index its e'.u = true /\ index its e'.v = true) /\
              mem_edge e (pure_prim_aux adj n its tree_edges fuel))
    (ensures e.u < n /\ e.v < n)
    (decreases fuel)
  = if fuel = 0 then ()
    else if all_in_tree its n then ()
    else match pure_prim_step adj n its tree_edges with
    | None -> ()
    | Some step_e ->
      lemma_prim_step_bounds adj n its tree_edges step_e;
      lemma_find_min_aux_valid adj n its 0 None;
      // Now we know: valid_crossing_with_weight adj n step_e its
      // Which gives: step_e.u < length its, index its step_e.u = true,
      //              step_e.v < length its, index its step_e.v = false
      assert (valid_crossing_edge step_e its);
      let its' = add_to_tree its step_e.v in
      lemma_add_to_tree_preserves_length its step_e.v;
      if mem_edge e tree_edges then ()
      else if edge_eq e step_e then
        edge_eq_endpoints e step_e
      else begin
        // e is in pure_prim_aux ... (step_e :: tree_edges) (fuel-1)
        // Need: all endpoints of (step_e :: tree_edges) are in its'
        let aux (e': edge) : Lemma
          (requires mem_edge e' (step_e :: tree_edges))
          (ensures e'.u < n /\ e'.v < n /\ index its' e'.u = true /\ index its' e'.v = true)
          = if edge_eq e' step_e then begin
              edge_eq_endpoints e' step_e;
              // Either (e'.u=step_e.u, e'.v=step_e.v) or (e'.u=step_e.v, e'.v=step_e.u)
              // step_e.u ∈ its, step_e.v added to its'
              // Case 1: e'.u=step_e.u (in its→in its'), e'.v=step_e.v (added to its')
              // Case 2: e'.u=step_e.v (added to its'), e'.v=step_e.u (in its→in its')
              lemma_add_to_tree_adds its step_e.v;
              assert (in_tree its step_e.u);
              lemma_add_to_tree_preserves its step_e.v step_e.u
            end
            else begin
              assert (mem_edge e' tree_edges);
              lemma_add_to_tree_preserves its step_e.v e'.u;
              lemma_add_to_tree_preserves its step_e.v e'.v
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        lemma_prim_aux_endpoints_in_tree adj n its' (step_e :: tree_edges) (fuel - 1) e
      end

/// noRepeats for pure_prim_aux: each new edge's v is fresh (not in tree yet)
#push-options "--z3rlimit 50"
let rec lemma_prim_aux_noRepeats
    (adj: adj_matrix) (n: nat) (its: vertex_set) (tree_edges: list edge) (fuel: nat)
  : Lemma
    (requires well_formed_adj adj n /\ length its = n /\
              Bridge.noRepeats_edge tree_edges /\
              (forall (e': edge). mem_edge e' tree_edges ==>
                e'.u < n /\ e'.v < n /\ index its e'.u = true /\ index its e'.v = true))
    (ensures Bridge.noRepeats_edge (pure_prim_aux adj n its tree_edges fuel))
    (decreases fuel)
  = if fuel = 0 then ()
    else if all_in_tree its n then ()
    else match pure_prim_step adj n its tree_edges with
    | None -> ()
    | Some step_e ->
      lemma_prim_step_bounds adj n its tree_edges step_e;
      lemma_find_min_aux_valid adj n its 0 None;
      assert (valid_crossing_edge step_e its);
      // step_e.v ∉ its (not in tree). All tree_edges endpoints ∈ its.
      // So for any e' ∈ tree_edges: e'.v ∈ its, so e'.v ≠ step_e.v.
      // Also e'.u ∈ its, so e'.u ≠ step_e.v (since step_e.v ∉ its).
      // For edge_eq step_e e': need {step_e.u, step_e.v} = {e'.u, e'.v} and same w.
      // step_e.v ∉ its, but e'.u ∈ its and e'.v ∈ its.
      // If step_e.v = e'.u: step_e.v ∈ its — contradiction.
      // If step_e.v = e'.v: step_e.v ∈ its — contradiction.
      // So step_e.v ≠ e'.u and step_e.v ≠ e'.v.
      // But edge_eq needs step_e.v ∈ {e'.u, e'.v}. Contradiction.
      // So ¬(edge_eq step_e e'). Hence ¬(mem_edge step_e tree_edges).
      let aux_not_mem (e': edge) : Lemma
        (requires mem_edge e' tree_edges /\ edge_eq step_e e')
        (ensures False)
        = edge_eq_endpoints step_e e'
          // step_e.v = e'.v or step_e.v = e'.u
          // Both e'.u and e'.v are in its. step_e.v not in its. Contradiction.
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_not_mem);
      assert (~(mem_edge step_e tree_edges));
      assert (Bridge.noRepeats_edge (step_e :: tree_edges));
      // Establish endpoints invariant for step_e :: tree_edges in its'
      let its' = add_to_tree its step_e.v in
      lemma_add_to_tree_preserves_length its step_e.v;
      lemma_add_to_tree_adds its step_e.v;
      let aux2 (e': edge) : Lemma
        (requires mem_edge e' (step_e :: tree_edges))
        (ensures e'.u < n /\ e'.v < n /\ index its' e'.u = true /\ index its' e'.v = true)
        = if edge_eq e' step_e then begin
            edge_eq_endpoints e' step_e;
            lemma_add_to_tree_adds its step_e.v;
            lemma_add_to_tree_preserves its step_e.v step_e.u
          end else begin
            lemma_add_to_tree_preserves its step_e.v e'.u;
            lemma_add_to_tree_preserves its step_e.v e'.v
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
      lemma_prim_aux_noRepeats adj n its' (step_e :: tree_edges) (fuel - 1)
#pop-options

/// noRepeats for pure_prim
let lemma_pure_prim_noRepeats (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n)
          (ensures Bridge.noRepeats_edge (pure_prim adj n start))
  = let its = upd (create n false) start true in
    lemma_prim_aux_noRepeats adj n its [] n

let pure_prim_is_mst (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\
                    well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n) /\
                    (forall (e: edge). mem_edge e (adj_to_graph adj n).edges ==>
                      e.u < n /\ e.v < n /\ e.u <> e.v))
          (ensures is_mst (adj_to_graph adj n) (pure_prim adj n start))
  = let g = adj_to_graph adj n in
    Existence.mst_exists g;
    lemma_prim_has_n_minus_1_edges adj n start;
    lemma_prim_all_connected adj n start;
    lemma_prim_result_is_safe adj n start;
    let result = pure_prim adj n start in
    // Derive is_spanning_tree from safety
    FStar.Classical.exists_elim (is_mst g result)
      #(list edge) #(fun t -> is_mst g t /\ subset_edges result t) ()
      (fun (t: list edge{is_mst g t /\ subset_edges result t}) ->
        // subset_edges result g.edges (via transitivity through t)
        subset_edges_transitive result t g.edges;
        // acyclic n result (subset of acyclic t)
        introduce forall (v2: nat) (cycle: list edge).
          v2 < n /\ subset_edges cycle result /\ Cons? cycle /\ all_edges_distinct cycle ==>
          ~(is_path_from_to cycle v2 v2)
        with introduce _ ==> _ with _. (
          subset_edges_transitive cycle result t
        );
        // Now: is_spanning_tree g result
        // noRepeats: proven by lemma_pure_prim_noRepeats
        lemma_pure_prim_noRepeats adj n start;
        assert (exists (t2: list edge). is_mst g t2 /\ subset_edges result t2);
        Bridge.safe_spanning_tree_is_mst g result
      )
