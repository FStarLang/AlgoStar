(*
   Union-Find Correctness for Kruskal's Algorithm
   Key theorem: find(u) ≠ find(v) ⟹ ¬(reachable edges u v)
*)
module CLRS.Ch23.Kruskal.UF

open FStar.List.Tot
open FStar.Seq
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.MST.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

let valid_parents (sparent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) < n)

let rec find_pure (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Tot nat (decreases steps)
  = if steps = 0 || v >= n || Seq.length sparent <> n then v
    else find_pure sparent (SZ.v (Seq.index sparent v)) (steps - 1) n

let rec find_pure_bounded (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n)
          (ensures find_pure sparent v steps n < n)
          (decreases steps)
  = if steps = 0 then ()
    else find_pure_bounded sparent (SZ.v (Seq.index sparent v)) (steps - 1) n

let rec find_pure_fixed (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n /\ SZ.v (Seq.index sparent v) = v)
          (ensures find_pure sparent v steps n = v)
          (decreases steps)
  = if steps = 0 then ()
    else find_pure_fixed sparent v (steps - 1) n

let rec find_pure_split (sparent: Seq.seq SZ.t) (v: nat) (k1 k2: nat) (n: nat)
  : Lemma (requires valid_parents sparent n /\ v < n)
          (ensures find_pure sparent v (k1 + k2) n =
                   find_pure sparent (find_pure sparent v k1 n) k2 n)
          (decreases k1)
  = if k1 = 0 then ()
    else begin
      find_pure_bounded sparent (SZ.v (Seq.index sparent v)) (k1 - 1) n;
      find_pure_split sparent (SZ.v (Seq.index sparent v)) (k1 - 1) k2 n
    end

// UF invariant: relates parent array to edge-list connectivity
let uf_inv (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat) : prop =
  valid_parents sparent n /\ ec < n /\
  (forall (v: nat). v < n ==> find_pure sparent v n n < n) /\
  (forall (v: nat). v < n ==>
    SZ.v (Seq.index sparent (find_pure sparent v n n)) = find_pure sparent v n n) /\
  (forall (v: nat). v < n ==> find_pure sparent v ec n = find_pure sparent v n n) /\
  (forall (u v: nat). u < n /\ v < n /\ reachable edges u v ==>
    find_pure sparent u n n = find_pure sparent v n n)

let uf_inv_unreachable (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u v: nat)
  : Lemma (requires uf_inv sparent edges n ec /\ u < n /\ v < n /\
                    find_pure sparent u n n <> find_pure sparent v n n)
          (ensures ~(reachable edges u v))
  = ()

let identity_parent (n: nat) (sparent: Seq.seq SZ.t) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) = i)

let rec find_pure_identity (sparent: Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires identity_parent n sparent /\ v < n)
          (ensures find_pure sparent v steps n = v)
          (decreases steps)
  = if steps = 0 then ()
    else find_pure_identity sparent v (steps - 1) n

let uf_inv_init (sparent: Seq.seq SZ.t) (n: nat)
  : Lemma (requires identity_parent n sparent /\ n > 0)
          (ensures uf_inv sparent [] n 0)
  = let aux (v: nat) : Lemma (requires v < n)
        (ensures find_pure sparent v n n = v /\
                 find_pure sparent v n n < n /\
                 SZ.v (Seq.index sparent (find_pure sparent v n n)) = find_pure sparent v n n /\
                 find_pure sparent v 0 n = find_pure sparent v n n) =
      find_pure_identity sparent v n n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// Path induction: if comp equates edge endpoints, it equates reachable vertices
let rec comp_along_path (comp: nat -> nat) (path: list edge) (es: list edge) (a b: nat)
  : Lemma (requires
             is_path_from_to path a b /\ subset_edges path es /\
             (forall (e: edge). mem_edge e es ==> comp e.u = comp e.v))
          (ensures comp a = comp b)
          (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      if e.u = a then comp_along_path comp rest es e.v b
      else comp_along_path comp rest es e.u b

let comp_reachable (comp: nat -> nat) (es: list edge) (a b: nat)
  : Lemma (requires reachable es a b /\
                    (forall (e: edge). mem_edge e es ==> comp e.u = comp e.v))
          (ensures comp a = comp b)
  = let aux (path: list edge)
      : Lemma (requires subset_edges path es /\ is_path_from_to path a b)
              (ensures comp a = comp b)
      = comp_along_path comp path es a b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let mem_edge_reachable (e: edge) (edges: list edge)
  : Lemma (requires mem_edge e edges)
          (ensures reachable edges e.u e.v)
  = edge_eq_reflexive e;
    assert (is_path_from_to [e] e.u e.v);
    assert (subset_edges [e] edges)

// All edges have endpoints within [0, n)
let all_edges_valid (edges: list edge) (n: nat) : prop =
  forall (e: edge). mem_edge e edges ==> e.u < n /\ e.v < n

// If find_pure sparent v steps n != root_u, then changing only parent[root_u]
// doesn't affect the find result (the path never visits root_u).
let rec find_pure_unchanged
    (sparent sparent': Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
    (root_u: nat)
  : Lemma
    (requires
      valid_parents sparent n /\ valid_parents sparent' n /\
      root_u < n /\ SZ.v (Seq.index sparent root_u) = root_u /\
      (forall (i: nat). i < n /\ i <> root_u ==>
        Seq.index sparent' i == Seq.index sparent i) /\
      v < n /\ find_pure sparent v steps n <> root_u)
    (ensures find_pure sparent' v steps n = find_pure sparent v steps n)
    (decreases steps)
  = if steps = 0 then ()
    else begin
      if v = root_u then begin
        // Contradiction: find_pure from a fixed point returns root_u
        find_pure_fixed sparent root_u (steps - 1) n
      end else begin
        let pv = SZ.v (Seq.index sparent v) in
        // parent'[v] = parent[v] since v <> root_u
        // find_pure sparent pv (steps-1) n = find_pure sparent v steps n <> root_u
        find_pure_unchanged sparent sparent' pv (steps - 1) n root_u
      end
    end

// If find_pure sparent v steps n = root_u, then in sparent' (where
// parent'[root_u] = root_v), one additional step routes to root_v.
let rec find_pure_rerouted
    (sparent sparent': Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
    (root_u root_v: nat)
  : Lemma
    (requires
      valid_parents sparent n /\ valid_parents sparent' n /\
      root_u < n /\ root_v < n /\ root_u <> root_v /\
      SZ.v (Seq.index sparent root_u) = root_u /\
      SZ.v (Seq.index sparent' root_u) = root_v /\
      SZ.v (Seq.index sparent root_v) = root_v /\
      SZ.v (Seq.index sparent' root_v) = root_v /\
      (forall (i: nat). i < n /\ i <> root_u ==>
        Seq.index sparent' i == Seq.index sparent i) /\
      v < n /\ find_pure sparent v steps n = root_u)
    (ensures find_pure sparent' v (steps + 1) n = root_v)
    (decreases steps)
  = if steps = 0 then ()
    else if v = root_u then
      find_pure_fixed sparent' root_v steps n
    else begin
      let pv = SZ.v (Seq.index sparent v) in
      find_pure_rerouted sparent sparent' pv (steps - 1) n root_u root_v
    end

// Key theorem: union maintains the UF invariant
// After adding edge (u_val, v_val) and setting parent[root_u] := root_v
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let uf_inv_union
    (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u_val v_val: nat) (root_u root_v: nat) (new_edge: edge)
  : Lemma (requires uf_inv sparent edges n ec /\
                    u_val < n /\ v_val < n /\
                    root_u = find_pure sparent u_val n n /\
                    root_v = find_pure sparent v_val n n /\
                    root_u <> root_v /\
                    valid_parents sparent' n /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    new_edge.u = u_val /\ new_edge.v = v_val /\
                    ec + 1 < n /\
                    all_edges_valid edges n)
          (ensures uf_inv sparent' (new_edge :: edges) n (ec + 1))
  = find_pure_bounded sparent u_val n n;
    find_pure_bounded sparent v_val n n;
    // Establish routing: find_pure sparent' v n n for each v
    let route (v: nat) : Lemma (requires v < n)
      (ensures find_pure sparent' v n n =
               (if find_pure sparent v n n = root_u then root_v
                else find_pure sparent v n n) /\
               find_pure sparent' v n n < n) =
      if find_pure sparent v n n = root_u then begin
        find_pure_rerouted sparent sparent' v ec n root_u root_v;
        find_pure_split sparent' v (ec + 1) (n - ec - 1) n;
        find_pure_fixed sparent' root_v (n - ec - 1) n
      end else begin
        find_pure_unchanged sparent sparent' v n n root_u;
        find_pure_bounded sparent v n n
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires route);
    // ec+1 steps suffice for all v
    let stp (v: nat) : Lemma (requires v < n)
      (ensures find_pure sparent' v (ec + 1) n = find_pure sparent' v n n) =
      route v;
      if find_pure sparent v n n = root_u then
        find_pure_rerouted sparent sparent' v ec n root_u root_v
      else begin
        find_pure_unchanged sparent sparent' v ec n root_u;
        find_pure_split sparent' v ec 1 n;
        find_pure_fixed sparent' (find_pure sparent v n n) 1 n
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires stp);
    // Completeness: comp_reachable
    let comp (x: nat) : nat =
      if x < n then find_pure sparent' x n n else x in
    route u_val; route v_val;
    let ecomp (e: edge) : Lemma
      (requires mem_edge e (new_edge :: edges))
      (ensures comp e.u = comp e.v) =
      if edge_eq e new_edge then ()
      else begin
        mem_edge_reachable e edges;
        route e.u; route e.v
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ecomp);
    let full (u v: nat) : Lemma
      (requires u < n /\ v < n /\ reachable (new_edge :: edges) u v)
      (ensures find_pure sparent' u n n = find_pure sparent' v n n) =
      comp_reachable comp (new_edge :: edges) u v
    in
    let wrap (u: nat) : Lemma (requires u < n)
      (ensures forall (v: nat). v < n /\ reachable (new_edge :: edges) u v ==>
                 find_pure sparent' u n n = find_pure sparent' v n n) =
      FStar.Classical.forall_intro (FStar.Classical.move_requires (full u))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires wrap)
    // Z3 derives remaining uf_inv conjuncts (root fixed points, etc.) 
    // from routing + old uf_inv + parent' properties
#pop-options

let not_mem_when_unreachable (e: edge) (edges: list edge)
  : Lemma (requires ~(reachable edges e.u e.v))
          (ensures ~(mem_edge e edges))
  = let aux () : Lemma (requires mem_edge e edges) (ensures False) =
      mem_edge_reachable e edges
    in
    FStar.Classical.move_requires aux ()

// mem_edge is order-independent: (e :: t) vs (t @ [e])
let rec mem_edge_cons_iff_append (x e: edge) (t: list edge)
  : Lemma (ensures mem_edge x (e :: t) = mem_edge x (t @ [e]))
  = match t with
    | [] -> ()
    | hd :: tl -> mem_edge_cons_iff_append x e tl

let rec subset_edges_cons_iff_append (cycle: list edge) (e: edge) (t: list edge)
  : Lemma (requires subset_edges cycle (t @ [e]))
          (ensures subset_edges cycle (e :: t))
  = match cycle with
    | [] -> ()
    | x :: rest ->
      mem_edge_cons_iff_append x e t;
      subset_edges_cons_iff_append rest e t

// acyclic is permutation-invariant for cons vs append
let acyclic_cons_to_append (n: nat) (e: edge) (t: list edge)
  : Lemma (requires acyclic n (e :: t))
          (ensures acyclic n (t @ [e]))
  = let aux (cycle: list edge)
      : Lemma (requires subset_edges cycle (t @ [e]))
              (ensures subset_edges cycle (e :: t))
      = subset_edges_cons_iff_append cycle e t
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// uf_inv is permutation-invariant (cons vs append)
// Uses comp_reachable to avoid existential reasoning about reachable
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let uf_inv_cons_to_append (sparent: Seq.seq SZ.t) (e: edge) (t: list edge) (n ec: nat)
  : Lemma (requires uf_inv sparent (e :: t) n ec /\ all_edges_valid (e :: t) n)
          (ensures uf_inv sparent (t @ [e]) n ec)
  = let comp (x: nat) : nat = if x < n then find_pure sparent x n n else x in
    // For each edge in (t@[e]), comp maps endpoints equally
    let ecomp (e': edge)
      : Lemma (requires mem_edge e' (t @ [e]))
              (ensures comp e'.u = comp e'.v) =
      mem_edge_cons_iff_append e' e t;
      mem_edge_reachable e' (e :: t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ecomp);
    // comp_reachable: reachable (t@[e]) u v ==> comp u = comp v
    let full (u v: nat)
      : Lemma (requires u < n /\ v < n /\ reachable (t @ [e]) u v)
              (ensures find_pure sparent u n n = find_pure sparent v n n) =
      comp_reachable comp (t @ [e]) u v
    in
    let wrap (u: nat) : Lemma (requires u < n)
      (ensures forall (v: nat). v < n /\ reachable (t @ [e]) u v ==>
                 find_pure sparent u n n = find_pure sparent v n n) =
      FStar.Classical.forall_intro (FStar.Classical.move_requires (full u))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires wrap)
    // Conjuncts 1-5 of uf_inv are edge-independent; Z3 derives from hypothesis
#pop-options

// Empty list is acyclic
let acyclic_empty (n: nat) : Lemma (acyclic n []) = ()

// find_pure agrees when parent values agree
let rec find_pure_eq (sparent sparent': Seq.seq SZ.t) (v: nat) (steps: nat) (n: nat)
  : Lemma (requires Seq.length sparent = n /\ Seq.length sparent' = n /\
                    (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) = SZ.v (Seq.index sparent' i)))
          (ensures find_pure sparent v steps n = find_pure sparent' v steps n)
          (decreases steps)
  = if steps = 0 || v >= n then ()
    else find_pure_eq sparent sparent' (SZ.v (Seq.index sparent v)) (steps - 1) n

// uf_inv preserved when parent values unchanged
let uf_inv_eq (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
  : Lemma (requires uf_inv sparent edges n ec /\ Seq.length sparent' = n /\
                    (forall (i: nat). i < n ==> SZ.v (Seq.index sparent' i) = SZ.v (Seq.index sparent i)))
          (ensures uf_inv sparent' edges n ec)
  = // Step 1: find_pure agrees on both parent arrays
    let eq_n (v: nat) : Lemma (requires v < n)
      (ensures find_pure sparent' v n n = find_pure sparent v n n) =
      find_pure_eq sparent sparent' v n n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires eq_n);
    let eq_ec (v: nat) : Lemma (requires v < n)
      (ensures find_pure sparent' v ec n = find_pure sparent v ec n) =
      find_pure_eq sparent sparent' v ec n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires eq_ec)
    // Step 2: Z3 derives uf_inv sparent' from uf_inv sparent and the equalities
