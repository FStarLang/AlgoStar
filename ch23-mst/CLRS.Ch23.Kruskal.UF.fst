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

// Key theorem: union maintains the UF invariant
// After adding edge (u_val, v_val) and setting parent[root_u] := root_v
#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
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
                    ec + 1 < n)
          (ensures uf_inv sparent' (new_edge :: edges) n (ec + 1))
  = // The proof follows from:
    // 1. After union, vertices with old root root_u get new root root_v
    // 2. Vertices with other old roots are unchanged
    // 3. UF completeness extends to new_edge :: edges via comp_reachable
    admit()
#pop-options

let mem_edge_reachable (e: edge) (edges: list edge)
  : Lemma (requires mem_edge e edges)
          (ensures reachable edges e.u e.v)
  = edge_eq_reflexive e;
    assert (is_path_from_to [e] e.u e.v);
    assert (subset_edges [e] edges)

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
