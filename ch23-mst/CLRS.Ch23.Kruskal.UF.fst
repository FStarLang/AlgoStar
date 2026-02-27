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

(*** Pure Find: follow parent pointers for `steps` steps ***)

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

let find_pure_reaches_root (sparent: Seq.seq SZ.t) (v: nat) (k: nat) (n: nat) (root: nat)
  : Lemma (requires valid_parents sparent n /\ v < n /\ root < n /\
                    SZ.v (Seq.index sparent root) = root /\
                    k <= n /\ find_pure sparent v k n = root)
          (ensures find_pure sparent v n n = root)
  = find_pure_bounded sparent v k n;
    find_pure_split sparent v k (n - k) n;
    find_pure_fixed sparent root (n - k) n

let find_pure_never_at_root (sparent: Seq.seq SZ.t) (v: nat) (k: nat) (n: nat) (root: nat)
  : Lemma (requires valid_parents sparent n /\ v < n /\ root < n /\
                    SZ.v (Seq.index sparent root) = root /\
                    k <= n /\ find_pure sparent v n n <> root)
          (ensures find_pure sparent v k n <> root)
  = if find_pure sparent v k n = root then
      find_pure_reaches_root sparent v k n root
    else ()

(*** UF Invariant ***)

let uf_inv (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat) : prop =
  valid_parents sparent n /\ ec < n /\
  // All find results are bounded and are fixed points (roots)
  (forall (v: nat). v < n ==> find_pure sparent v n n < n) /\
  (forall (v: nat). v < n ==>
    SZ.v (Seq.index sparent (find_pure sparent v n n)) = find_pure sparent v n n) /\
  // ec steps suffice to reach the root
  (forall (v: nat). v < n ==> find_pure sparent v ec n = find_pure sparent v n n) /\
  // UF completeness: connected vertices have the same root
  (forall (u v: nat). u < n /\ v < n /\ reachable edges u v ==>
    find_pure sparent u n n = find_pure sparent v n n)

let uf_inv_unreachable (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u v: nat)
  : Lemma (requires uf_inv sparent edges n ec /\ u < n /\ v < n /\
                    find_pure sparent u n n <> find_pure sparent v n n)
          (ensures ~(reachable edges u v))
  = ()

// All edges have valid endpoints
let all_edges_valid (edges: list edge) (n: nat) : prop =
  forall (e: edge). mem_edge e edges ==> e.u < n /\ e.v < n

(*** Initial State ***)

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

(*** Key Lemma 1: Path unchanged when root ≠ root_u ***)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec find_pure_unchanged
    (sparent sparent': Seq.seq SZ.t) (w: nat) (steps: nat) (n: nat) (root_u: nat)
  : Lemma (requires valid_parents sparent n /\ valid_parents sparent' n /\
                    w < n /\ root_u < n /\ steps <= n /\
                    SZ.v (Seq.index sparent root_u) = root_u /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    // w's root is a fixed point and differs from root_u
                    find_pure sparent w n n <> root_u /\
                    (let r = find_pure sparent w n n in
                     r < n /\ SZ.v (Seq.index sparent r) = r))
          (ensures find_pure sparent' w steps n = find_pure sparent w steps n)
          (decreases steps)
  = if steps = 0 then ()
    else begin
      find_pure_never_at_root sparent w 0 n root_u;
      let p = SZ.v (Seq.index sparent w) in
      // Show find_pure sparent p n n = find_pure sparent w n n
      // By definition: find_pure w n = find_pure p (n-1) [one step]
      // find_pure p n = find_pure (find_pure p (n-1)) 1 [split] = find_pure root 1 = root
      find_pure_bounded sparent p (n - 1) n;
      find_pure_split sparent p (n - 1) 1 n;
      let r = find_pure sparent w n n in
      find_pure_fixed sparent r 1 n;
      // Now find_pure sparent p n n = r = find_pure sparent w n n
      find_pure_unchanged sparent sparent' p (steps - 1) n root_u
    end
#pop-options

(*** Key Lemma 2: Path redirected from root_u to root_v ***)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec find_pure_redirected_ec
    (sparent sparent': Seq.seq SZ.t) (w: nat) (ec: nat) (n: nat) (root_u root_v: nat)
  : Lemma (requires valid_parents sparent n /\ valid_parents sparent' n /\
                    w < n /\ root_u < n /\ root_v < n /\ ec < n /\
                    root_u <> root_v /\
                    SZ.v (Seq.index sparent root_u) = root_u /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    SZ.v (Seq.index sparent' root_v) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    find_pure sparent w ec n = root_u)
          (ensures find_pure sparent' w (ec + 1) n = root_v)
          (decreases ec)
  = if ec = 0 then begin
      assert (w = root_u);
      assert (find_pure sparent' root_u 1 n = root_v)
    end else if w = root_u then begin
      find_pure_fixed sparent' root_v ec n;
      assert (find_pure sparent' root_u (ec + 1) n = root_v)
    end else begin
      assert (Seq.index sparent' w == Seq.index sparent w);
      find_pure_redirected_ec sparent sparent' (SZ.v (Seq.index sparent w)) (ec - 1) n root_u root_v;
      assert (find_pure sparent' w (ec + 1) n = root_v)
    end

let find_pure_redirected_n
    (sparent sparent': Seq.seq SZ.t) (w: nat) (ec: nat) (n: nat) (root_u root_v: nat)
  : Lemma (requires valid_parents sparent n /\ valid_parents sparent' n /\
                    w < n /\ root_u < n /\ root_v < n /\ ec < n /\
                    root_u <> root_v /\
                    SZ.v (Seq.index sparent root_u) = root_u /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    SZ.v (Seq.index sparent' root_v) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    find_pure sparent w ec n = root_u)
          (ensures find_pure sparent' w n n = root_v)
  = find_pure_redirected_ec sparent sparent' w ec n root_u root_v;
    find_pure_bounded sparent' w (ec + 1) n;
    find_pure_split sparent' w (ec + 1) (n - ec - 1) n;
    find_pure_fixed sparent' root_v (n - ec - 1) n
#pop-options

(*** Generic path lemma: comp equates endpoints of all edges ⟹ comp equates reachable vertices ***)

let rec comp_along_path (comp: nat -> nat) (path: list edge) (es: list edge) (a b: nat)
  : Lemma (requires
             is_path_from_to path a b /\ subset_edges path es /\
             (forall (e: edge). mem_edge e es ==> comp e.u = comp e.v))
          (ensures comp a = comp b)
          (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      if e.u = a then
        comp_along_path comp rest es e.v b
      else
        comp_along_path comp rest es e.u b

// If comp equates endpoints of all edges in es, it equates reachable vertices
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

(*** Union Maintains uf_inv ***)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"

// Helper: compute comp' value for any vertex
let comp'_value
    (sparent sparent': Seq.seq SZ.t) (w: nat) (ec: nat) (n: nat) (root_u root_v: nat)
  : Lemma (requires valid_parents sparent n /\ valid_parents sparent' n /\
                    w < n /\ root_u < n /\ root_v < n /\ ec < n /\
                    root_u <> root_v /\
                    SZ.v (Seq.index sparent root_u) = root_u /\
                    SZ.v (Seq.index sparent root_v) = root_v /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    SZ.v (Seq.index sparent' root_v) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    // from uf_inv
                    find_pure sparent w n n < n /\
                    (SZ.v (Seq.index sparent (find_pure sparent w n n)) = find_pure sparent w n n) /\
                    find_pure sparent w ec n = find_pure sparent w n n)
          (ensures find_pure sparent' w n n =
                   (if find_pure sparent w n n = root_u then root_v
                    else find_pure sparent w n n))
  = find_pure_bounded sparent w n n;
    if find_pure sparent w n n = root_u then
      find_pure_redirected_n sparent sparent' w ec n root_u root_v
    else
      find_pure_unchanged sparent sparent' w n n root_u

// Helper: edges_eq_comp - comp' equates endpoints of all edges in (new_edge :: edges)
let edges_eq_comp
    (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u_val v_val: nat) (root_u root_v: nat) (new_edge: edge) (e: edge)
  : Lemma (requires uf_inv sparent edges n ec /\
                    u_val < n /\ v_val < n /\
                    root_u = find_pure sparent u_val n n /\
                    root_v = find_pure sparent v_val n n /\
                    root_u <> root_v /\
                    valid_parents sparent' n /\
                    SZ.v (Seq.index sparent' root_u) = root_v /\
                    SZ.v (Seq.index sparent' root_v) = root_v /\
                    (forall (i: nat). i < n /\ i <> root_u ==>
                      Seq.index sparent' i == Seq.index sparent i) /\
                    new_edge.u = u_val /\ new_edge.v = v_val /\
                    mem_edge e (new_edge :: edges) /\
                    e.u < n /\ e.v < n)
          (ensures find_pure sparent' e.u n n = find_pure sparent' e.v n n)
  = find_pure_bounded sparent u_val n n;
    find_pure_bounded sparent v_val n n;
    if edge_eq e new_edge then begin
      edge_eq_endpoints e new_edge;
      // {e.u, e.v} = {u_val, v_val}, all < n
      comp'_value sparent sparent' e.u ec n root_u root_v;
      comp'_value sparent sparent' e.v ec n root_u root_v
    end else begin
      assert (mem_edge e edges);
      // One-hop path shows reachable
      edge_eq_reflexive e;
      assert (is_path_from_to [e] e.u e.v);
      assert (subset_edges [e] edges);
      assert (reachable edges e.u e.v);
      // By old completeness: find_pure sparent e.u n n = find_pure sparent e.v n n
      // Map through comp'_value
      comp'_value sparent sparent' e.u ec n root_u root_v;
      comp'_value sparent sparent' e.v ec n root_u root_v
    end

let uf_inv_union
    (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat)
    (u_val v_val: nat) (root_u root_v: nat) (new_edge: edge)
  : Lemma (requires uf_inv sparent edges n ec /\
                    all_edges_valid edges n /\
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
          (ensures uf_inv sparent' (new_edge :: edges) n (ec + 1) /\
                   all_edges_valid (new_edge :: edges) n)
  = find_pure_bounded sparent u_val n n;
    find_pure_bounded sparent v_val n n;
    assert (SZ.v (Seq.index sparent' root_v) = root_v);

    // (1) All find results in sparent' are fixed points and bounded
    let roots_ok (w: nat) : Lemma (requires w < n)
        (ensures find_pure sparent' w n n < n /\
                 SZ.v (Seq.index sparent' (find_pure sparent' w n n)) =
                 find_pure sparent' w n n) =
      comp'_value sparent sparent' w ec n root_u root_v;
      if find_pure sparent w n n = root_u then begin
        // find_pure sparent' w n n = root_v < n
        assert (find_pure sparent' w n n = root_v)
      end else begin
        let r = find_pure sparent w n n in
        // find_pure sparent' w n n = r < n
        assert (find_pure sparent' w n n = r);
        assert (r <> root_u);
        assert (Seq.index sparent' r == Seq.index sparent r)
      end
    in

    // (2) ec+1 steps suffice in sparent'
    let depth_ok (w: nat) : Lemma (requires w < n)
        (ensures find_pure sparent' w (ec + 1) n = find_pure sparent' w n n) =
      find_pure_bounded sparent w n n;
      comp'_value sparent sparent' w ec n root_u root_v;
      if find_pure sparent w n n = root_u then begin
        find_pure_redirected_ec sparent sparent' w ec n root_u root_v
      end else begin
        find_pure_unchanged sparent sparent' w (ec + 1) n root_u;
        // find_pure sparent' w (ec+1) = find_pure sparent w (ec+1)
        // find_pure sparent w (ec+1) = find_pure sparent w (ec + 1)
        // = find_pure sparent (find_pure sparent w ec n) 1 n [split]
        // = find_pure sparent root 1 n = root [fixed]
        find_pure_split sparent w ec 1 n;
        let r = find_pure sparent w n n in
        find_pure_fixed sparent r 1 n
      end
    in

    // (3) UF completeness for new_edge :: edges
    let complete (a b: nat) : Lemma
        (requires a < n /\ b < n /\ reachable (new_edge :: edges) a b)
        (ensures find_pure sparent' a n n = find_pure sparent' b n n) =
      let comp (w: nat) : nat = find_pure sparent' w n n in
      let edge_comp (e: edge) : Lemma
          (requires mem_edge e (new_edge :: edges))
          (ensures comp e.u = comp e.v) =
        // Establish e.u < n /\ e.v < n from all_edges_valid + edge_eq_endpoints
        (if edge_eq e new_edge then edge_eq_endpoints e new_edge
         else ());
        edges_eq_comp sparent sparent' edges n ec u_val v_val root_u root_v new_edge e
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires edge_comp);
      comp_reachable comp (new_edge :: edges) a b
    in

    FStar.Classical.forall_intro (FStar.Classical.move_requires roots_ok);
    FStar.Classical.forall_intro (FStar.Classical.move_requires depth_ok);
    // Establish completeness using nested forall_intro
    let complete_inner (a: nat) (b: nat) : Lemma
        ((a < n /\ b < n /\ reachable (new_edge :: edges) a b) ==>
         find_pure sparent' a n n = find_pure sparent' b n n) =
      FStar.Classical.move_requires (complete a) b
    in
    let complete_outer (a: nat) : Lemma
        (forall (b: nat). (a < n /\ b < n /\ reachable (new_edge :: edges) a b) ==>
         find_pure sparent' a n n = find_pure sparent' b n n) =
      FStar.Classical.forall_intro (complete_inner a)
    in
    FStar.Classical.forall_intro complete_outer;
    // Establish all_edges_valid for new_edge :: edges
    let valid_eps (e: edge) : Lemma
        (requires mem_edge e (new_edge :: edges))
        (ensures e.u < n /\ e.v < n) =
      if edge_eq e new_edge then edge_eq_endpoints e new_edge
      else ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires valid_eps);
    // Assert pieces to help Z3 assemble the postcondition
    assert (valid_parents sparent' n);
    assert (ec + 1 < n)

#pop-options

(*** Edge membership implies reachability ***)

let mem_edge_reachable (e: edge) (edges: list edge)
  : Lemma (requires mem_edge e edges)
          (ensures reachable edges e.u e.v)
  = edge_eq_reflexive e;
    assert (is_path_from_to [e] e.u e.v);
    assert (subset_edges [e] edges)
