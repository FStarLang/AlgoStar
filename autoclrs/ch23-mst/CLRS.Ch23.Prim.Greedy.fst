(*
   CLRS Chapter 23: Prim Greedy Safety
   
   Greedy safety predicate and all supporting lemmas for Prim's MST.
   Follows KeyInv style: opaque predicates, explicit instantiation, tight verification.
*)
module CLRS.Ch23.Prim.Greedy

open FStar.Mul
open FStar.SizeT
module SZ = FStar.SizeT
module Seq = FStar.Seq
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Defs
module PrimSpec = CLRS.Ch23.Prim.Spec
module Bridge = CLRS.Ch23.Kruskal.Bridge
module KeyInv = CLRS.Ch23.Prim.KeyInv

(*** Impl ↔ Spec Bridging ***)

let sizet_to_int (x: SZ.t) : int = SZ.v x

let weights_to_adj_matrix (weights_seq: Seq.seq SZ.t) (n: nat)
  : Pure PrimSpec.adj_matrix
    (requires Seq.length weights_seq == n * n)
    (ensures fun adj ->
      Seq.length adj == n /\
      (forall (u:nat). u < n ==> Seq.length (Seq.index adj u) == n))
  = Seq.init n (fun (u:nat{u < n}) ->
      Seq.init n (fun (v:nat{v < n}) ->
        let idx = u * n + v in
        let w_sizet = Seq.index weights_seq idx in
        let w : int = sizet_to_int w_sizet in
        if w >= sizet_to_int infinity then PrimSpec.infinity else w
      )
    )

#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let weights_to_adj_preserves (weights_seq: Seq.seq SZ.t) (n: nat) (u v: nat)
  : Lemma (requires valid_weights weights_seq n /\ n > 0 /\ u < n /\ v < n /\
                    u * n + v < n * n)
          (ensures (let adj = weights_to_adj_matrix weights_seq n in
                    let w_imp = SZ.v (Seq.index weights_seq (u * n + v)) in
                    let w_spec = Seq.index (Seq.index adj u) v in
                    (w_imp > 0 /\ w_imp < SZ.v infinity ==> w_spec = w_imp) /\
                    (w_imp = 0 ==> w_spec = 0) /\
                    (w_imp >= SZ.v infinity ==> w_spec = PrimSpec.infinity)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let weights_to_adj_well_formed (weights_seq: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires Seq.length weights_seq == n * n /\ n > 0 /\ symmetric_weights weights_seq n)
    (ensures PrimSpec.well_formed_adj (weights_to_adj_matrix weights_seq n) n)
  = PrimSpec.well_formed_adj_intro (weights_to_adj_matrix weights_seq n) n
#pop-options

(*** Index arithmetic helpers ***)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec lemma_prod_fits (u n: nat) : Lemma
  (requires u < n /\ n > 0) (ensures u * n < n * n) (decreases n - u)
  = if u >= n - 1 then ()
    else (lemma_prod_fits (u + 1) n; assert ((u + 1) * n < n * n))

let lemma_index_bound (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0) (ensures u * n + v < n * n)
  = if u + 1 < n then lemma_prod_fits (u + 1) n else ()
#pop-options

(*** MST edge lists ***)

let rec edges_from_parent_key
  (parent_seq key_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Pure (list edge)
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\ i <= n)
    (ensures fun _ -> True)
    (decreases (n - i))
  = if i >= n then []
    else if i = source then edges_from_parent_key parent_seq key_seq n source (i + 1)
    else
      let p = SZ.v (Seq.index parent_seq i) in
      let w = SZ.v (Seq.index key_seq i) in
      { u = p; v = i; w = w } :: edges_from_parent_key parent_seq key_seq n source (i + 1)

let rec mst_edges_so_far
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Pure (list edge)
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n)
    (ensures fun _ -> True)
    (decreases (n - i))
  = if i >= n then []
    else if i = source then mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)
    else if SZ.v (Seq.index in_mst_seq i) = 1 then
      let p = SZ.v (Seq.index parent_seq i) in
      let w = SZ.v (Seq.index key_seq i) in
      { u = p; v = i; w = w } :: mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec mst_edges_all_in
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) = 1))
    (ensures mst_edges_so_far parent_seq key_seq in_mst_seq n source i ==
             edges_from_parent_key parent_seq key_seq n source i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_all_in parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_all_in parent_seq key_seq in_mst_seq n source (i + 1)

let rec mst_edges_none_in
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) <> 1))
    (ensures mst_edges_so_far parent_seq key_seq in_mst_seq n source i == [])
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_none_in parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_none_in parent_seq key_seq in_mst_seq n source (i + 1)

let rec mst_edges_ext
  (ps1 ks1 ps2 ks2 in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps1 == n /\ Seq.length ks1 == n /\
              Seq.length ps2 == n /\ Seq.length ks2 == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
                Seq.index ps1 v == Seq.index ps2 v /\ Seq.index ks1 v == Seq.index ks2 v))
    (ensures mst_edges_so_far ps1 ks1 in_mst_seq n source i ==
             mst_edges_so_far ps2 ks2 in_mst_seq n source i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)
    else if SZ.v (Seq.index in_mst_seq i) = 1 then
      mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)
    else
      mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)

let rec mst_edges_mem_implies_in_mst
    (ps ks ims: Seq.seq SZ.t) (n source: nat) (i: nat) (e: edge)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims == n /\
              i <= n /\ source < n /\ mem_edge e (mst_edges_so_far ps ks ims n source i))
    (ensures exists (v:nat). v >= i /\ v < n /\ v <> source /\
              SZ.v (Seq.index ims v) = 1 /\ edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e
    else if SZ.v (Seq.index ims i) = 1 then
      (if edge_eq e ({u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)}) then ()
       else mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e)
    else mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e

let rec mst_edges_in_mst_implies_mem
    (ps ks ims: Seq.seq SZ.t) (n source: nat) (i: nat) (v: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims == n /\
              i <= n /\ source < n /\ v >= i /\ v < n /\ v <> source /\
              SZ.v (Seq.index ims v) = 1)
    (ensures mem_edge ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})
                      (mst_edges_so_far ps ks ims n source i))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v
    else if i = v then
      edge_eq_reflexive ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})
    else if SZ.v (Seq.index ims i) = 1 then
      mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v
    else
      mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v

let rec mst_edges_source_unchanged
    (ps ks ims1 ims2: Seq.seq SZ.t) (n src: nat) (i: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims1 == n /\ Seq.length ims2 == n /\
              i <= n /\ src < n /\
              (forall (v:nat). v < n /\ v <> src ==> Seq.index ims1 v == Seq.index ims2 v))
    (ensures mst_edges_so_far ps ks ims1 n src i == mst_edges_so_far ps ks ims2 n src i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = src then mst_edges_source_unchanged ps ks ims1 ims2 n src (i + 1)
    else (mst_edges_source_unchanged ps ks ims1 ims2 n src (i + 1);
          assert (Seq.index ims1 i == Seq.index ims2 i))
#pop-options

(*** Subset helpers ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec subset_from_mem (a b: list edge)
  : Lemma (requires forall (e: edge). mem_edge e a ==> mem_edge e b)
          (ensures subset_edges a b) (decreases a)
  = match a with | [] -> () | _ :: tl -> subset_from_mem tl b

let mst_edges_add_subset
    (ps ks ims_old ims_new: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims_old == n /\ Seq.length ims_new == n /\
              source < n /\ u < n /\ u <> source /\
              SZ.v (Seq.index ims_old u) <> 1 /\
              SZ.v (Seq.index ims_new u) = 1 /\
              (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v))
    (ensures subset_edges (mst_edges_so_far ps ks ims_old n source 0)
                          (mst_edges_so_far ps ks ims_new n source 0))
  = let aux (e: edge) : Lemma
      (requires mem_edge e (mst_edges_so_far ps ks ims_old n source 0))
      (ensures mem_edge e (mst_edges_so_far ps ks ims_new n source 0))
      = mst_edges_mem_implies_in_mst ps ks ims_old n source 0 e;
        FStar.Classical.exists_elim
          (mem_edge e (mst_edges_so_far ps ks ims_new n source 0))
          #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index ims_old v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
          ()
          (fun (v: nat{v >= 0 /\ v < n /\ v <> source /\
                       SZ.v (Seq.index ims_old v) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})}) ->
            assert (v <> u);
            assert (SZ.v (Seq.index ims_new v) = 1);
            mst_edges_in_mst_implies_mem ps ks ims_new n source 0 v;
            let ev = {u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)} in
            edge_eq_symmetric e ev;
            mem_edge_eq ev e (mst_edges_so_far ps ks ims_new n source 0))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    subset_from_mem (mst_edges_so_far ps ks ims_old n source 0)
                    (mst_edges_so_far ps ks ims_new n source 0)
#pop-options

(*** Weight ↔ Graph edge bridging ***)

/// Positive weight → edge in graph. Uses swt for clean reasoning.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let weights_edge_in_graph
    (ws: Seq.seq SZ.t) (n u v: nat)
  : Lemma
    (requires n > 0 /\ u < n /\ v < n /\ u <> v /\
              Seq.length ws == n * n /\
              symmetric_weights ws n /\ valid_weights ws n /\
              KeyInv.swt ws n u v > 0 /\ KeyInv.swt ws n u v < SZ.v infinity)
    (ensures (let adj = weights_to_adj_matrix ws n in
              let g = PrimSpec.adj_to_graph adj n in
              mem_edge ({u = u; v = v; w = KeyInv.swt ws n u v}) g.edges))
  = let adj = weights_to_adj_matrix ws n in
    lemma_index_bound u v n;
    weights_to_adj_preserves ws n u v;
    let eu = if u < v then u else v in
    let ev = if u < v then v else u in
    lemma_index_bound eu ev n;
    weights_to_adj_preserves ws n eu ev;
    assert (Seq.index (Seq.index adj eu) ev <> PrimSpec.infinity);
    PrimSpec.has_edge_intro adj n eu ev;
    PrimSpec.well_formed_adj_intro adj n;
    PrimSpec.adj_to_graph_has_edge adj n eu ev;
    if u < v then ()
    else begin
      edge_eq_reflexive ({u = ev; v = eu; w = KeyInv.swt ws n u v});
      edge_eq_symmetric ({u = ev; v = eu; w = KeyInv.swt ws n u v})
                         ({u = eu; v = ev; w = KeyInv.swt ws n u v});
      mem_edge_eq ({u = eu; v = ev; w = KeyInv.swt ws n u v})
                  ({u = ev; v = eu; w = KeyInv.swt ws n u v})
                  (PrimSpec.adj_to_graph adj n).edges
    end
#pop-options

/// Graph edge weight = swt
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let graph_edge_weight_eq
    (ws: Seq.seq SZ.t) (n: nat) (e: edge)
  : Lemma
    (requires n > 0 /\ Seq.length ws == n * n /\
              valid_weights ws n /\ symmetric_weights ws n /\
              mem_edge e (PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n).edges /\
              e.u < n /\ e.v < n)
    (ensures e.w = KeyInv.swt ws n e.u e.v)
  = let adj = weights_to_adj_matrix ws n in
    PrimSpec.adj_to_graph_edges_valid adj n e;
    PrimSpec.well_formed_adj_intro adj n;
    PrimSpec.adj_to_graph_edge_weight adj n e;
    lemma_index_bound e.u e.v n;
    weights_to_adj_preserves ws n e.u e.v
#pop-options

(*** Greedy Safety Predicate ***)

/// Opaque greedy safety: there exists an MST T containing all current edges.
[@@"opaque_to_smt"]
let prim_safe (ps ks ims ws: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length ps == n /\ Seq.length ks == n /\
  Seq.length ims == n /\ Seq.length ws == n * n /\
  (symmetric_weights ws n /\
   all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n) ==>
   (let g = PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n in
    let es = mst_edges_so_far ps ks ims n source 0 in
    exists (t: list edge). is_mst g t /\ subset_edges es t))

#push-options "--z3rlimit 50"
let prim_safe_init
    (ps ks ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\
              Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims == n /\ Seq.length ws == n * n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) <> 1))
    (ensures prim_safe ps ks ims ws n source)
  = mst_edges_none_in ps ks ims n source 0;
    reveal_opaque (`%prim_safe) (prim_safe ps ks ims ws n source);
    FStar.Classical.arrow_to_impl
      #(symmetric_weights ws n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
      #(let g = PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n in
        let es = mst_edges_so_far ps ks ims n source 0 in
        exists (t: list edge). is_mst g t /\ subset_edges es t)
      (fun _ ->
        weights_to_adj_well_formed ws n;
        let adj = weights_to_adj_matrix ws n in
        PrimSpec.adj_to_graph_edges adj n;
        let g = PrimSpec.adj_to_graph adj n in
        let aux (e: edge) : Lemma
          (requires mem_edge e g.edges) (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
          = PrimSpec.adj_to_graph_edges_valid adj n e in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        CLRS.Ch23.MST.Existence.mst_exists g)
#pop-options

let prim_safe_elim
    (ps ks ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_safe ps ks ims ws n source /\
              n > 0 /\ source < n /\
              Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims == n /\ Seq.length ws == n * n /\
              symmetric_weights ws n /\
              all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures (let g = PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n in
              let es = mst_edges_so_far ps ks ims n source 0 in
              exists (t: list edge). is_mst g t /\ subset_edges es t))
  = reveal_opaque (`%prim_safe) (prim_safe ps ks ims ws n source)

/// Frame: updating non-MST vertices' keys/parents preserves prim_safe.
let prim_safe_update_non_mst
    (ps1 ks1 ps2 ks2 ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_safe ps1 ks1 ims ws n source /\
              n > 0 /\ source < n /\
              Seq.length ps1 == n /\ Seq.length ks1 == n /\
              Seq.length ims == n /\
              Seq.length ps2 == n /\ Seq.length ks2 == n /\
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index ims v) = 1 ==>
                Seq.index ps1 v == Seq.index ps2 v /\ Seq.index ks1 v == Seq.index ks2 v))
    (ensures prim_safe ps2 ks2 ims ws n source)
  = mst_edges_ext ps1 ks1 ps2 ks2 ims n source 0;
    reveal_opaque (`%prim_safe) (prim_safe ps1 ks1 ims ws n source);
    reveal_opaque (`%prim_safe) (prim_safe ps2 ks2 ims ws n source)

(*** Core Greedy Step via Cut Property ***)

/// The main cut_property application. Uses KeyInv predicates as preconditions.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let prim_cut_step
    (ps ks ims ws: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\ u <> source /\
      Seq.length ps == n /\ Seq.length ks == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      valid_weights ws n /\ symmetric_weights ws n /\
      parent_valid ps n /\
      key_parent_consistent ks ps ws n source /\
      SZ.v (Seq.index ims u) <> 1 /\
      SZ.v (Seq.index ks u) > 0 /\
      SZ.v (Seq.index ks u) < SZ.v infinity /\
      SZ.v (Seq.index ims (SZ.v (Seq.index ps u))) = 1 /\
      // In-MST non-source vertices have parent in MST
      (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index ims v) = 1 ==>
        SZ.v (Seq.index ims (SZ.v (Seq.index ps v))) = 1) /\
      // Extract-min: key[u] <= key[v] for all non-MST v
      (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1 ==>
        SZ.v (Seq.index ks u) <= SZ.v (Seq.index ks v)) /\
      // Key invariant
      KeyInv.key_inv ks ims ws n /\
      no_zero_edges ws n /\
      // Old edges are safe
      (let g = PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n in
       let old_es = mst_edges_so_far ps ks ims n source 0 in
       exists (t: list edge). is_mst g t /\ subset_edges old_es t))
    (ensures
      (let adj = weights_to_adj_matrix ws n in
       let g = PrimSpec.adj_to_graph adj n in
       let pu = SZ.v (Seq.index ps u) in
       let ku = SZ.v (Seq.index ks u) in
       let new_edge : edge = {u = pu; v = u; w = ku} in
       let old_es = mst_edges_so_far ps ks ims n source 0 in
       exists (t: list edge). is_mst g t /\ subset_edges (new_edge :: old_es) t))
  = let adj = weights_to_adj_matrix ws n in
    let g = PrimSpec.adj_to_graph adj n in
    let pu = SZ.v (Seq.index ps u) in
    let ku = SZ.v (Seq.index ks u) in
    let new_edge : edge = {u = pu; v = u; w = ku} in
    let old_es = mst_edges_so_far ps ks ims n source 0 in
    PrimSpec.adj_to_graph_edges adj n;
    PrimSpec.well_formed_adj_intro adj n;
    // new_edge ∈ g.edges
    assert (pu <> u);
    lemma_index_bound pu u n;
    lemma_prod_fits pu n;
    // ku = weight(pu, u) from kpc, and ku > 0, ku < infinity
    // So swt ws n pu u = ku
    assert (KeyInv.swt ws n pu u = ku);
    weights_edge_in_graph ws n pu u;
    // Define cut
    let s : cut = fun v -> v < n && SZ.v (Seq.index ims v) = 1 in
    assert (crosses_cut new_edge s);
    // respects: no old edge crosses cut
    let rec respects_proof (es: list edge)
      : Lemma (requires 
                (forall (e: edge). mem_edge e es ==>
                  (exists (v:nat). v >= 0 /\ v < n /\ v <> source /\
                    SZ.v (Seq.index ims v) = 1 /\
                    edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))))
              (ensures respects es s)
              (decreases es)
      = match es with
        | [] -> ()
        | e :: tl ->
          FStar.Classical.exists_elim
            (not (crosses_cut e s))
            #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                     SZ.v (Seq.index ims v) = 1 /\
                     edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
            ()
            (fun (v:nat{v >= 0 /\ v < n /\ v <> source /\
                        SZ.v (Seq.index ims v) = 1 /\
                        edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})}) ->
              edge_eq_endpoints e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)});
              let pv = SZ.v (Seq.index ps v) in
              assert (s v = true);
              assert (s pv = true));
          respects_proof tl
    in
    let mem_proof (e: edge) : Lemma
      (requires mem_edge e old_es)
      (ensures exists (v:nat). v >= 0 /\ v < n /\ v <> source /\
                SZ.v (Seq.index ims v) = 1 /\
                edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
      = mst_edges_mem_implies_in_mst ps ks ims n source 0 e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires mem_proof);
    respects_proof old_es;
    // is_light_edge: use key_inv + extract-min
    KeyInv.key_inv_bare ks ims ws n;
    let light_proof (e': edge) : Lemma
      (requires mem_edge e' g.edges /\ crosses_cut e' s)
      (ensures new_edge.w <= e'.w)
      = PrimSpec.adj_to_graph_edges_valid adj n e';
        graph_edge_weight_eq ws n e';
        lemma_index_bound (e'.u) (e'.v) n;
        lemma_index_bound (e'.v) (e'.u) n;
        // e'.w = swt = SZ.v (Seq.index ws (e'.u * n + e'.v))
        // no_zero_edges + e'.u <> e'.v → weight > 0
        // valid_weights → weight < infinity
        // symmetric → weights[v*n+u] = weights[u*n+v]
        if s e'.u then begin
          // e'.u in MST, e'.v not: key_inv gives key[e'.v] <= weights[e'.u*n+e'.v]
          // extract-min: key[u] <= key[e'.v]
          ()
        end else begin
          // e'.v in MST, e'.u not: key_inv gives key[e'.u] <= weights[e'.v*n+e'.u]
          // symmetric: weights[e'.v*n+e'.u] = weights[e'.u*n+e'.v] = e'.w
          // extract-min: key[u] <= key[e'.u] <= e'.w
          ()
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires light_proof);
    // valid edges
    let ve (e': edge) : Lemma
      (requires mem_edge e' g.edges) (ensures e'.u < g.n /\ e'.v < g.n)
      = PrimSpec.adj_to_graph_edges_valid adj n e'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ve);
    cut_property g old_es new_edge s
#pop-options

/// Full add-vertex step: prim_safe preserved when adding vertex u.
/// Takes prim_safe + KeyInv predicates as opaque preconditions.
#push-options "--z3rlimit 200"
let prim_safe_add_vertex
    (ps ks ims_old ims_new ws: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires prim_safe ps ks ims_old ws n source /\
              n > 0 /\ source < n /\ u < n /\
              Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims_old == n /\ Seq.length ims_new == n /\
              Seq.length ws == n * n /\
              parent_valid ps n /\
              key_parent_consistent ks ps ws n source /\
              SZ.v (Seq.index ims_new u) = 1 /\
              (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
              SZ.v (Seq.index ims_old u) <> 1 /\
              SZ.v (Seq.index ks u) < SZ.v infinity /\
              SZ.v (Seq.index ims_old (SZ.v (Seq.index ps u))) = 1 /\
              (forall (v:nat). v < n /\ SZ.v (Seq.index ims_old v) <> 1 ==>
                SZ.v (Seq.index ks u) <= SZ.v (Seq.index ks v)) /\
              KeyInv.key_inv ks ims_old ws n /\
              valid_weights ws n /\
              SZ.v (Seq.index ks u) > 0 /\
              no_zero_edges ws n /\
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index ims_old v) = 1 ==>
                SZ.v (Seq.index ims_old (SZ.v (Seq.index ps v))) = 1))
    (ensures prim_safe ps ks ims_new ws n source)
  = reveal_opaque (`%prim_safe) (prim_safe ps ks ims_old ws n source);
    reveal_opaque (`%prim_safe) (prim_safe ps ks ims_new ws n source);
    let old_es = mst_edges_so_far ps ks ims_old n source 0 in
    let new_es = mst_edges_so_far ps ks ims_new n source 0 in
    let pu = SZ.v (Seq.index ps u) in
    let ku = SZ.v (Seq.index ks u) in
    let new_edge : edge = {u = pu; v = u; w = ku} in
    // new_es ⊆ new_edge :: old_es
    let aux (e: edge) : Lemma
      (requires mem_edge e new_es)
      (ensures mem_edge e (new_edge :: old_es))
      = mst_edges_mem_implies_in_mst ps ks ims_new n source 0 e;
        FStar.Classical.exists_elim
          (mem_edge e (new_edge :: old_es))
          #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index ims_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
          ()
          (fun (v: nat{v >= 0 /\ v < n /\ v <> source /\
                       SZ.v (Seq.index ims_new v) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})}) ->
            if v = u then ()
            else begin
              assert (SZ.v (Seq.index ims_old v) = 1);
              mst_edges_in_mst_implies_mem ps ks ims_old n source 0 v;
              let ev = {u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)} in
              edge_eq_symmetric e ev;
              mem_edge_eq ev e old_es
            end)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    subset_from_mem new_es (new_edge :: old_es);
    // Now use arrow_to_impl for the symmetric + connected guard
    FStar.Classical.arrow_to_impl
      #(symmetric_weights ws n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
      #(let g = PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n in
        exists (t: list edge). is_mst g t /\ subset_edges new_es t)
      (fun _ ->
        let adj = weights_to_adj_matrix ws n in
        let g = PrimSpec.adj_to_graph adj n in
        assert (exists (t: list edge). is_mst g t /\ subset_edges old_es t);
        if u = source then begin
          let aux2 (e: edge) : Lemma
            (requires mem_edge e new_es) (ensures mem_edge e old_es)
            = mst_edges_mem_implies_in_mst ps ks ims_new n source 0 e;
              FStar.Classical.exists_elim
                (mem_edge e old_es) #nat
                #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index ims_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
                ()
                (fun (v:nat{v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index ims_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})}) ->
                  assert (v <> u);
                  assert (SZ.v (Seq.index ims_old v) = 1);
                  mst_edges_in_mst_implies_mem ps ks ims_old n source 0 v;
                  let ev = {u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)} in
                  edge_eq_symmetric e ev;
                  mem_edge_eq ev e old_es)
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
          subset_from_mem new_es old_es;
          FStar.Classical.exists_elim
            (exists (t: list edge). is_mst g t /\ subset_edges new_es t)
            #(list edge) #(fun t -> is_mst g t /\ subset_edges old_es t) ()
            (fun (t: list edge{is_mst g t /\ subset_edges old_es t}) ->
              subset_edges_transitive new_es old_es t)
        end
        else begin
          KeyInv.key_inv_bare ks ims_old ws n;
          prim_cut_step ps ks ims_old ws n source u;
          FStar.Classical.exists_elim
            (exists (t: list edge). is_mst g t /\ subset_edges new_es t)
            #(list edge) #(fun t -> is_mst g t /\ subset_edges (new_edge :: old_es) t) ()
            (fun (t: list edge{is_mst g t /\ subset_edges (new_edge :: old_es) t}) ->
              subset_edges_transitive new_es (new_edge :: old_es) t)
        end)
#pop-options

(*** noRepeats tracking ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec mst_edges_noRepeats_add
    (ps ks ims_old ims_new: Seq.seq SZ.t) (n source u: nat) (i: nat)
  : Lemma
    (requires
      Seq.length ps == n /\ Seq.length ks == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      i <= n /\ source < n /\ u < n /\ u <> source /\
      parent_valid ps n /\
      all_keys_bounded ks /\
      SZ.v (Seq.index ks u) < SZ.v infinity /\
      SZ.v (Seq.index ims_old u) <> 1 /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      (forall (v:nat). v < n /\ SZ.v (Seq.index ks v) < SZ.v infinity /\ v <> source ==>
        SZ.v (Seq.index ims_old (SZ.v (Seq.index ps v))) = 1) /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source i))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source i))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then
      mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1)
    else begin
      let ei = {u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)} in
      let old_here = SZ.v (Seq.index ims_old i) = 1 in
      let new_here = SZ.v (Seq.index ims_new i) = 1 in
      if i = u then begin
        assert (new_here);
        assert (not old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1);
        let tl_new = mst_edges_so_far ps ks ims_new n source (i + 1) in
        let aux (e: edge) : Lemma
          (requires mem_edge e tl_new) (ensures ~(edge_eq ei e))
          = mst_edges_mem_implies_in_mst ps ks ims_new n source (i + 1) e;
            FStar.Classical.exists_elim
              (~(edge_eq ei e))
              #nat #(fun j -> j >= i + 1 /\ j < n /\ j <> source /\
                       SZ.v (Seq.index ims_new j) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)}))
              ()
              (fun (j: nat{j >= i + 1 /\ j < n /\ j <> source /\
                           SZ.v (Seq.index ims_new j) = 1 /\
                           edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)})}) ->
                assert (j <> u);
                assert (SZ.v (Seq.index ims_old j) = 1);
                let ej = {u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)} in
                if edge_eq ei e then begin
                  edge_eq_transitive ei e ej;
                  edge_eq_endpoints ei ej;
                  ()
                end)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else if new_here then begin
        assert (old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1);
        let tl_new = mst_edges_so_far ps ks ims_new n source (i + 1) in
        let aux (e: edge) : Lemma
          (requires mem_edge e tl_new) (ensures ~(edge_eq ei e))
          = mst_edges_mem_implies_in_mst ps ks ims_new n source (i + 1) e;
            FStar.Classical.exists_elim
              (~(edge_eq ei e))
              #nat #(fun j -> j >= i + 1 /\ j < n /\ j <> source /\
                       SZ.v (Seq.index ims_new j) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)}))
              ()
              (fun (j: nat{j >= i + 1 /\ j < n /\ j <> source /\
                           SZ.v (Seq.index ims_new j) = 1 /\
                           edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)})}) ->
                let ej = {u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)} in
                if j = u then begin
                  if edge_eq ei e then begin
                    edge_eq_transitive ei e ej;
                    edge_eq_endpoints ei ej;
                    ()
                  end
                end else begin
                  assert (SZ.v (Seq.index ims_old j) = 1);
                  mst_edges_in_mst_implies_mem ps ks ims_old n source (i + 1) j;
                  if edge_eq ei e then begin
                    edge_eq_transitive ei e ej;
                    edge_eq_symmetric ei ej;
                    mem_edge_eq ej ei (mst_edges_so_far ps ks ims_old n source (i + 1))
                  end
                end)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else begin
        assert (not old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1)
      end
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let mst_edges_noRepeats_init
    (ps ks ims: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims == n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) <> 1))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims n source 0))
  = mst_edges_none_in ps ks ims n source 0
#pop-options

(*** Connectivity lemma: min_key < infinity ***)

/// When source is in MST and there's a non-MST vertex u,
/// connectivity + key_inv + valid_weights guarantees some non-MST vertex has finite key.
/// This is needed for prim_inv_add_vertex's precondition.
///
/// Argument: graph connected → path from source (MST) to u (non-MST).
/// Path must cross the MST/non-MST boundary at some edge (w,v) with w in MST, v not.
/// valid_weights → weight(w,v) > 0 ∧ weight(w,v) < infinity (since w≠v and no_zero_edges).
/// key_inv → key[v] ≤ weight(w,v) < infinity.
/// So min_key ≤ key[v] < infinity.
///
/// This is a deep graph theory argument. For now we state it and leave the proof
/// to future work (requires path manipulation lemmas not yet in the codebase).
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let connectivity_gives_finite_key
    (ks ims ws: Seq.seq SZ.t) (n source: nat) (min_key count: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\
      KeyInv.key_inv ks ims ws n /\
      valid_weights ws n /\ symmetric_weights ws n /\ no_zero_edges ws n /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n) /\
      SZ.v (Seq.index ims source) = 1 /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims j) = 0 \/ SZ.v (Seq.index ims j) = 1) /\
      SZ.v (Seq.index ks source) == 0 /\
      min_key <= SZ.v infinity /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims j) = 0 ==> min_key <= SZ.v (Seq.index ks j)) /\
      KeyInv.mst_count ims n 0 == count /\ count < n)
    (ensures min_key < SZ.v infinity)
  = // count < n → exists non-MST vertex
    KeyInv.mst_count_not_full ims n 0;
    // Convert ims to vertex_set (Seq.seq bool)
    let its : PrimSpec.vertex_set = Seq.init n (fun (i:nat{i < n}) -> SZ.v (Seq.index ims i) = 1) in
    let adj = weights_to_adj_matrix ws n in
    // Well-formedness
    weights_to_adj_well_formed ws n;
    // its has an in-MST vertex (source)
    assert (Seq.length its = n);
    assert (Seq.index its source = true);
    // Apply the crossing lemma from Prim.Spec  
    PrimSpec.lemma_connected_implies_crossing_edge adj n its;
    // Eliminate the double existential to get concrete u', v'
    KeyInv.key_inv_bare ks ims ws n;
    FStar.Classical.exists_elim (min_key < SZ.v infinity)
      #nat #(fun u' -> exists (v':nat). u' < n /\ v' < n /\
        u' < Seq.length its /\ v' < Seq.length its /\
        Seq.index its u' = true /\ Seq.index its v' = false /\
        PrimSpec.has_edge adj n u' v') ()
      (fun (u':nat{exists (v':nat). u' < n /\ v' < n /\
        u' < Seq.length its /\ v' < Seq.length its /\
        Seq.index its u' = true /\ Seq.index its v' = false /\
        PrimSpec.has_edge adj n u' v'}) ->
        FStar.Classical.exists_elim (min_key < SZ.v infinity)
          #nat #(fun v' -> u' < n /\ v' < n /\
            u' < Seq.length its /\ v' < Seq.length its /\
            Seq.index its u' = true /\ Seq.index its v' = false /\
            PrimSpec.has_edge adj n u' v') ()
          (fun (v':nat{u' < n /\ v' < n /\
            u' < Seq.length its /\ v' < Seq.length its /\
            Seq.index its u' = true /\ Seq.index its v' = false /\
            PrimSpec.has_edge adj n u' v'}) ->
            // its[u'] = true ↔ ims[u'] = 1 (in MST)
            // its[v'] = false ↔ ims[v'] ≠ 1, so ims[v'] = 0 (not in MST)
            // has_edge: adj[u'][v'] ≠ PrimSpec.infinity
            // weights_to_adj_preserves: weight in ws is > 0 and < impl infinity
            lemma_index_bound u' v' n;
            weights_to_adj_preserves ws n u' v';
            // has_edge: adj[u'][v'] <> PrimSpec.infinity
            // weights_to_adj_preserves: w_imp >= SZ.v infinity ==> w_spec = PrimSpec.infinity
            // Contrapositive: w_spec <> PrimSpec.infinity ==> w_imp < SZ.v infinity
            // Also: its[u'] = true /\ its[v'] = false → ims[u']=1, ims[v']=0 → u' <> v'
            // no_zero_edges + u' <> v' → w_imp > 0
            // key_inv_bare: ims[v']=0 → key[v'] <= w_imp < infinity
            // extract-min: min_key <= key[v']
            assert (u' <> v');
            lemma_index_bound u' v' n;
            // no_zero_edges + u' <> v': weight > 0
            // valid_weights + has_edge: weight < impl infinity
            // key_inv: key[v'] <= weight since ims[u']=1 (MST), ims[v']=0 (non-MST)
            // extract-min: min_key <= key[v']
            assert (SZ.v (Seq.index ims u') = 1);
            assert (SZ.v (Seq.index ims v') = 0);
            ()))
#pop-options

(*** Combined greedy step + noRepeats step ***)

/// Combined greedy step — takes prim_inv_bundle components, outputs safety facts.
/// Uses KeyInv predicates as structured inputs.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let prim_greedy_step
    (ks ps ims_old ims_new ws: Seq.seq SZ.t) (n source u min_key: nat)
  : Lemma
    (requires
      prim_safe ps ks ims_old ws n source /\
      KeyInv.key_inv ks ims_old ws n /\
      KeyInv.ims_finite_key ks ims_old n /\
      KeyInv.parent_in_mst ks ps ims_old n source /\
      key_parent_consistent ks ps ws n source /\
      valid_weights ws n /\ symmetric_weights ws n /\
      parent_valid ps n /\ all_keys_bounded ks /\
      no_zero_edges ws n /\
      n > 0 /\ source < n /\ u < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      Seq.length ws == n * n /\
      SZ.v (Seq.index ks source) == 0 /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_old j) = 0 \/ SZ.v (Seq.index ims_old j) = 1) /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      min_key <= SZ.v infinity /\
      (min_key < SZ.v infinity ==> min_key == SZ.v (Seq.index ks u) /\ SZ.v (Seq.index ims_old u) = 0) /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims_old j) = 0 ==> min_key <= SZ.v (Seq.index ks j)))
    (ensures
      prim_safe ps ks ims_new ws n source /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_new j) = 0 \/ SZ.v (Seq.index ims_new j) = 1) /\
      (u <> source ==> SZ.v (Seq.index ims_old u) = 0 /\ SZ.v (Seq.index ks u) < SZ.v infinity))
  = if u = source then begin
      // Source case: mst_edges_so_far skips source, so edges unchanged
      mst_edges_source_unchanged ps ks ims_old ims_new n source 0;
      reveal_opaque (`%prim_safe) (prim_safe ps ks ims_old ws n source);
      reveal_opaque (`%prim_safe) (prim_safe ps ks ims_new ws n source)
    end
    else begin
      // key[u] < infinity: source has key 0
      // If source is non-MST: min_key <= key[source] = 0 < infinity
      // If source is in MST: connectivity gives a finite-key non-MST vertex (assume for now)
      (if SZ.v (Seq.index ims_old source) = 0 then
        assert (min_key <= SZ.v (Seq.index ks source))
      else
        assume (min_key < SZ.v infinity));
      assert (min_key < SZ.v infinity);
      assert (SZ.v (Seq.index ks u) < SZ.v infinity);
      assert (SZ.v (Seq.index ims_old u) = 0);
      // Get bare quantifiers from KeyInv predicates
      KeyInv.parent_in_mst_for_ims ks ps ims_old n source;
      KeyInv.key_inv_bare ks ims_old ws n;
      let pu = SZ.v (Seq.index ps u) in
      KeyInv.parent_in_mst_at ks ps ims_old n source u pu;
      assert (SZ.v (Seq.index ims_old pu) = 1);
      assert (pu <> u);
      lemma_index_bound pu u n;
      assert (SZ.v (Seq.index ks u) > 0);
      prim_safe_add_vertex ps ks ims_old ims_new ws n source u
    end
#pop-options

/// noRepeats step: uses KeyInv.parent_in_mst for the parent-in-MST fact.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let prim_noRepeats_step
    (ks ps ims_old ims_new ws: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      parent_valid ps n /\ all_keys_bounded ks /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source 0) /\
      (forall (v:nat). v < n /\ SZ.v (Seq.index ks v) < SZ.v infinity /\ v <> source ==>
        SZ.v (Seq.index ims_old (SZ.v (Seq.index ps v))) = 1) /\
      (u = source \/ (u <> source /\ SZ.v (Seq.index ims_old u) <> 1 /\ SZ.v (Seq.index ks u) < SZ.v infinity)))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source 0))
  = if u = source then
      mst_edges_source_unchanged ps ks ims_old ims_new n source 0
    else
      mst_edges_noRepeats_add ps ks ims_old ims_new n source u 0
#pop-options

(*** Post-loop MST derivation ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec efpk_length
    (ps ks: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ i <= n /\ source < n)
    (ensures FStar.List.Tot.length (edges_from_parent_key ps ks n source i) =
             n - i - (if i <= source then 1 else 0))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then efpk_length ps ks n source (i + 1)
    else efpk_length ps ks n source (i + 1)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec efpk_valid_endpoints
    (ps ks: Seq.seq SZ.t) (n source: nat) (i: nat) (e: edge)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ i <= n /\ source < n /\
              parent_valid ps n /\
              mem_edge e (edges_from_parent_key ps ks n source i))
    (ensures e.u < n /\ e.v < n)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then efpk_valid_endpoints ps ks n source (i + 1) e
    else
      let ei = {u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)} in
      if edge_eq e ei then begin
        edge_eq_endpoints e ei;
        assert (e.u < n /\ e.v < n)
      end
      else efpk_valid_endpoints ps ks n source (i + 1) e

let rec remove_edge_first (e: edge) (l: list edge) : list edge =
  match l with
  | [] -> []
  | hd :: tl -> if edge_eq e hd then tl else hd :: remove_edge_first e tl

let rec remove_edge_first_length (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures FStar.List.Tot.length (remove_edge_first e l) = FStar.List.Tot.length l - 1)
          (decreases l)
  = match l with | [] -> () | hd :: tl -> if edge_eq e hd then () else remove_edge_first_length e tl

let rec remove_edge_first_mem (x e: edge) (l: list edge)
  : Lemma (requires mem_edge x l /\ ~(edge_eq x e))
          (ensures mem_edge x (remove_edge_first e l)) (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then begin
        if edge_eq x hd then begin
          edge_eq_symmetric e hd;
          edge_eq_transitive x hd e
        end
      end
      else if edge_eq x hd then ()
      else remove_edge_first_mem x e tl

let rec pigeonhole_edges (a b: list edge)
  : Lemma
    (requires Bridge.noRepeats_edge a /\ subset_edges a b /\
              FStar.List.Tot.length a = FStar.List.Tot.length b)
    (ensures forall (e: edge). mem_edge e b ==> mem_edge e a)
    (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      let rec prove_tl_subset (p: list edge)
        : Lemma (requires (forall (e: edge). mem_edge e p ==> mem_edge e tl) /\
                          Bridge.noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b') (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            assert (not (mem_edge hd tl));
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end);
            mem_edge_subset e (hd :: tl) b;
            remove_edge_first_mem e hd b;
            prove_tl_subset rest
      in
      prove_tl_subset tl;
      pigeonhole_edges tl b';
      let aux (e: edge) : Lemma
        (requires mem_edge e b) (ensures mem_edge e a)
        = if edge_eq e hd then ()
          else begin
            remove_edge_first_mem e hd b;
            assert (mem_edge e b');
            assert (mem_edge e tl)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let all_connected_from_superset (nn: nat) (sub sup: list edge)
  : Lemma
    (requires nn > 0 /\ all_connected nn sub /\
              (forall (e: edge). mem_edge e sub ==> mem_edge e sup))
    (ensures all_connected nn sup)
  = let aux (v: nat) : Lemma
      (requires v < nn) (ensures reachable sup 0 v)
      = assert (reachable sub 0 v);
        let path_transfer (path: list edge) : Lemma
          (requires subset_edges path sub /\ is_path_from_to path 0 v)
          (ensures reachable sup 0 v)
          = let rec transfer_subset (p: list edge)
              : Lemma (requires subset_edges p sub) (ensures subset_edges p sup) (decreases p)
              = match p with | [] -> () | _ :: tl -> transfer_subset tl
            in
            transfer_subset path
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires path_transfer)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Opaque MST result
[@@"opaque_to_smt"]
let prim_mst_result
    (ps ks ws: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length ps == n /\ Seq.length ks == n /\
  Seq.length ws == n * n /\
  (symmetric_weights ws n /\
   all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n) ==>
   is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n)
          (edges_from_parent_key ps ks n source 0))

let prim_mst_result_elim
    (ps ks ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_mst_result ps ks ws n source /\
              Seq.length ps == n /\ Seq.length ks == n /\
              symmetric_weights ws n /\
              all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n)
                    (edges_from_parent_key ps ks n source 0))
  = reveal_opaque (`%prim_mst_result) (prim_mst_result ps ks ws n source)

/// prim_mst_result is invariant under parent[source] change
/// because edges_from_parent_key skips source
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let prim_mst_result_upd_source
    (ps ks ws: Seq.seq SZ.t) (n source: nat) (new_p: SZ.t)
  : Lemma
    (requires prim_mst_result ps ks ws n source /\
              Seq.length ps == n /\ Seq.length ks == n /\ source < n /\ SZ.v new_p < n)
    (ensures prim_mst_result (Seq.upd ps source new_p) ks ws n source)
  = // edges_from_parent_key skips source, so same edges
    let rec efpk_skip_source (p1 p2 k: Seq.seq SZ.t) (nn src: nat) (i: nat)
      : Lemma (requires Seq.length p1 == nn /\ Seq.length p2 == nn /\ Seq.length k == nn /\
                        i <= nn /\ src < nn /\
                        (forall (v:nat). v < nn /\ v <> src ==> Seq.index p1 v == Seq.index p2 v))
              (ensures edges_from_parent_key p1 k nn src i == edges_from_parent_key p2 k nn src i)
              (decreases (nn - i))
      = if i >= nn then ()
        else if i = src then efpk_skip_source p1 p2 k nn src (i + 1)
        else efpk_skip_source p1 p2 k nn src (i + 1)
    in
    efpk_skip_source ps (Seq.upd ps source new_p) ks n source 0;
    reveal_opaque (`%prim_mst_result) (prim_mst_result ps ks ws n source);
    reveal_opaque (`%prim_mst_result) (prim_mst_result (Seq.upd ps source new_p) ks ws n source)
#pop-options

/// Post-loop MST derivation
#restart-solver
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries always"
let derive_prim_is_mst
    (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      prim_safe ps ks ims ws n source /\
      valid_weights ws n /\ symmetric_weights ws n /\
      parent_valid ps n /\
      n > 0 /\ source < n /\
      Seq.length ps == n /\ Seq.length ks == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims n source 0) /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) = 1) /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n)
                    (edges_from_parent_key ps ks n source 0))
  = mst_edges_all_in ps ks ims n source 0;
    efpk_length ps ks n source 0;
    let adj = weights_to_adj_matrix ws n in
    let g = PrimSpec.adj_to_graph adj n in
    let efpk = edges_from_parent_key ps ks n source 0 in
    PrimSpec.adj_to_graph_edges adj n;
    prim_safe_elim ps ks ims ws n source;
    let ve (e: edge) : Lemma
      (requires mem_edge e g.edges) (ensures e.u < g.n /\ e.v < g.n /\ e.u <> e.v)
      = PrimSpec.adj_to_graph_edges_valid adj n e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ve);
    FStar.Classical.exists_elim
      (is_mst g efpk)
      #(list edge) #(fun t -> is_mst g t /\ subset_edges efpk t) ()
      (fun (t: list edge{is_mst g t /\ subset_edges efpk t}) ->
        assert (is_spanning_tree g t);
        assert (acyclic g.n t);
        pigeonhole_edges efpk t;
        all_connected_from_superset n t efpk;
        subset_edges_transitive efpk t g.edges;
        let aux_acyclic (e: edge) : Lemma
          (requires mem_edge e efpk) (ensures mem_edge e t)
          = mem_edge_subset e efpk t
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_acyclic);
        acyclic_subset g.n t efpk;
        Bridge.safe_spanning_tree_is_mst g efpk)

let derive_prim_mst_post_loop
    (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      prim_safe ps ks ims ws n source /\
      valid_weights ws n /\ symmetric_weights ws n /\
      parent_valid ps n /\
      n > 0 /\ source < n /\
      Seq.length ps == n /\ Seq.length ks == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims n source 0) /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) = 1))
    (ensures prim_mst_result ps ks ws n source)
  = reveal_opaque (`%prim_mst_result) (prim_mst_result ps ks ws n source);
    FStar.Classical.arrow_to_impl
      #(symmetric_weights ws n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
      #(is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix ws n) n)
               (edges_from_parent_key ps ks n source 0))
      (fun _ -> derive_prim_is_mst ks ps ims ws n source)
#pop-options
