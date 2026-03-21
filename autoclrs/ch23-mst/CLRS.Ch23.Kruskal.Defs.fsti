module CLRS.Ch23.Kruskal.Defs
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq
module MSTSpec = CLRS.Ch23.MST.Spec
module KSpec = CLRS.Ch23.Kruskal.Spec
module UF = CLRS.Ch23.Kruskal.UF

/// Safe indexing into adjacency matrix — bundles the nonlinear index bound
let adj_weight (sadj: Seq.seq int) (n: nat{n > 0}) (u: nat{u < n}) (v: nat{v < n /\ Seq.length sadj == n * n}) : int
  = Seq.index sadj (u * n + v)

let valid_parents (sparent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) < n)

/// Helper: u < n /\ v < n ==> u * n + v < n * n
val index_bound (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0) (ensures u * n + v < n * n)

val lemma_index_in_bounds (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
          (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))

// Valid endpoints: all selected edges have valid vertex indices
let valid_endpoints (seu sev: Seq.seq int) (n ec: nat) : prop =
  ec <= n /\
  Seq.length seu == n /\ Seq.length sev == n /\
  (forall (k: nat). k < ec ==>
    Seq.index seu k >= 0 /\ Seq.index seu k < n /\
    Seq.index sev k >= 0 /\ Seq.index sev k < n)

// Convert imperative result to edge list for MST spec
let rec edges_from_arrays (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Pure (list MSTSpec.edge)
    (requires
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
    (ensures fun _ -> True)
    (decreases (ec - i))
  = if i >= ec then []
    else
      let u_int = Seq.index seu i in
      let v_int = Seq.index sev i in
      {u = u_int; v = v_int; w = 1} :: edges_from_arrays seu sev ec (i + 1)

val valid_endpoints_ext (seu sev seu' sev': Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\
                    ec <= n /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    Seq.length seu' == n /\ Seq.length sev' == n /\
                    (forall (k:nat). k < ec ==> Seq.index seu' k == Seq.index seu k /\
                                                  Seq.index sev' k == Seq.index sev k))
          (ensures valid_endpoints seu' sev' n ec)

val valid_endpoints_extend
  (seu sev seu' sev': Seq.seq int) (n ec: nat) (vbu vbv: nat)
  : Lemma
    (requires
      valid_endpoints seu sev n ec /\
      ec + 1 <= n /\
      Seq.length seu == n /\ Seq.length sev == n /\
      Seq.length seu' == n /\ Seq.length sev' == n /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
      vbu < n /\ vbv < n)
    (ensures valid_endpoints seu' sev' n (ec + 1))

val valid_endpoints_implies_all_edges_valid
  (seu sev: Seq.seq int) (n ec: nat) (i: nat{i <= ec})
  : Lemma (requires valid_endpoints seu sev n ec /\
                    ec <= Seq.length seu /\ ec <= Seq.length sev /\
                    (forall (k:nat). k < ec ==>
                      Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
          (ensures UF.all_edges_valid (edges_from_arrays seu sev ec i) n)

// Extensionality: edges_from_arrays depends only on values in [i, ec)
val edges_from_arrays_ext (seu1 sev1 seu2 sev2: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      ec <= Seq.length seu1 /\ ec <= Seq.length sev1 /\
      ec <= Seq.length seu2 /\ ec <= Seq.length sev2 /\
      (forall (k:nat). k < ec ==> Seq.index seu1 k >= 0 /\ Seq.index sev1 k >= 0) /\
      (forall (k:nat). k < ec ==> Seq.index seu2 k >= 0 /\ Seq.index sev2 k >= 0) /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu1 k == Seq.index seu2 k /\ Seq.index sev1 k == Seq.index sev2 k))
    (ensures edges_from_arrays seu1 sev1 ec i == edges_from_arrays seu2 sev2 ec i)

// Extension: adding one element at index ec appends to the edge list
val edges_from_arrays_extend (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec}) (eu ev: nat)
  : Lemma
    (requires
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      Seq.index seu ec == eu /\ Seq.index sev ec == ev)
    (ensures edges_from_arrays seu sev (ec + 1) i ==
             FStar.List.Tot.append (edges_from_arrays seu sev ec i) [{u = eu; v = ev; w = 1}])

// Length of edges_from_arrays
val edges_from_arrays_length (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
    (ensures FStar.List.Tot.length (edges_from_arrays seu sev ec i) = ec - i)

// Postcondition: result forms a forest (acyclic edge set)
val result_is_forest (seu sev: Seq.seq int) (n ec: nat) : prop

val lemma_kruskal_maintains_forest
  (seu: Seq.seq int) (sev: Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\ ec <= n - 1 /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
                    KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
          (ensures result_is_forest seu sev n ec)

// Each selected edge has a positive entry in the adjacency matrix
val edges_adj_pos (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop

val edges_adj_pos_init (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat)
  : Lemma (requires Seq.length sadj == n * n /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures edges_adj_pos sadj seu sev n 0)

val edges_adj_pos_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires edges_adj_pos sadj seu sev n ec)
          (ensures Seq.length sadj == n * n /\ n > 0 /\
                   ec <= Seq.length seu /\ ec <= Seq.length sev /\
                   (forall (k:nat). k < ec ==>
                     Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                     Seq.index seu k < n /\ Seq.index sev k < n /\
                     adj_weight sadj n (Seq.index seu k) (Seq.index sev k) > 0))

val edges_adj_pos_ext (sadj: Seq.seq int) (seu sev seu' sev': Seq.seq int) (n ec: nat)
  : Lemma (requires edges_adj_pos sadj seu sev n ec /\
                    ec <= n /\
                    Seq.length sadj == n * n /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    Seq.length seu' == n /\ Seq.length sev' == n /\
                    (forall (k:nat). k < ec ==> Seq.index seu' k == Seq.index seu k /\
                                                  Seq.index sev' k == Seq.index sev k))
          (ensures edges_adj_pos sadj seu' sev' n ec)

val edges_adj_pos_step
  (sadj: Seq.seq int) (seu sev seu' sev': Seq.seq int) (n ec ec': nat)
  (vbu vbv: nat) (should_add: bool)
  : Lemma
    (requires
      edges_adj_pos sadj seu sev n ec /\
      Seq.length sadj == n * n /\ n > 0 /\
      vbu < n /\ vbv < n /\
      ec' == (if should_add then ec + 1 else ec) /\
      Seq.length seu' == Seq.length seu /\ Seq.length sev' == Seq.length sev /\
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      (should_add ==> Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
                       adj_weight sadj n vbu vbv > 0))
    (ensures edges_adj_pos sadj seu' sev' n ec')

// Strengthened postcondition: forest + edges come from adjacency matrix
val result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop

val result_is_forest_adj_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures
      ec <= n - 1 /\
      Seq.length seu == n /\ Seq.length sev == n /\
      Seq.length sadj == n * n /\ n > 0 /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index seu k < n /\
        Seq.index sev k >= 0 /\ Seq.index sev k < n /\
        adj_weight sadj n (Seq.index seu k) (Seq.index sev k) > 0))

val result_is_forest_adj_forest_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures
      ec <= n - 1 /\ n > 0 /\
      Seq.length seu == n /\ Seq.length sev == n /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n)

/// Intro lemma: construct result_is_forest_adj from its components
val result_is_forest_adj_intro (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest seu sev n ec /\ edges_adj_pos sadj seu sev n ec)
    (ensures result_is_forest_adj sadj seu sev n ec)

/// Extract edges_adj_pos from result_is_forest_adj
val result_is_forest_adj_adj_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures edges_adj_pos sadj seu sev n ec)

/// Postcondition predicate for do_union
let do_union_post (sparent sparent': Seq.seq SZ.t) (root_u root_v n: nat) : prop =
  valid_parents sparent' n /\
  Seq.length sparent == n /\
  Seq.length sparent' == n /\
  (root_u < n ==> SZ.v (Seq.index sparent' root_u) == root_v) /\
  (forall (i: nat). (i < n /\ i <> root_u) ==>
    Seq.index sparent' i == Seq.index sparent i)

/// Edges with actual weights from the adjacency matrix
let rec weighted_edges_from_arrays
  (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat) (ec: nat) (i: nat{i <= ec})
  : Pure (list edge)
    (requires
      n > 0 /\ ec <= Seq.length seu /\ ec <= Seq.length sev /\
      Seq.length sadj == n * n /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n))
    (ensures fun r -> FStar.List.Tot.length r = ec - i)
    (decreases (ec - i))
  = if i >= ec then []
    else
      let u_int = Seq.index seu i in
      let v_int = Seq.index sev i in
      let w = Seq.index sadj (u_int * n + v_int) in
      {u = u_int; v = v_int; w = w} :: weighted_edges_from_arrays sadj seu sev n ec (i + 1)

val weighted_edges_from_arrays_ext
    (sadj: Seq.seq int) (seu1 sev1 seu2 sev2: Seq.seq int) (n: nat) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu1 /\ ec <= Seq.length sev1 /\
      ec <= Seq.length seu2 /\ ec <= Seq.length sev2 /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu1 k >= 0 /\ Seq.index sev1 k >= 0 /\
        Seq.index seu1 k < n /\ Seq.index sev1 k < n /\
        Seq.index seu2 k >= 0 /\ Seq.index sev2 k >= 0 /\
        Seq.index seu2 k < n /\ Seq.index sev2 k < n) /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu1 k == Seq.index seu2 k /\ Seq.index sev1 k == Seq.index sev2 k))
    (ensures weighted_edges_from_arrays sadj seu1 sev1 n ec i ==
             weighted_edges_from_arrays sadj seu2 sev2 n ec i)

val weighted_edges_from_arrays_extend
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat) (ec: nat) (i: nat{i <= ec})
    (eu: nat{eu < n}) (ev: nat{ev < n})
  : Lemma
    (requires
      n > 0 /\ ec < Seq.length seu /\ ec < Seq.length sev /\
      Seq.length sadj == n * n /\
      Seq.index seu ec == eu /\ Seq.index sev ec == ev /\
      (forall (k:nat). i <= k /\ k < ec + 1 ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n))
    (ensures
      weighted_edges_from_arrays sadj seu sev n (ec + 1) i ==
        FStar.List.Tot.append
          (weighted_edges_from_arrays sadj seu sev n ec i)
          [{u = eu; v = ev; w = adj_weight sadj n eu ev}])

/// subset_edges (hd :: tl) s ==> subset_edges (tl @ [hd]) s
val subset_edges_cons_to_append (hd: edge) (tl: list edge) (s: list edge)
  : Lemma (requires subset_edges (hd :: tl) s)
          (ensures subset_edges (FStar.List.Tot.append tl [hd]) s)

module Bridge = CLRS.Ch23.Kruskal.Bridge
/// all_edges_distinct and Bridge.noRepeats_edge are identical
val aed_eq_noRepeats (es: list edge)
  : Lemma (ensures all_edges_distinct es == Bridge.noRepeats_edge es)
