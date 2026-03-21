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

/// Helper: u < n /\ v < n ==> u * n + v < n * n
let index_bound (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0) (ensures u * n + v < n * n)
  = FStar.Math.Lemmas.lemma_mult_lt_right n u n

let lemma_index_in_bounds (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
          (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))
  = ()

// valid_endpoints is defined transparently in the .fsti

// edges_from_arrays is defined transparently in the .fsti

// Transfer lemma for extensional array equality
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
let valid_endpoints_ext (seu sev seu' sev': Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\
                    ec <= n /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    Seq.length seu' == n /\ Seq.length sev' == n /\
                    (forall (k:nat). k < ec ==> Seq.index seu' k == Seq.index seu k /\
                                                  Seq.index sev' k == Seq.index sev k))
          (ensures valid_endpoints seu' sev' n ec)
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n ec);
    reveal_opaque (`%valid_endpoints) (valid_endpoints seu' sev' n ec)
#pop-options

// Extending valid_endpoints by one: if valid at ec and the new entry is valid, then valid at ec+1
let valid_endpoints_extend
  (seu sev seu' sev': Seq.seq int) (n ec: nat) (vbu vbv: nat)
  : Lemma
    (requires
      valid_endpoints seu sev n ec /\
      ec + 1 <= n /\
      Seq.length seu' == n /\ Seq.length sev' == n /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
      vbu < n /\ vbv < n)
    (ensures valid_endpoints seu' sev' n (ec + 1))
  = // For k < ec: old valid_endpoints + array agreement
    assert (forall (k:nat). k < ec ==>
      Seq.index seu' k >= 0 /\ Seq.index seu' k < n /\
      Seq.index sev' k >= 0 /\ Seq.index sev' k < n);
    // For k = ec: explicit
    assert (Seq.index seu' ec >= 0 /\ Seq.index seu' ec < n);
    assert (Seq.index sev' ec >= 0 /\ Seq.index sev' ec < n)

// valid_endpoints implies all edges have valid vertices (< n)
let rec valid_endpoints_implies_all_edges_valid
  (seu sev: Seq.seq int) (n ec: nat) (i: nat{i <= ec})
  : Lemma (requires valid_endpoints seu sev n ec)
          (ensures UF.all_edges_valid (edges_from_arrays seu sev ec i) n)
          (decreases (ec - i))
  = if i >= ec then ()
    else valid_endpoints_implies_all_edges_valid seu sev n ec (i + 1)

// Extensionality: edges_from_arrays depends only on values in [i, ec)
let rec edges_from_arrays_ext (seu1 sev1 seu2 sev2: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      ec <= Seq.length seu1 /\ ec <= Seq.length sev1 /\
      ec <= Seq.length seu2 /\ ec <= Seq.length sev2 /\
      (forall (k:nat). k < ec ==> Seq.index seu1 k >= 0 /\ Seq.index sev1 k >= 0) /\
      (forall (k:nat). k < ec ==> Seq.index seu2 k >= 0 /\ Seq.index sev2 k >= 0) /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu1 k == Seq.index seu2 k /\ Seq.index sev1 k == Seq.index sev2 k))
    (ensures edges_from_arrays seu1 sev1 ec i == edges_from_arrays seu2 sev2 ec i)
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_ext seu1 sev1 seu2 sev2 ec (i + 1)

// Extension: adding one element at index ec appends to the edge list
let rec edges_from_arrays_extend (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec}) (eu ev: nat)
  : Lemma
    (requires
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      Seq.index seu ec == eu /\ Seq.index sev ec == ev)
    (ensures edges_from_arrays seu sev (ec + 1) i ==
             FStar.List.Tot.append (edges_from_arrays seu sev ec i) [{u = eu; v = ev; w = 1}])
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_extend seu sev ec (i + 1) eu ev

// Length of edges_from_arrays
let rec edges_from_arrays_length (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
    (ensures FStar.List.Tot.length (edges_from_arrays seu sev ec i) = ec - i)
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_length seu sev ec (i + 1)

// Postcondition: result forms a forest (acyclic edge set)
let result_is_forest (seu sev: Seq.seq int) (n ec: nat) : prop =
  valid_endpoints seu sev n ec /\
  ec <= n - 1 /\
  (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
  KSpec.is_forest (edges_from_arrays seu sev ec 0) n

// Forest property is established from the loop invariant which tracks is_forest.
let lemma_kruskal_maintains_forest
  (seu: Seq.seq int) (sev: Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\ ec <= n - 1 /\
                    (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
                    KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
          (ensures result_is_forest seu sev n ec)
  = ()

// Track that each selected edge has a positive entry in the adjacency matrix.
// This connects imperative edge arrays to the graph structure (needed for subset_edges).
[@@"opaque_to_smt"]
let edges_adj_pos (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop =
  Seq.length sadj == n * n /\ n > 0 /\
  ec <= Seq.length seu /\ ec <= Seq.length sev /\
  (forall (k:nat). k < ec ==>
    Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
    Seq.index seu k < n /\ Seq.index sev k < n /\
    adj_weight sadj n (Seq.index seu k) (Seq.index sev k) > 0)

let edges_adj_pos_init (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat)
  : Lemma (requires Seq.length sadj == n * n /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures edges_adj_pos sadj seu sev n 0)
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n 0)

let edges_adj_pos_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires edges_adj_pos sadj seu sev n ec)
          (ensures Seq.length sadj == n * n /\ n > 0 /\
                   ec <= Seq.length seu /\ ec <= Seq.length sev /\
                   (forall (k:nat). k < ec ==>
                     Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                     Seq.index seu k < n /\ Seq.index sev k < n /\
                     adj_weight sadj n (Seq.index seu k) (Seq.index sev k) > 0))
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n ec)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
let edges_adj_pos_ext (sadj: Seq.seq int) (seu sev seu' sev': Seq.seq int) (n ec: nat)
  : Lemma (requires edges_adj_pos sadj seu sev n ec /\
                    ec <= n /\
                    Seq.length sadj == n * n /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    Seq.length seu' == n /\ Seq.length sev' == n /\
                    (forall (k:nat). k < ec ==> Seq.index seu' k == Seq.index seu k /\
                                                  Seq.index sev' k == Seq.index sev k))
          (ensures edges_adj_pos sadj seu' sev' n ec)
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n ec);
    reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu' sev' n ec)
#pop-options

let edges_adj_pos_step
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
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n ec);
    reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu' sev' n ec')

// Strengthened postcondition: forest + edges come from adjacency matrix
let result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop =
  result_is_forest seu sev n ec /\
  edges_adj_pos sadj seu sev n ec

// Elim lemma for external consumers
let result_is_forest_adj_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
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
  = edges_adj_pos_elim sadj seu sev n ec

// Structural elim: expose is_forest from result_is_forest_adj
let result_is_forest_adj_forest_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures
      ec <= n - 1 /\ n > 0 /\
      Seq.length seu == n /\ Seq.length sev == n /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
  = ()

// Intro lemma: construct result_is_forest_adj from its components
let result_is_forest_adj_intro (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest seu sev n ec /\ edges_adj_pos sadj seu sev n ec)
    (ensures result_is_forest_adj sadj seu sev n ec)
  = ()

let result_is_forest_adj_adj_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures edges_adj_pos sadj seu sev n ec)
  = ()

// Edges with actual weights from the adjacency matrix
// (edges_from_arrays uses weight 1 for internal forest tracking;
//  this version uses adj[u*n+v] for MST weight reasoning)
// weighted_edges_from_arrays is defined transparently in the .fsti

/// Weighted edges extensional equality: same arrays for first ec elements gives same list
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec weighted_edges_from_arrays_ext
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
    (decreases (ec - i))
  = if i >= ec then ()
    else weighted_edges_from_arrays_ext sadj seu1 sev1 seu2 sev2 n ec (i + 1)
#pop-options

/// Weighted edges extend by one edge
#push-options "--fuel 2 --ifuel 1 --z3rlimit 800 "
let rec weighted_edges_from_arrays_extend
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
    (decreases (ec - i))
  = if i >= ec then ()
    else weighted_edges_from_arrays_extend sadj seu sev n ec (i + 1) eu ev
#pop-options

/// subset_edges (hd :: tl) s ==> subset_edges (tl @ [hd]) s
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec subset_edges_cons_to_append (hd: edge) (tl: list edge) (s: list edge)
  : Lemma (requires subset_edges (hd :: tl) s)
          (ensures subset_edges (FStar.List.Tot.append tl [hd]) s)
          (decreases tl)
  = match tl with
    | [] -> ()
    | _ :: rest -> subset_edges_cons_to_append hd rest s
#pop-options

module Bridge = CLRS.Ch23.Kruskal.Bridge
let rec aed_eq_noRepeats (es: list edge)
  : Lemma (ensures all_edges_distinct es == Bridge.noRepeats_edge es)
          (decreases es)
  = match es with | [] -> () | _ :: tl -> aed_eq_noRepeats tl
