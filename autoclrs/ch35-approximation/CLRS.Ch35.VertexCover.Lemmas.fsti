module CLRS.Ch35.VertexCover.Lemmas

(**
 * Proofs of lemmas about APPROX-VERTEX-COVER (CLRS Chapter 35).
 *
 * Includes counting lemmas, matching arguments, CLRS Theorem 35.1,
 * and the connection from Pulse's is_cover to the pure specification.
 *
 * 0 admits. Fully proven.
 *)

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch35.VertexCover.Spec

(*** Counting lemmas ***)

val count_cover_ext (c1 c2: cover_fn) (n: nat)
  : Lemma (requires forall (x: nat). x < n ==> (c1 x == c2 x))
          (ensures count_cover c1 n == count_cover c2 n)

val count_zero (n: nat) 
  : Lemma (ensures count_cover (fun (_ : nat) -> false) n == 0)

val count_single (v: nat) (n: nat)
  : Lemma (requires v < n)
          (ensures count_cover (fun (x:nat) -> x = v) n == 1)

val count_cover_mono (c1 c2: cover_fn) (n: nat)
  : Lemma (requires forall (v: nat). v < n /\ c2 v ==> c1 v)
          (ensures count_cover c1 n >= count_cover c2 n)

val count_split (c: cover_fn) (u v: nat) (n: nat)
  : Lemma (requires u < n /\ v < n /\ u <> v)
          (ensures (let c' : cover_fn = fun (x:nat) -> c x && not (x = u || x = v) in
                   count_cover c n >= 
                   (if c u then 1 else 0) + (if c v then 1 else 0) + count_cover c' n))

(*** Matching lower bound ***)

val matching_lower_bound (c: cover_fn) (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              is_valid_cover_for_edges c m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures count_cover c n >= List.Tot.length m)

(*** Algorithm cover size = 2 * matching size ***)

val matching_cover_size (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures 
              count_cover (fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m) n ==
              2 * List.Tot.length m)

(*** CLRS Theorem 35.1: 2-approximation ***)

val theorem_35_1 
  (m: list edge) (c_opt: cover_fn) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)) /\
              is_valid_cover_for_edges c_opt m)
          (ensures (
              let c_alg : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m in
              count_cover c_alg n == 2 * List.Tot.length m /\
              count_cover c_opt n >= List.Tot.length m /\
              count_cover c_alg n <= 2 * count_cover c_opt n))

(*** Connection to Pulse implementation ***)

val pulse_cover_is_valid (s_adj s_cover: seq int) (n: nat)
  : Lemma (requires is_cover s_adj s_cover n n 0 /\ Seq.length s_cover = n)
          (ensures is_valid_graph_cover s_adj n (seq_to_cover_fn s_cover n))

val extract_edges_contains (adj: seq int) (n: nat) (u v u' v': nat)
  : Lemma (requires Seq.length adj = n * n /\
                    u' < n /\ v' < n /\ u' < v' /\
                    Seq.index adj (u' * n + v') <> 0 /\
                    u <= u' /\ (u < u' \/ v <= v'))
          (ensures memP (u', v') (extract_edges adj n u v))

val valid_cover_covers_matching (adj: seq int) (n: nat) (c: cover_fn) (m: list edge)
  : Lemma (requires is_valid_graph_cover adj n c /\
                    Seq.length adj = n * n /\
                    (forall (e: edge). memP e m ==>
                      (let (u, v) = e in u < n /\ v < n /\ u < v /\ Seq.index adj (u * n + v) <> 0)))
          (ensures is_valid_cover_for_edges c m)

(*** Existence of minimum vertex cover ***)

// The trivial "all vertices" cover is valid for any graph
val all_true_is_valid (adj: seq int) (n: nat)
  : Lemma (requires Seq.length adj = n * n)
          (ensures is_valid_graph_cover adj n (fun (_ : nat) -> true))

// The count of the all-true cover is exactly n
val count_all_true (n: nat)
  : Lemma (ensures count_cover (fun (_ : nat) -> true) n = n)

// Every finite graph has a minimum vertex cover.
// This makes the 2-approximation guarantee non-vacuous.
val min_cover_exists (adj: seq int) (n: nat)
  : Lemma (requires Seq.length adj = n * n)
          (ensures exists (opt: nat). min_vertex_cover_size adj n opt)

(*** 2-Approximation Ratio Theorem ***)

val approximation_ratio_theorem (s_adj s_cover: seq int) (n: nat) (m: list edge) (c_opt: cover_fn)
  : Lemma (requires
            Seq.length s_cover = n /\
            Seq.length s_adj = n * n /\
            (forall (i: nat). i < n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
            is_valid_graph_cover s_adj n c_opt /\
            pairwise_disjoint m /\
            (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)) /\
            (forall (e: edge). memP e m ==> (let (u, v) = e in u < v /\ Seq.index s_adj (u * n + v) <> 0)) /\
            (forall (x: nat). x < n ==> ((Seq.index s_cover x <> 0) == existsb (fun e -> edge_uses_vertex e x) m)))
          (ensures count_cover (seq_to_cover_fn s_cover n) n <= 2 * count_cover c_opt n)
