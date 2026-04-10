module AVCBridgeLemmas

open FStar.Mul
open FStar.List.Tot
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec
module Lemmas = CLRS.Ch35.VertexCover.Lemmas

let to_int_seq (s: Seq.seq (option Int32.t)) : Seq.seq int =
  Seq.init (Seq.length s) (fun i ->
    match Seq.index s i with
    | Some x -> Int32.v x
    | None -> 0)

let to_int_seq_length (s: Seq.seq (option Int32.t))
  : Lemma (ensures Seq.length (to_int_seq s) = Seq.length s)
          [SMTPat (Seq.length (to_int_seq s))]
  = ()

let to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.index (to_int_seq s) i = AVCHelper.seq_val s i)
          [SMTPat (Seq.index (to_int_seq s) i)]
  = ()

#push-options "--z3rlimit 80"
private
let cover_pointwise
  (sa sc: Seq.seq (option Int32.t)) (n u v: nat)
  : Lemma
    (requires AVCHelper.outer_inv_pure sa sc n n /\
              u < n /\ v < n /\ u < v /\
              Seq.index (to_int_seq sa) (u * n + v) <> 0)
    (ensures Seq.index (to_int_seq sc) u <> 0 \/ Seq.index (to_int_seq sc) v <> 0)
    [SMTPat (Seq.index (to_int_seq sa) (u * n + v));
     SMTPat (Seq.index (to_int_seq sc) u)]
  = to_int_seq_index sa (u * n + v);
    to_int_seq_index sc u;
    to_int_seq_index sc v
#pop-options

#push-options "--z3rlimit 200"
let outer_inv_implies_is_cover
  (sa sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n)
          (ensures Spec.is_cover (to_int_seq sa) (to_int_seq sc) n n 0)
  = to_int_seq_length sa;
    to_int_seq_length sc
#pop-options

let binary_implies_binary_int
  (sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.binary sc n /\ Seq.length sc = n)
          (ensures forall (i: nat). i < n ==>
            (Seq.index (to_int_seq sc) i = 0 \/ Seq.index (to_int_seq sc) i = 1))
  = ()

let bridge_full
  (sa sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n)
          (ensures (
            let s_adj = to_int_seq sa in
            let s_cover = to_int_seq sc in
            Spec.is_cover s_adj s_cover n n 0 /\
            (forall (i: nat). i < n ==>
              (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
            (exists (opt: nat). Spec.min_vertex_cover_size s_adj n opt)))
  = outer_inv_implies_is_cover sa sc n;
    binary_implies_binary_int sc n;
    Lemmas.min_cover_exists (to_int_seq sa) n

#push-options "--z3rlimit 80"
let bridge_apply_approximation
  (sa sc: Seq.seq (option Int32.t)) (n: nat) (m: list Spec.edge)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n /\
                    AVCHelper.matching_inv_opt sa sc n m)
          (ensures (
            let s_adj = to_int_seq sa in
            let s_cover = to_int_seq sc in
            forall (opt: nat). Spec.min_vertex_cover_size s_adj n opt ==>
              Spec.count_cover (Spec.seq_to_cover_fn s_cover n) n <= 2 * opt))
  = let s_adj = to_int_seq sa in
    let s_cover = to_int_seq sc in
    to_int_seq_length sa;
    to_int_seq_length sc;
    binary_implies_binary_int sc n;
    let bound (c_opt: Spec.cover_fn)
      : Lemma (requires Spec.is_valid_graph_cover s_adj n c_opt)
              (ensures Spec.count_cover (Spec.seq_to_cover_fn s_cover n) n <= 2 * Spec.count_cover c_opt n) =
      Lemmas.approximation_ratio_theorem s_adj s_cover n m c_opt
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bound)
#pop-options

#push-options "--z3rlimit 80"
let bridge_derive_even_count
  (sa sc: Seq.seq (option Int32.t)) (n: nat) (m: list Spec.edge)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n /\
                    AVCHelper.matching_inv_opt sa sc n m)
          (ensures (
            let s_cover = to_int_seq sc in
            exists (k: nat). Spec.count_cover (Spec.seq_to_cover_fn s_cover n) n = 2 * k))
  = let s_adj = to_int_seq sa in
    let s_cover = to_int_seq sc in
    to_int_seq_length sa;
    to_int_seq_length sc;
    binary_implies_binary_int sc n;
    let c_alg = Spec.seq_to_cover_fn s_cover n in
    let c_m : Spec.cover_fn = fun (x:nat) -> existsb (fun (e: Spec.edge) -> Spec.edge_uses_vertex e x) m in
    Lemmas.count_cover_ext c_alg c_m n;
    Lemmas.matching_cover_size m n
#pop-options
