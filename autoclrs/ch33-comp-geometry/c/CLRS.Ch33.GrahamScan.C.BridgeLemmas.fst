(*
   Bridge lemmas connecting c2pulse postconditions (Int32.t arrays)
   to CLRS.Ch33.GrahamScan.Spec functions (int sequences).

   c2pulse operates on Seq.seq (option Int32.t); the Impl.fsti specs
   use Seq.seq int. These lemmas prove that the c2pulse ensures
   imply the corresponding spec-level properties.
*)

module CLRS.Ch33.GrahamScan.C.BridgeLemmas
open FStar.Mul
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

(* Convert c2pulse option-wrapped Int32 sequence to plain int sequence.
   Requires all elements are Some (well-initialized). *)
let int_val (x: Int32.t) : int = Int32.v x

let to_int_seq
  (s: Seq.seq (option Int32.t) {forall (i: nat). i < Seq.length s ==> Some? (Seq.index s i)})
  : GTot (Seq.seq int)
  = Seq.init_ghost (Seq.length s) (fun i -> int_val (Some?.v (Seq.index s i)))

let to_int_seq_length
  (s: Seq.seq (option Int32.t) {forall (i: nat). i < Seq.length s ==> Some? (Seq.index s i)})
  : Lemma (Seq.length (to_int_seq s) == Seq.length s)
  = ()

(* The c2pulse forall ensures for find_bottom implies is_bottommost on int sequences. *)
let find_bottom_is_bottommost_bridge
  (xs_opt: Seq.seq (option Int32.t))
  (ys_opt: Seq.seq (option Int32.t))
  (m: nat)
  : Lemma
    (requires
      Seq.length xs_opt == Seq.length ys_opt /\
      m < Seq.length xs_opt /\
      (forall (i: nat). i < Seq.length xs_opt ==> Some? (Seq.index xs_opt i)) /\
      (forall (i: nat). i < Seq.length ys_opt ==> Some? (Seq.index ys_opt i)) /\
      (forall (k: nat). k < Seq.length xs_opt ==>
        int_val (Some?.v (Seq.index ys_opt m)) < int_val (Some?.v (Seq.index ys_opt k)) \/
        (int_val (Some?.v (Seq.index ys_opt m)) = int_val (Some?.v (Seq.index ys_opt k)) /\
         int_val (Some?.v (Seq.index xs_opt m)) <= int_val (Some?.v (Seq.index xs_opt k)))))
    (ensures (
      let sxs = to_int_seq xs_opt in
      let sys = to_int_seq ys_opt in
      is_bottommost sxs sys m))
  = ()

(* polar_cmp_spec is cross_product_spec applied to array elements (by definition). *)
let polar_cmp_bridge
  (sxs sys: Seq.seq int)
  (p0 a b: nat)
  : Lemma
    (requires
      p0 < Seq.length sxs /\ a < Seq.length sxs /\ b < Seq.length sxs /\
      Seq.length sys == Seq.length sxs)
    (ensures
      polar_cmp_spec sxs sys p0 a b ==
      cross_product_spec (Seq.index sxs p0) (Seq.index sys p0)
                         (Seq.index sxs a) (Seq.index sys a)
                         (Seq.index sxs b) (Seq.index sys b))
  = ()

(* The c2pulse cross_product_spec ensures for polar_cmp, when lifted through
   to_int_seq, equals polar_cmp_spec on the int sequences. *)
let polar_cmp_c2pulse_bridge
  (xs_opt ys_opt: Seq.seq (option Int32.t))
  (p0 a b: nat)
  : Lemma
    (requires
      Seq.length xs_opt == Seq.length ys_opt /\
      p0 < Seq.length xs_opt /\ a < Seq.length xs_opt /\ b < Seq.length xs_opt /\
      (forall (i: nat). i < Seq.length xs_opt ==> Some? (Seq.index xs_opt i)) /\
      (forall (i: nat). i < Seq.length ys_opt ==> Some? (Seq.index ys_opt i)))
    (ensures (
      let sxs = to_int_seq xs_opt in
      let sys = to_int_seq ys_opt in
      polar_cmp_spec sxs sys p0 a b ==
      cross_product_spec
        (int_val (Some?.v (Seq.index xs_opt p0)))
        (int_val (Some?.v (Seq.index ys_opt p0)))
        (int_val (Some?.v (Seq.index xs_opt a)))
        (int_val (Some?.v (Seq.index ys_opt a)))
        (int_val (Some?.v (Seq.index xs_opt b)))
        (int_val (Some?.v (Seq.index ys_opt b)))))
  = ()

(* The c2pulse hull write property (hull[return-1] = p_idx, below preserved)
   partially captures scan_step_sz_spec. This lemma shows that if the
   pop_while result is new_top, writing p_idx at new_top gives the same
   sequence as Seq.upd hull new_top p_idx. *)
let scan_step_hull_write_bridge
  (hull: Seq.seq SZ.t)
  (new_top: nat)
  (p_idx: SZ.t)
  : Lemma
    (requires new_top < Seq.length hull)
    (ensures (
      let hull' = Seq.upd hull new_top p_idx in
      Seq.index hull' new_top == p_idx /\
      (forall (k: nat). k < new_top ==> Seq.index hull' k == Seq.index hull k) /\
      (forall (k: nat). k > new_top /\ k < Seq.length hull ==>
        Seq.index hull' k == Seq.index hull k)))
  = ()
