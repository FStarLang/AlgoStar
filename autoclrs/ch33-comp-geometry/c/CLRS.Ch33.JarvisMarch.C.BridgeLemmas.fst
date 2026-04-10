(*
   Bridge lemmas connecting c2pulse postconditions (Int32.t arrays)
   to CLRS.Ch33.JarvisMarch.Spec functions (int sequences).

   c2pulse operates on Seq.seq (option Int32.t); the Impl.fsti specs
   use Seq.seq int. These lemmas prove that the c2pulse ensures
   imply the corresponding spec-level properties.
*)

module CLRS.Ch33.JarvisMarch.C.BridgeLemmas
open FStar.Mul
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

(* Convert c2pulse option-wrapped Int32 sequence to plain int sequence. *)
let int_val (x: Int32.t) : int = Int32.v x

let to_int_seq
  (s: Seq.seq (option Int32.t) {forall (i: nat). i < Seq.length s ==> Some? (Seq.index s i)})
  : GTot (Seq.seq int)
  = Seq.init_ghost (Seq.length s) (fun i -> int_val (Some?.v (Seq.index s i)))

(* The c2pulse forall ensures for find_leftmost implies is_leftmost on int sequences. *)
let find_leftmost_is_leftmost_bridge
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
        int_val (Some?.v (Seq.index xs_opt m)) < int_val (Some?.v (Seq.index xs_opt k)) \/
        (int_val (Some?.v (Seq.index xs_opt m)) = int_val (Some?.v (Seq.index xs_opt k)) /\
         int_val (Some?.v (Seq.index ys_opt m)) <= int_val (Some?.v (Seq.index ys_opt k)))))
    (ensures (
      let sxs = to_int_seq xs_opt in
      let sys = to_int_seq ys_opt in
      is_leftmost sxs sys m))
  = ()

(* The c2pulse cross_product_spec ensures for jm_cross, when lifted through
   to_int_seq, can be used to reason about find_next_spec decisions. *)
let cross_product_c2pulse_bridge
  (xs_opt ys_opt: Seq.seq (option Int32.t))
  (current next k: nat)
  : Lemma
    (requires
      Seq.length xs_opt == Seq.length ys_opt /\
      current < Seq.length xs_opt /\
      next < Seq.length xs_opt /\
      k < Seq.length xs_opt /\
      (forall (i: nat). i < Seq.length xs_opt ==> Some? (Seq.index xs_opt i)) /\
      (forall (i: nat). i < Seq.length ys_opt ==> Some? (Seq.index ys_opt i)))
    (ensures (
      let sxs = to_int_seq xs_opt in
      let sys = to_int_seq ys_opt in
      cross_product_spec
        (int_val (Some?.v (Seq.index xs_opt current)))
        (int_val (Some?.v (Seq.index ys_opt current)))
        (int_val (Some?.v (Seq.index xs_opt next)))
        (int_val (Some?.v (Seq.index ys_opt next)))
        (int_val (Some?.v (Seq.index xs_opt k)))
        (int_val (Some?.v (Seq.index ys_opt k)))
      ==
      cross_product_spec
        (Seq.index sxs current) (Seq.index sys current)
        (Seq.index sxs next) (Seq.index sys next)
        (Seq.index sxs k) (Seq.index sys k)))
  = ()
