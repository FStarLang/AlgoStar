(*
   Left-to-Right Modular Exponentiation — Complexity Interface

   Transparent definition of the complexity bound for the left-to-right
   modular exponentiation.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

let modexp_lr_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= num_bits e_init
