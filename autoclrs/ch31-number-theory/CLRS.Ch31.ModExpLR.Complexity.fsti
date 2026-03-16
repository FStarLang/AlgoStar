(*
   Left-to-Right Modular Exponentiation — Complexity Interface

   The left-to-right variant processes exactly num_bits(e) iterations,
   one per bit of the exponent from MSB to LSB.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

// Complexity bound for left-to-right modular exponentiation
let modexp_lr_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= num_bits e_init
