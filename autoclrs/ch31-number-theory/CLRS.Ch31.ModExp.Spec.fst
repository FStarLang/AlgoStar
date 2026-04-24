(*
   Modular Exponentiation — Pure Specification

   Defines pow and mod_exp_spec for modular exponentiation.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Spec


//SNIPPET_START: mod_exp_spec
let rec pow (b: int) (e: nat) : Tot int (decreases e) =
  if e = 0 then 1
  else b * pow b (e - 1)

let mod_exp_spec (b: int) (e: nat) (m: pos) : int = pow b e % m
//SNIPPET_END: mod_exp_spec
