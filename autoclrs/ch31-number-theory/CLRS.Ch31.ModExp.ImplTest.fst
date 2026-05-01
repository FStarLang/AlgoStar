(*
   CLRS Chapter 31: Modular Exponentiation (R-to-L) — Spec Validation Test

   Tests that the mod_exp_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     2^10 mod 1000 = 24

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ mod_exp_spec 2 10 1000 == 24 normalized
        ✓ SZ.v result == 24 from postcondition
     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparison returns bool checked at runtime
        ✓ Returns bool — caller can verify at runtime

   NO admits. NO assumes.
*)
module CLRS.Ch31.ModExp.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open CLRS.Ch31.ModExp.Impl
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  not (a <^ b || b <^ a)

/// Prove the expected output by normalizing the pure spec
let modexp_expected ()
  : Lemma (mod_exp_spec 2 10 100 == 24)
  = assert_norm (mod_exp_spec 2 10 100 == 24)

```pulse
(* Test: 2^10 mod 100 = 24 *)
fn test_mod_exp ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Prove m^2 fits: 100^2 = 10000 < 65536 = pow2 16
  SZ.fits_at_least_16 (100 * 100);

  // Call mod_exp_impl with SZ.t arguments
  let result = mod_exp_impl 2sz 10sz 100sz ctr;

  // Postcondition gives: mod_exp_spec 2 10 100 == SZ.v result
  // Normalize spec: mod_exp_spec 2 10 100 == pow 2 10 % 100 == 1024 % 100 == 24
  modexp_expected ();
  assert (pure (SZ.v result == 24));

  // Bounds from postcondition: 0 ≤ result < 100
  assert (pure (SZ.v result >= 0));
  assert (pure (SZ.v result < 100));

  // Runtime check (survives extraction to C)
  let pass = sz_eq result 24sz;

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  pass
}
```
