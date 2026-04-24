(*
   CLRS Chapter 31: Modular Exponentiation (L-to-R) — Spec Validation Test

   Tests that the mod_exp_lr_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     3^5 mod 7 = 5

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ mod_exp_spec 3 5 7 == 5 normalized
        ✓ SZ.v result == 5 from postcondition
     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparison returns bool checked at runtime
        ✓ Returns bool — caller can verify at runtime

   NO admits. NO assumes.
*)
module CLRS.Ch31.ModExpLR.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open CLRS.Ch31.ModExpLR.Impl
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ModExpLR.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  not (a <^ b || b <^ a)

/// Prove the expected output by normalizing the pure spec
let modexplr_expected ()
  : Lemma (mod_exp_spec 3 5 7 == 5)
  = assert_norm (mod_exp_spec 3 5 7 == 5)

/// Prove m^2 fits in SZ.t (7^2 = 49, easily fits)
let modexplr_m_fits ()
  : Lemma (SZ.fits (7 * 7))
  = SZ.fits_at_least_16 0

```pulse
(* Test: 3^5 mod 7 = 5 *)
fn test_mod_exp_lr ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Prove m^2 fits
  modexplr_m_fits ();

  // Call mod_exp_lr_impl with SZ.t arguments
  let result = mod_exp_lr_impl 3sz 5sz 7sz ctr;

  // Postcondition gives: mod_exp_spec 3 5 7 == SZ.v result
  // Normalize spec: mod_exp_spec 3 5 7 == pow 3 5 % 7 == 243 % 7 == 5
  modexplr_expected ();
  assert (pure (SZ.v result == 5));

  // Bounds from postcondition: 0 ≤ result < 7
  assert (pure (SZ.v result >= 0));
  assert (pure (SZ.v result < 7));

  // Runtime check (survives extraction to C)
  let pass = sz_eq result 5sz;

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  pass
}
```
