(*
  ISSUE: While-loop conditions with preconditioned operations

  In new Pulse (NuWhile encoding), the while-loop condition is folded into the
  loop invariant as an existentially quantified computation. Operations with
  preconditions in the condition (SizeT arithmetic, array reads) become ill-typed
  because the preconditions can't be established in the existential slprop context.

  This file demonstrates the problem: SizeT subtraction in a while condition.
  `hi - lo` requires `SZ.v hi >= SZ.v lo` as a precondition.

  Expected error:
    Ill-typed term: SZ.sub requires precondition
    
  See ISSUE_01_fixed.fst for the working version.
*)
module ISSUE_01_lemma_call
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module SZ = FStar.SizeT
module R  = Pulse.Lib.Reference

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

(*
  FAILS: `vhi - vlo` (SizeT subtraction) in the while condition requires
  `SZ.v vhi >= SZ.v vlo`. In the NuWhile encoding, this operation is lifted
  into the invariant's existential context where the precondition can't be proved.
*)
```pulse
fn binary_search_style_FAILS
  (lo_init hi_init: SZ.t)
  requires pure (SZ.v lo_init < SZ.v hi_init /\ SZ.v hi_init <= 100)
  returns _: unit
  ensures pure True
{
  let mut lo: SZ.t = lo_init;
  let mut hi: SZ.t = hi_init;

  // FAILS: `vhi - vlo` has precondition (SZ.v vhi >= SZ.v vlo)
  while (
    let vlo = !lo;
    let vhi = !hi;
    (vhi - vlo) > 1sz
  )
  invariant exists* vlo vhi.
    R.pts_to lo vlo **
    R.pts_to hi vhi **
    pure (
      SZ.v vlo <= SZ.v vhi /\
      SZ.v vhi <= 100
    )
  {
    let vlo = !lo;
    let vhi = !hi;
    let mid = vlo + ((vhi - vlo) / 2sz);
    lo := mid
  }
}
```
