(*
  FIX for ISSUE_01: Boolean flag pattern

  When a while-loop condition requires operations with preconditions
  (SizeT subtraction, array reads, lemma calls), refactor to:

    1. Compute the condition BEFORE the loop into a mutable bool `go`
    2. Use `while (!go)` as the condition (ref read has no preconditions)
    3. Recompute the condition at the END of each iteration body
    4. Tie the flag to the actual condition in the invariant:
         (vgo ==> <when-true facts>) /\ (not vgo ==> <when-false facts>)

  This file demonstrates the fix for the SizeT subtraction in condition
  from ISSUE_01_lemma_call.fst.
*)
module ISSUE_01_fixed
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module SZ = FStar.SizeT
module R  = Pulse.Lib.Reference

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

```pulse
fn binary_search_style_FIXED
  (lo_init hi_init: SZ.t)
  requires pure (SZ.v lo_init < SZ.v hi_init /\ SZ.v hi_init <= 100)
  returns _: unit
  ensures pure True
{
  let mut lo: SZ.t = lo_init;
  let mut hi: SZ.t = hi_init;

  // Step 1: Compute the condition BEFORE the loop
  let mut go: bool = ((hi_init - lo_init) > 1sz);

  // Step 2: Use `!go` as the condition — no preconditions needed
  while (!go)
  invariant exists* vlo vhi vgo.
    R.pts_to lo vlo **
    R.pts_to hi vhi **
    R.pts_to go vgo **
    pure (
      SZ.v vlo <= SZ.v vhi /\
      SZ.v vhi <= 100 /\
      // Step 4: Tie the flag to the real condition
      (vgo == (SZ.v vhi - SZ.v vlo > 1))
    )
  {
    let vlo = !lo;
    let vhi = !hi;
    let mid = vlo + ((vhi - vlo) / 2sz);
    lo := mid;

    // Step 3: Recompute condition at the END of the body
    let new_lo = !lo;
    let new_hi = !hi;
    go := ((new_hi - new_lo) > 1sz)
  }
}
```
#pop-options
