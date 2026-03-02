(*
  FIX for ISSUE_02: Add leading `_` to `with` after while loops.

  The NuWhile encoding adds a `meas: unit` existential that shifts
  all `with ... . _;` bindings after a loop. Prefix with `_` to skip it.

  This file should verify successfully.
*)
module ISSUE_02_fixed
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module SZ = FStar.SizeT
module R  = Pulse.Lib.Reference
module A  = Pulse.Lib.Array

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

```pulse
fn with_after_loop_FIXED
  (arr: A.array int)
  (n: SZ.t)
  requires
    A.pts_to arr (Seq.create (SZ.v n) 0) **
    pure (SZ.v n > 0)
  returns _: unit
  ensures exists* s.
    A.pts_to arr s **
    pure (Seq.length s == SZ.v n)
{
  let mut i: SZ.t = 0sz;

  while (
    let vi = !i;
    vi < n
  )
  invariant exists* vi sarr.
    R.pts_to i vi **
    A.pts_to arr sarr **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sarr == SZ.v n
    )
  {
    let vi = !i;
    A.op_Array_Assignment arr vi 42;
    i := vi + 1sz
  };

  // FIX: Skip the meas existential with a leading `_`
  with _ vn sarr. _;
  assert pure (Seq.length sarr == SZ.v n)
}
```
