(*
  ISSUE: `with` binding shift after while loops (meas existential)

  In new Pulse (NuWhile encoding), while loops add an extra `meas: unit`
  existential to the invariant upon loop exit. This means `with x y z. _;`
  bindings AFTER a while loop are off by one — the first variable gets
  bound to `meas` (unit) instead of the first invariant variable.

  FIX: Add a leading `_` wildcard: `with _ x y z. _;`

  NOTE: This only affects `with ... . _;` AFTER the loop, not inside the body.

  This file contains ONLY the failing example to demonstrate the bug.
  See ISSUE_02_fixed.fst for the working version.
*)
module ISSUE_02_seq_index_ensures
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module SZ = FStar.SizeT
module R  = Pulse.Lib.Reference
module A  = Pulse.Lib.Array

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

(*
  FAILS: After the while loop, `with vn sarr. _;` binds:
    vn   ← meas (unit)    -- WRONG, expected SZ.t
    sarr ← vn   (SZ.t)    -- WRONG, expected Seq.seq int
  This causes type errors when using vn and sarr later.
*)
```pulse
fn with_after_loop_FAILS
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

  // BUG: vn gets type `unit` (the meas), sarr gets type `SZ.t`
  with vn sarr. _;
  // Using sarr causes a type error since it's actually SZ.t not Seq.seq int
  assert pure (Seq.length sarr == SZ.v n)
}
```
