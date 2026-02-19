(*
  ISSUE 02: Seq.index refinement failure in Pulse ensures clauses
  under exists*.

  When a Pulse function's `ensures` clause uses `Seq.index s i` inside
  a `pure()` block where `s` is existentially quantified (from
  `exists*`), the refinement check `i < Seq.length s` fails even when
  `Seq.length s == n` and `i < n` appear as earlier conjuncts in the
  same pure block.

  Expected behavior: The refinement should be dischargeable from
  sibling conjuncts in the same pure() block.

  Actual behavior: Error pointing to FStar.Seq.Base.fsti's index
  signature, indicating the refinement can't be proven.

  Workaround: Use a wrapper function that guards the index:
    let safe_index (s: Seq.seq int) (i: nat) : int =
      if i < Seq.length s then Seq.index s i else 0

  This was discovered in AutoCLRS's StackDFS module when trying to add
  explicit update postconditions (e.g. `Seq.index scolor' (SZ.v u) == 2`)
  to the finish_vertex function.
*)
module ISSUE_02_seq_index_ensures
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.WithPure
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// (* Workaround helper *)
// let safe_index (s: Seq.seq int) (i: nat) : int =
//   if i < Seq.length s then Seq.index s i else 0

(*
  CASE 1: Using Seq.index directly in ensures — FAILS

  This function sets arr[idx] to value and tries to state in its
  postcondition that the new value at position idx equals value.
*)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
fn set_and_report_FAILS
  (arr: A.array int)
  (idx: SZ.t)
  (value: int)
  (n: SZ.t)
  (#s: erased (Seq.seq int))
  requires
    A.pts_to arr s **
    with_pure (
      SZ.v idx < SZ.v n /\
      Seq.length s == SZ.v n
    )
  ensures exists* s'.
    A.pts_to arr s' **
    pure (
      Seq.length s' == SZ.v n /\
      // BUG: This line causes "See also FStar.Seq.Base.fsti(32,40-32,52)"
      // The refinement i < Seq.length s' on Seq.index can't be proven,
      // even though Seq.length s' == SZ.v n and SZ.v idx < SZ.v n
      // are both in scope.
      Seq.index s' (SZ.v idx) == value
    )
{
  A.op_Array_Assignment arr idx value
}
#pop-options


// (*
//   CASE 2: Using safe_index wrapper — WORKS

//   Same function but with the guarded wrapper. The wrapper avoids the
//   refinement issue because it checks length internally.
// *)

// #push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
// fn set_and_report_WORKS
//   (arr: A.array int)
//   (idx: SZ.t)
//   (value: int)
//   (n: SZ.t)
//   (#s: erased (Seq.seq int))
//   requires
//     A.pts_to arr s **
//     pure (
//       SZ.v idx < SZ.v n /\
//       Seq.length s == SZ.v n
//     )
//   ensures exists* s'.
//     A.pts_to arr s' **
//     pure (
//       Seq.length s' == SZ.v n /\
//       // Using the safe wrapper avoids the refinement issue
//       safe_index s' (SZ.v idx) == value
//     )
// {
//   A.op_Array_Assignment arr idx value
// }
// #pop-options


// (*
//   CASE 3: Seq.index in ensures with quantifier — FAILS

//   Common pattern: state that all other elements are unchanged.
// *)

// #push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
// fn set_and_preserve_FAILS
//   (arr: A.array int)
//   (idx: SZ.t)
//   (value: int)
//   (n: SZ.t)
//   (#s: erased (Seq.seq int))
//   requires
//     A.pts_to arr s **
//     pure (
//       SZ.v idx < SZ.v n /\
//       Seq.length s == SZ.v n
//     )
//   ensures exists* s'.
//     A.pts_to arr s' **
//     pure (
//       Seq.length s' == SZ.v n /\
//       // BUG: This quantified postcondition also fails for the same reason.
//       // Seq.index s' j and Seq.index s j both need j < Seq.length s'/s,
//       // which should follow from j < SZ.v n and Seq.length == SZ.v n.
//       (forall (j:nat). j < SZ.v n /\ j <> SZ.v idx ==>
//         Seq.index s' j == Seq.index s j)
//     )
// {
//   A.op_Array_Assignment arr idx value
// }
// #pop-options


// (*
//   CASE 4: Same quantifier with safe_index — WORKS
// *)

// #push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
// fn set_and_preserve_WORKS
//   (arr: A.array int)
//   (idx: SZ.t)
//   (value: int)
//   (n: SZ.t)
//   (#s: erased (Seq.seq int))
//   requires
//     A.pts_to arr s **
//     pure (
//       SZ.v idx < SZ.v n /\
//       Seq.length s == SZ.v n
//     )
//   ensures exists* s'.
//     A.pts_to arr s' **
//     pure (
//       Seq.length s' == SZ.v n /\
//       // Using safe_index avoids the refinement problem
//       (forall (j:nat). j < SZ.v n /\ j <> SZ.v idx ==>
//         safe_index s' j == safe_index s j)
//     )
// {
//   A.op_Array_Assignment arr idx value
// }
// #pop-options
