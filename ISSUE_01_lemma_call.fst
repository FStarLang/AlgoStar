(*
  ISSUE 01: Pulse generates ill-typed lambda for existential witnesses
  when function precondition references a recursive pure function on
  erased sequences.

  When calling a Pulse `fn` whose precondition mentions a recursive F*
  function applied to erased sequences (e.g. `count_ones scolor n`),
  from within a while loop with many existential variables in its
  invariant, Pulse generates a term of the form:

    FStar.SizeT.v ((fun _ _ _ _ ... __vtop_w4646 _ _ ... -> ...))

  where the existential witnesses appear as lambda parameters instead
  of being resolved to concrete values. The resulting term is ill-typed
  because `SZ.v` expects `SZ.t`, not a lambda.

  This was discovered in AutoCLRS's StackDFS DFS implementation where:
  - The dfs_visit while loop has 8 existential variables
  - Helper function `discover_vertex_dfs` has `count_gray scolor n == vtop`
    in its precondition
  - Calling discover_vertex_dfs from the while loop body produces the
    ill-typed lambda error
*)
module ISSUE_01_lemma_call
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* A recursive pure function on sequences *)
let rec count_ones_aux (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot (r: nat{r <= k}) (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) = 1 then 1 else 0) + count_ones_aux s (k - 1)

let count_ones (s: Seq.seq int) (k: nat) : nat =
  if k <= Seq.length s then count_ones_aux s k else 0

let count_ones_lemma (s:Seq.seq int)
: Lemma 
  (requires exists i. i < Seq.length s /\ Seq.index s i <> 1)
  (ensures count_ones s (Seq.length s) < (Seq.length s))
= admit()

(* A helper fn whose precondition references count_ones *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn do_push
  (color: A.array int) (d_arr: A.array int) (pred_arr: A.array int)
  (stack_arr: A.array SZ.t) (top_ref: R.ref SZ.t)
  (scan_arr: A.array SZ.t) (time_ref: R.ref int)
  (u: SZ.t) (vv: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  requires
    A.pts_to color scolor **
    A.pts_to d_arr sd **
    A.pts_to pred_arr spred **
    A.pts_to stack_arr sstack **
    A.pts_to scan_arr sscan **
    R.pts_to top_ref vtop **
    R.pts_to time_ref vtime **
    pure (
      True /\
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtop < SZ.v n /\   // <-- THIS is what we need to prove at call site
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0   /\
      count_ones scolor (SZ.v n) == SZ.v vtop /\ // <-- triggers the bug
      True
    )
  ensures exists* scolor' sd' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d_arr sd' **
    A.pts_to pred_arr spred' **
    A.pts_to stack_arr sstack' **
    A.pts_to scan_arr sscan' **
    R.pts_to top_ref vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' <= SZ.v n /\
      vtime' >= vtime
    )
{ admit();
  let t = !time_ref;
  time_ref := t + 1;
  A.op_Array_Assignment d_arr vv (t + 1);
  A.op_Array_Assignment color vv 1;
  A.op_Array_Assignment pred_arr vv (SZ.v u);
  A.op_Array_Assignment scan_arr vv 0sz;
  let top = !top_ref;
  A.op_Array_Assignment stack_arr top vv;
  top_ref := SZ.add top 1sz
}
#pop-options


(* The function that calls do_push from inside a while loop *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
fn caller
  (color: A.array int)
  (d_arr: A.array int)
  (f_arr: A.array int)
  (pred_arr: A.array int)
  (stack_arr: A.array SZ.t)
  (scan_arr: A.array SZ.t)
  (top_ref: R.ref SZ.t)
  (time_ref: R.ref int)
  (n: SZ.t)
  (#scolor0: erased (Seq.seq int))
  (#sd0: erased (Seq.seq int))
  (#sf0: erased (Seq.seq int))
  (#spred0: erased (Seq.seq int))
  (#sstack0: erased (Seq.seq SZ.t))
  (#sscan0: erased (Seq.seq SZ.t))
  (#vtop0: erased SZ.t)
  (#vtime0: erased int)
  requires
    A.pts_to color scolor0 **
    A.pts_to d_arr sd0 **
    A.pts_to f_arr sf0 **
    A.pts_to pred_arr spred0 **
    A.pts_to stack_arr sstack0 **
    A.pts_to scan_arr sscan0 **
    R.pts_to top_ref vtop0 **
    R.pts_to time_ref vtime0 **
    pure (
      SZ.v n > 0 /\
      Seq.length scolor0 == SZ.v n /\
      Seq.length sd0 == SZ.v n /\
      Seq.length sf0 == SZ.v n /\
      Seq.length spred0 == SZ.v n /\
      Seq.length sstack0 == SZ.v n /\
      Seq.length sscan0 == SZ.v n /\
      SZ.v vtop0 <= SZ.v n /\
      vtime0 >= 0 /\
      count_ones scolor0 (SZ.v n) == SZ.v vtop0
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d_arr sd' **
    A.pts_to f_arr sf' **
    A.pts_to pred_arr spred' **
    A.pts_to stack_arr sstack' **
    A.pts_to scan_arr sscan' **
    R.pts_to top_ref vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      SZ.v vtop' <= SZ.v n
    )
{
  while (
    let t = !top_ref;
    SZ.gt t 0sz
  )
  invariant exists* vtop_w vtime_w scolor_w sd_w sf_w spred_w sstack_w sscan_w.
    R.pts_to top_ref vtop_w **
    R.pts_to time_ref vtime_w **
    A.pts_to color scolor_w **
    A.pts_to d_arr sd_w **
    A.pts_to f_arr sf_w **
    A.pts_to pred_arr spred_w **
    A.pts_to stack_arr sstack_w **
    A.pts_to scan_arr sscan_w **
    pure (
      SZ.v vtop_w <= SZ.v n /\
      Seq.length scolor_w == SZ.v n /\
      Seq.length sd_w == SZ.v n /\
      Seq.length sf_w == SZ.v n /\
      Seq.length spred_w == SZ.v n /\
      Seq.length sstack_w == SZ.v n /\
      Seq.length sscan_w == SZ.v n /\
      vtime_w >= 0 /\
      count_ones scolor_w (SZ.v n) == SZ.v vtop_w
    )
  {
    let top = !top_ref;
    let u_idx: SZ.t = SZ.sub top 1sz;
    let u: SZ.t = A.op_Array_Access stack_arr u_idx;

    // Read color[0] to check if we should push
    let cv: int = A.op_Array_Access color 0sz;

    if (cv <> 1) {
      // We know color[0] != 1, count_ones scolor n == vtop, so vtop < n.
      // BUG: Calling do_push here, which requires count_ones == vtop in
      // its precondition, triggers the ill-typed lambda elaboration.
      with scolor_w. assert A.pts_to color scolor_w;
      count_ones_lemma scolor_w; //you need cal a lemma that proves this inductive property
      //the smt solver cannot prove properties directly by induction
      // Use assume_ to provide vtop < n (since we can't call the lemma)
      // assume_ (pure (SZ.v top < SZ.v n));
 
      //but you also need to prove this property, presumably an invariant of the stack_arr
      assume_ (pure (SZ.v u < SZ.v n)); 
      
      //this call now typechecks
      do_push color d_arr pred_arr stack_arr top_ref scan_arr time_ref u 0sz n;

      admit()
    } else {
      // Pop
      top_ref := SZ.sub top 1sz;
      assume_ (pure (SZ.v u < SZ.v n));
      A.op_Array_Assignment color (A.op_Array_Access stack_arr u_idx) 2;
      admit()
    }
  }
}
#pop-options
